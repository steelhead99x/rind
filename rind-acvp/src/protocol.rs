// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use std::io::{self, Read, Write};

use crate::ops;

/// One argument, or the whole request, may not ask for more than this.
/// ACVP's ordinary prompts are a few kilobytes; the cap rejects a length
/// that would allocate without bound.
const MAX_BYTES: usize = 1 << 20;
const MAX_ARGS: usize = 16;

pub fn serve() -> io::Result<()> {
    let mut input = io::stdin().lock();
    let mut output = io::stdout().lock();
    let mut wrapper = ops::Wrapper::default();
    loop {
        let Some(request) = read_request(&mut input)? else {
            return Ok(());
        };
        let reply = {
            let Some((command, args)) = request.split_first() else {
                return Err(io::Error::other("empty ACVP request"));
            };
            match std::str::from_utf8(command) {
                Ok(command) => wrapper.handle(command, args).map_err(io::Error::other),
                Err(_) => Err(io::Error::other("ACVP command is not UTF-8")),
            }
        };
        let reply = reply?;
        let spans = reply.slices();
        write_reply(&mut output, &spans)?;
    }
}

fn read_request(input: &mut impl Read) -> io::Result<Option<Vec<Vec<u8>>>> {
    let mut count = [0u8; 4];
    // EOF between requests is clean shutdown. Once one byte arrives, the
    // whole frame must arrive, including its header and every argument.
    match input.read_exact(&mut count[..1]) {
        Ok(()) => {}
        Err(err) if err.kind() == io::ErrorKind::UnexpectedEof => return Ok(None),
        Err(err) => return Err(err),
    }
    input.read_exact(&mut count[1..])?;
    let count = u32::from_ne_bytes(count) as usize;
    if count == 0 || count > MAX_ARGS {
        return Err(io::Error::other("ACVP request argument count"));
    }
    let mut lengths = Vec::with_capacity(count);
    let mut total = 0usize;
    for _ in 0..count {
        let len = read_u32(input)? as usize;
        total = total
            .checked_add(len)
            .filter(|total| *total <= MAX_BYTES)
            .ok_or_else(|| io::Error::other("ACVP request is too large"))?;
        lengths.push(len);
    }
    let mut args = Vec::with_capacity(count);
    for len in lengths {
        let mut buf = vec![0u8; len];
        input.read_exact(&mut buf)?;
        args.push(buf);
    }
    Ok(Some(args))
}

fn write_reply(output: &mut impl Write, spans: &[&[u8]]) -> io::Result<()> {
    if spans.is_empty() || spans.len() > MAX_ARGS {
        return Err(io::Error::other("ACVP reply argument count"));
    }
    let mut header = Vec::with_capacity(4 * (1 + spans.len()));
    header.extend_from_slice(&(spans.len() as u32).to_ne_bytes());
    for span in spans {
        header.extend_from_slice(&(span.len() as u32).to_ne_bytes());
    }
    output.write_all(&header)?;
    for span in spans {
        output.write_all(span)?;
    }
    // The client waits for this reply with stdin still open. Flush even
    // when a pipe buffers the bytes and the reply contains no newline.
    output.flush()
}

fn read_u32(input: &mut impl Read) -> io::Result<u32> {
    let mut buf = [0u8; 4];
    input.read_exact(&mut buf)?;
    Ok(u32::from_ne_bytes(buf))
}

pub(crate) fn u32_arg(bytes: &[u8]) -> Option<u32> {
    let bytes: [u8; 4] = bytes.try_into().ok()?;
    Some(u32::from_ne_bytes(bytes))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn eof_is_clean_only_between_requests() {
        let mut frame = Vec::new();
        for n in [2u32, 8, 3] {
            frame.extend_from_slice(&n.to_ne_bytes());
        }
        frame.extend_from_slice(b"SHA2-256abc");
        for end in 1..frame.len() {
            let err = read_request(&mut &frame[..end]).unwrap_err();
            assert_eq!(err.kind(), io::ErrorKind::UnexpectedEof, "{end}");
        }
        assert!(read_request(&mut &[][..]).unwrap().is_none());
        let mut input = frame.as_slice();
        assert_eq!(
            read_request(&mut input).unwrap(),
            Some(vec![b"SHA2-256".to_vec(), b"abc".to_vec()])
        );
        assert!(read_request(&mut input).unwrap().is_none());
    }
}
