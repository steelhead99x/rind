// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use std::fs::File;
use std::io::{self, Read, Write};
use std::mem::ManuallyDrop;
use std::os::fd::{AsRawFd, FromRawFd};

use crate::ops;

/// One argument, or the whole request, may not ask for more than this.
/// ACVP's ordinary prompts are a few kilobytes; the cap rejects a length
/// that would allocate without bound.
const MAX_BYTES: usize = 1 << 20;
const MAX_ARGS: usize = 16;

pub fn serve() -> io::Result<()> {
    let mut input = io::stdin().lock();
    loop {
        let mut request = match read_request(&mut input) {
            Ok(request) => request,
            Err(err) if err.kind() == io::ErrorKind::UnexpectedEof => return Ok(()),
            Err(err) => return Err(err),
        };
        let reply = {
            let Some((command, args)) = request.split_first() else {
                return Err(io::Error::other("empty ACVP request"));
            };
            match std::str::from_utf8(command) {
                Ok(command) => ops::handle(command, args).map_err(io::Error::other),
                Err(_) => Err(io::Error::other("ACVP command is not UTF-8")),
            }
        };
        for arg in &mut request {
            ops::wipe(arg);
        }
        let reply = reply?;
        // `io::stdout()` is block-buffered on a pipe. A reply with no newline
        // stays there until exit, and the parent still holding stdin never
        // sees it. Write the fd directly. `ManuallyDrop` keeps the drop from
        // closing the process's stdout.
        // SAFETY: the fd is stdout, which outlives this process. `ManuallyDrop`
        // keeps `File`'s destructor from closing it.
        let mut output = ManuallyDrop::new(unsafe { File::from_raw_fd(io::stdout().as_raw_fd()) });
        let spans = reply.slices();
        write_reply(&mut *output, &spans)?;
    }
}

fn read_request(input: &mut impl Read) -> io::Result<Vec<Vec<u8>>> {
    let count = read_u32(input)? as usize;
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
    Ok(args)
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
    Ok(())
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
