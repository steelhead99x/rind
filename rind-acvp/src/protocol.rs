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

    #[test]
    fn framing_bounds_match_the_constants() {
        let err = read_request(&mut &0u32.to_ne_bytes()[..]).unwrap_err();
        assert_eq!(err.kind(), io::ErrorKind::Other, "{err}");
        let err = read_request(&mut &17u32.to_ne_bytes()[..]).unwrap_err();
        assert_eq!(err.kind(), io::ErrorKind::Other, "{err}");
        let mut frame = 16u32.to_ne_bytes().to_vec();
        frame.extend(std::iter::repeat_n(0u8, 16 * 4));
        let got = read_request(&mut frame.as_slice()).unwrap().unwrap();
        assert_eq!(got, vec![Vec::<u8>::new(); 16]);
        let mut huge = 1u32.to_ne_bytes().to_vec();
        huge.extend_from_slice(&((1u32 << 20) + 1).to_ne_bytes());
        let err = read_request(&mut huge.as_slice()).unwrap_err();
        assert_eq!(err.kind(), io::ErrorKind::Other, "{err}");

        let err = write_reply(&mut Vec::new(), &[]).unwrap_err();
        assert_eq!(err.kind(), io::ErrorKind::Other, "{err}");
        let too_many: Vec<&[u8]> = vec![&b"a"[..]; 17];
        let err = write_reply(&mut Vec::new(), &too_many).unwrap_err();
        assert_eq!(err.kind(), io::ErrorKind::Other, "{err}");
        let spans: Vec<&[u8]> = vec![&b"ab"[..]; 16];
        let mut out = Vec::new();
        write_reply(&mut out, &spans).unwrap();
        assert_eq!(&out[..4], &16u32.to_ne_bytes());
        assert!(out.ends_with(b"ab"));
    }

    /// A failed read is not a clean shutdown. Treating every error as EOF
    /// would drop the failure and end the session.
    #[test]
    fn read_error_is_not_a_clean_shutdown() {
        struct BrokenRead;
        impl Read for BrokenRead {
            fn read(&mut self, _buf: &mut [u8]) -> io::Result<usize> {
                Err(io::Error::other("broken"))
            }
        }
        let err = read_request(&mut BrokenRead).unwrap_err();
        assert_eq!(err.kind(), io::ErrorKind::Other, "{err}");
    }

    /// Framing and argument parsing. `ACVP_FUZZ_SECONDS` sets the budget;
    /// a normal test run skips it. A panic or a call that does not return
    /// fails the test.
    #[test]
    fn fuzz_frames_and_argument_parsing() {
        let Some(seconds) = std::env::var("ACVP_FUZZ_SECONDS")
            .ok()
            .and_then(|text| text.parse::<u64>().ok())
            .filter(|seconds| *seconds > 0)
        else {
            return;
        };
        let deadline = std::time::Instant::now() + std::time::Duration::from_secs(seconds);
        let mut rng = Rng(0xA6C7_F00D_1234_5678);
        let mut cases = 0u64;
        while std::time::Instant::now() < deadline {
            if cases.is_multiple_of(2) {
                fuzz_frame(&mut rng);
            } else {
                fuzz_handle(&mut rng);
            }
            cases += 1;
        }
        eprintln!("rind-acvp fuzz: {cases} cases in {seconds}s");
    }

    fn fuzz_frame(rng: &mut Rng) {
        let frame = match rng.below(5) {
            0 => Vec::new(),
            1 => {
                let n = rng.below(64) as usize;
                (0..n).map(|_| rng.byte()).collect()
            }
            _ => random_frame(rng),
        };
        let frame_for_panic = frame.clone();
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let mut input = frame.as_slice();
            let _ = read_request(&mut input);
        }));
        if result.is_err() {
            panic!("read_request panicked on {} bytes", frame_for_panic.len());
        }
    }

    fn random_frame(rng: &mut Rng) -> Vec<u8> {
        let count = match rng.below(6) {
            0 => 0,
            1 => 17 + rng.below(8),
            2 => u32::MAX,
            _ => 1 + rng.below(16),
        };
        let mut frame = count.to_ne_bytes().to_vec();
        let args = count.min(8);
        let mut total = 0usize;
        for i in 0..args {
            let len = match rng.below(8) {
                0 => 0,
                1 => 1 << 20,
                2 => u32::MAX,
                3 if i == 0 => 4,
                _ => rng.below(48),
            };
            total = total.saturating_add(len as usize);
            if total > (1 << 20) + 64 {
                frame.extend_from_slice(&len.to_ne_bytes());
                break;
            }
            frame.extend_from_slice(&len.to_ne_bytes());
            let take = (len as usize).min(64);
            for _ in 0..take {
                frame.push(rng.byte());
            }
        }
        if rng.below(4) == 0 {
            frame.truncate(rng.below(frame.len().max(1) as u32) as usize);
        }
        frame
    }

    fn fuzz_handle(rng: &mut Rng) {
        let commands = [
            "getConfig",
            "SHA-1",
            "SHA2-256",
            "SHA2-256/MCT",
            "SHA2-256/LDT",
            "SHA3-512",
            "HMAC-SHA-1",
            "HMAC-SHA2-512",
            "AES/encrypt",
            "AES/decrypt",
            "AES-CBC/encrypt",
            "AES-CBC/decrypt",
            "AES-CTR/encrypt",
            "AES-CTR/decrypt",
            "AES-GCM/seal",
            "AES-GCM/open",
            "AES-KW/seal",
            "AES-KW/open",
            "AES-KWP/seal",
            "AES-KWP/open",
            "PBKDF",
            "ECDSA/keyGen",
            "ECDSA/keyVer",
            "ECDSA/sigGen",
            "ECDSA/sigVer",
            "ECDSA/sigGen/componentTest",
            "EDDSA/ED-25519/keyGen",
            "EDDSA/ED-25519/keyVer",
            "EDDSA/ED-25519/sigGen",
            "EDDSA/ED-25519/sigVer",
            "ML-KEM/ML-KEM-768/keyGen",
            "ML-KEM/ML-KEM-768/encap",
            "ML-KEM/ML-KEM-768/decap",
            "ML-DSA/ML-DSA-44/keyGen",
            "ML-DSA/ML-DSA-65/sigGen",
            "ML-DSA/ML-DSA-87/sigVer",
            "RSA/signaturePrimitive",
            "RSA/decryptionPrimitive",
            "RSA/decryptionPrimitive/crt",
            "KDA/HKDF/SHA-1",
            "KDA/HKDF/SHA2-256",
            "HKDF/SHA2-256/extract",
            "HKDF/SHA2-512/expand",
            "HKDF/SHA2-256/nope",
            "ECDH/P-256",
            "ECDH/P-521",
            "ECDH/P-224",
            "hmacDRBG/SHA-1",
            "hmacDRBG/SHA2-256",
            "hmacDRBG-pr/SHA2-384",
            "hmacDRBG-reseed/SHA2-512",
            "hmacDRBG",
            "",
            "not-a-command",
        ];
        let command = if rng.below(6) == 0 {
            let n = rng.below(24) as usize;
            (0..n).map(|_| rng.byte() as char).collect::<String>()
        } else {
            commands[rng.below(commands.len() as u32) as usize].to_string()
        };
        let nargs = match rng.below(5) {
            0 => 0,
            1 => 17,
            _ => rng.below(10) as usize,
        };
        let mut args = Vec::with_capacity(nargs);
        for index in 0..nargs {
            args.push(fuzz_arg(rng, &command, index));
        }
        if command.ends_with("/LDT") && args.len() >= 2 {
            // Huge accepted repetitions are real work, not a parser hang.
            // Over the 8 GiB cap must still return.
            let times = if rng.below(2) == 0 {
                1 + u64::from(rng.below(8))
            } else {
                u64::MAX
            };
            args[1] = times.to_ne_bytes().to_vec();
            if args[0].len() > 32 {
                args[0].truncate(32);
            }
        }
        let command_for_panic = command.clone();
        let (tx, rx) = std::sync::mpsc::channel();
        std::thread::spawn(move || {
            let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                let _ = crate::ops::Wrapper::default().handle(&command, &args);
            }));
            let _ = tx.send(result);
        });
        match rx.recv_timeout(std::time::Duration::from_secs(5)) {
            Ok(Ok(())) => {}
            Ok(Err(_)) => panic!("handle panicked on {command_for_panic:?}"),
            Err(_) => panic!("handle did not return within 5s on {command_for_panic:?}"),
        }
    }

    fn fuzz_arg(rng: &mut Rng, command: &str, index: usize) -> Vec<u8> {
        let len = match rng.below(10) {
            0 => 0,
            1 => 1,
            2 => 4,
            3 => 8,
            4 => 16,
            5 => 32,
            6 => 48,
            7 => 66,
            8 => rng.below(256) as usize,
            _ => rng.below(24) as usize,
        };
        if command == "PBKDF" && index == 2 {
            let iterations = [0u32, 1, 10_000, 10_001, u32::MAX][rng.below(5) as usize];
            return iterations.to_ne_bytes().to_vec();
        }
        if (command.starts_with("AES/")
            || command.starts_with("AES-CBC/")
            || command.starts_with("AES-CTR/"))
            && (index == 2 && command.starts_with("AES/") || index == 3)
        {
            let iterations = [0u32, 1, 2, 1000, 1001, u32::MAX][rng.below(6) as usize];
            return iterations.to_ne_bytes().to_vec();
        }
        if command.starts_with("hmacDRBG") && index == 0 {
            let out = [0u32, 1, 128, 65536, 65537][rng.below(5) as usize];
            return out.to_ne_bytes().to_vec();
        }
        (0..len).map(|_| rng.byte()).collect()
    }

    struct Rng(u64);

    impl Rng {
        fn below(&mut self, bound: u32) -> u32 {
            self.0 = self.0.wrapping_mul(0xD134_2543_DE82_EF95).wrapping_add(1);
            if bound == 0 {
                return 0;
            }
            (self.0 >> 33) as u32 % bound
        }

        fn byte(&mut self) -> u8 {
            self.below(256) as u8
        }
    }
}
