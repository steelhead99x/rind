#[cfg(target_arch = "xtensa")]
fn main() {}

#[cfg(not(target_arch = "xtensa"))]
mod common;

#[cfg(not(target_arch = "xtensa"))]
use common::Dit;

#[cfg(not(target_arch = "xtensa"))]
const PASSWORD: &[u8] = b"password";
#[cfg(not(target_arch = "xtensa"))]
const SALT: &[u8] = b"per-user salt";

/// One cost's rows: `$memory_kib` KiB over `$passes` passes and `$lanes`
/// lanes. Filling memory is nearly all the cost.
macro_rules! rows {
    ($memory_kib:expr, $passes:expr, $lanes:expr) => {
        fn rustcrypto_setup() -> (argon2::Argon2<'static>, [u8; 32]) {
            let params = argon2::Params::new($memory_kib, $passes, $lanes, Some(32)).unwrap();
            let ctx =
                argon2::Argon2::new(argon2::Algorithm::Argon2id, argon2::Version::V0x13, params);
            (ctx, [0; 32])
        }

        #[bench(setup = rustcrypto_setup)]
        fn rustcrypto((ctx, out): &mut (argon2::Argon2<'static>, [u8; 32])) {
            ctx.hash_password_into(PASSWORD, SALT, out).unwrap();
        }

        #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
        fn openssl_setup() -> [u8; 32] {
            [0; 32]
        }

        #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
        #[bench(setup = openssl_setup)]
        fn openssl(out: &mut [u8; 32]) {
            openssl::kdf::argon2id(
                None,
                PASSWORD,
                SALT,
                None,
                None,
                $passes,
                $lanes,
                $memory_kib,
                out,
            )
            .unwrap();
        }

        fn rind_setup() -> Dit<(rind::argon2::Params, rind::argon2::Secret, [u8; 32])> {
            let params = rind::argon2::Params::new($memory_kib, $passes, $lanes).unwrap();
            Dit::hold((params, rind::argon2::Secret::new(PASSWORD), [0; 32]))
        }

        #[bench(setup = rind_setup)]
        fn rind(input: &mut Dit<(rind::argon2::Params, rind::argon2::Secret, [u8; 32])>) {
            let (params, secret, out) = &mut **input;
            secret.derive(*params, SALT, out).unwrap();
        }
    };
}

// RFC 9106's second recommendation, the one cheap enough to sample, and one
// lane of 16 MiB in one pass.
#[allow(non_snake_case)]
#[cfg(not(target_arch = "xtensa"))]
mod argon2id_16MiB_t1_p1 {
    use swole::bench;

    use super::*;

    rows!(1 << 14, 1, 1);
}

#[allow(non_snake_case)]
#[cfg(not(target_arch = "xtensa"))]
mod argon2id_64MiB_t3_p4 {
    use swole::bench;

    use super::*;

    rows!(1 << 16, 3, 4);
}

#[cfg(not(target_arch = "xtensa"))]
fn main() {
    swole::main();
}
