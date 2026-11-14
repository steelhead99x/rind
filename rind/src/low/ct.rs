// Written for Graviola by Joe Birr-Pixton, 2025.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

cfg_if::cfg_if! {
    if #[cfg(feature = "__ctgrind")] {
        use crabgrind::{memcheck, valgrind};
        use core::mem::size_of_val;

        #[inline]
        pub(crate) fn secret_slice<T>(v: &[T]) {
            if let valgrind::RunningMode::Valgrind = valgrind::running_mode() {
                memcheck::mark_memory(
                    v.as_ptr().cast(),
                    size_of_val(v),
                    memcheck::MemState::Undefined,
                )
                .unwrap();
            }
        }

        #[inline]
        pub(crate) fn public_slice<T>(v: &[T]) {
            if let valgrind::RunningMode::Valgrind = valgrind::running_mode() {
                memcheck::mark_memory(
                    v.as_ptr().cast(),
                    size_of_val(v),
                    memcheck::MemState::Defined,
                )
                .unwrap();
            }
        }

        /// `bytes`, after [`public_slice`].
        ///
        /// The client request takes the address as an integer, so LLVM does
        /// not treat it as a write. Inlined into a caller, a function that
        /// marks its argument and returns it hands back the unmarked original,
        /// and a later compare branches on whatever still taints that original.
        /// This stays a call, and the copy below is loaded after the request.
        #[inline(never)]
        pub(crate) fn defined_bytes<const N: usize>(bytes: [u8; N]) -> [u8; N] {
            public_slice(&bytes);
            bytes
        }

        #[inline]
        #[must_use]
        pub(crate) fn into_secret<T>(v: T) -> T {
            if let valgrind::RunningMode::Valgrind = valgrind::running_mode() {
                memcheck::mark_memory(
                    (&v as *const T).cast(),
                    size_of_val(&v),
                    memcheck::MemState::Undefined,
                )
                .unwrap();
            }
            v
        }

        #[inline]
        #[must_use]
        pub(crate) fn into_public<T>(v: T) -> T {
            if let valgrind::RunningMode::Valgrind = valgrind::running_mode() {
                memcheck::mark_memory(
                    (&v as *const T).cast(),
                    size_of_val(&v),
                    memcheck::MemState::Defined,
                )
                .unwrap();
            }
            v
        }
    } else if #[cfg(test)] {
        // `admin/ct-binsec` replaces these markers with fresh secret or
        // public values, so BINSEC checks the policy valgrind does.
        use super::ct_binsec::{classify, declassify};
        use core::mem::size_of_val;

        #[inline]
        pub(crate) fn secret_slice<T>(v: &[T]) {
            classify(v.as_ptr().cast_mut().cast(), size_of_val(v));
        }

        #[inline]
        pub(crate) fn public_slice<T>(v: &[T]) {
            declassify(v.as_ptr().cast_mut().cast(), size_of_val(v));
        }

        #[inline]
        #[must_use]
        pub(crate) fn into_secret<T>(mut v: T) -> T {
            classify((&raw mut v).cast(), size_of_val(&v));
            v
        }

        #[inline]
        #[must_use]
        pub(crate) fn into_public<T>(mut v: T) -> T {
            declassify((&raw mut v).cast(), size_of_val(&v));
            v
        }
    } else {
        #[inline]
        pub(crate) fn secret_slice<T>(_v: &[T]) {}

        #[inline]
        pub(crate) fn public_slice<T>(_v: &[T]) {}

        #[inline]
        #[must_use]
        pub(crate) fn into_secret<T>(v: T) -> T { v }

        #[inline]
        #[must_use]
        pub(crate) fn into_public<T>(v: T) -> T { v }
    }
}
