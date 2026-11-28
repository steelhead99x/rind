//! A decapsulation key wipes its whole value on drop, encapsulation key
//! included, as AGENTS.md requires of a key type: it is only rind's
//! decapsulation key, which wipes itself, with no other copy beside it.

use core::mem::size_of;
use core::ptr;
use std::alloc::{Layout, dealloc};

use kem::KeyInit;
use rind_kem::{DecapsulationKey, MlKem512, MlKem768, MlKem1024, ParameterSet, Seed};

#[test]
fn decapsulation_keys() {
    fn check<P: ParameterSet>() {
        assert_eq!(
            size_of::<DecapsulationKey<P>>(),
            size_of::<rind::kem::DecapsulationKey<P::Rind>>()
        );
        let key = DecapsulationKey::<P>::new(&Seed::from([0x42; 64]));
        // Its encapsulation key is the one inside rind's key, not a copy.
        let inner = key.encapsulation_key() as *const _ as usize;
        let outer = &key as *const _ as usize;
        assert!(inner >= outer && inner < outer + size_of::<DecapsulationKey<P>>());
        check_zeroed_on_drop(Box::new(key));
    }
    check::<MlKem512>();
    check::<MlKem768>();
    check::<MlKem1024>();
}

/// Checks that dropping `value` zeroes every byte of it, public key included,
/// by dropping it in place and reading its memory before freeing it.
///
/// A deliberate read after drop, as `rind/tests/zeroing.rs` does: unsound in
/// principle, but deterministic, since nothing can reuse the allocation
/// before the read.
fn check_zeroed_on_drop<T>(value: Box<T>) {
    let len = size_of::<T>();
    assert_ne!(len, 0);
    let addr = Box::into_raw(value);
    let ptr = addr as *const u8;
    // SAFETY: `addr` came from a valid `Box<T>`, and is dropped only here.
    unsafe { ptr::drop_in_place(addr) };
    // SAFETY: the allocation is still live, and `len` bytes long.
    let after: Vec<u8> = (0..len)
        .map(|i| unsafe { ptr::read_volatile(ptr.add(i)) })
        .collect();
    // SAFETY: `addr` came from a `Box<T>`, so it was allocated with `T`'s layout.
    unsafe { dealloc(addr as *mut u8, Layout::new::<T>()) };
    if let Some(i) = after.iter().position(|&b| b != 0) {
        panic!("byte {i} of {len} was not cleared after drop: {after:02x?}");
    }
}
