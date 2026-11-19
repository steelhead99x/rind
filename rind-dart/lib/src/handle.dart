// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// The base of every native object. No public library exports this one, so
// a key's pointer is out of reach of the package's API.
library;

import 'dart:ffi';

/// A native object, freed by the finalizer it attaches.
abstract base class Handle implements Finalizable {
  /// Takes the native object at the pointer, which [finalizer] frees.
  Handle(this._pointer, NativeFinalizer finalizer) {
    finalizer.attach(this, _pointer, detach: this);
  }

  final Pointer<Void> _pointer;
}

/// The native pointer behind a [Handle], for this package's own calls.
extension HandlePointer on Handle {
  /// The pointer the handle's finalizer frees.
  Pointer<Void> get pointer => _pointer;
}
