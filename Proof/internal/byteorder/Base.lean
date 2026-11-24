/-
The package initialization instance of the standard library's `internal/byteorder`: Perennial's
(claim #34 stage 2, 2026-11-25: Perennial translates the package, which its `crypto/sha1` imports; until
then the k8s-apiserver project's translation, with this module's own instance). Kept as a module so
that this repository's specs of `BEPutUint32`, `BEPutUint64` and `LEUint32` keep their import.
-/
module

public import Perennial.Proof.internal.byteorder.Base

@[expose] public section
