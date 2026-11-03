/-
The proof prelude for proofs about code that uses the Linux file extension (`osFsExt`, the
extension named `os`): its definition, ghost state and specs. The proofs assume
`[HasExt osFsExt]`.
-/
module

public import Perennial.Proof.ProofPrelude
public import GooseLang.Ext.OsFs.Impl
public import GooseLang.Ext.OsFs.Specs
