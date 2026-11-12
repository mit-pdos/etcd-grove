/-
The proof prelude for proofs about code that uses the Linux file extension (`Fs.fsExt`, the
extension named `os`): its definition, ghost state and specs. The proofs assume
`[HasExt Fs.fsExt]`.
-/
module

public import Perennial.Proof.ProofPrelude
public import GooseLang.Ext.Fs.Impl
public import GooseLang.Ext.Fs.Specs
public import GooseLang.Ext.Fs.Truncate
public import GooseLang.Ext.Fs.TreeSpecsOpen
public import GooseLang.Ext.Fs.TreeSpecsMeta
public import GooseLang.Ext.Fs.TreeSpecsDirFd
