/-
The proof prelude for code that uses the durable-state extension
(`github.com/mit-pdos/etcd-grove/examples/durable`): its specs. The proofs assume
`[HasExt durableExt]`. Goose's generated proofs of a package that uses the extension import
it in place of Perennial's `ProofPrelude`.
-/
module

public import Perennial.Proof.ProofPrelude
public import DurablePrelude
public import GooseLang.Ext.Durable.Specs
