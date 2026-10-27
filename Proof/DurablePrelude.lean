/-
The proof prelude for proofs about code that uses the durable-state extension
(`github.com/mit-pdos/etcd-grove/examples/durable`): its definition and specs. The proofs
assume `[HasExt durableExt]`.
-/
module

public import Perennial.Proof.ProofPrelude
public import GooseLang.Ext.Durable.Impl
public import GooseLang.Ext.Durable.Specs
