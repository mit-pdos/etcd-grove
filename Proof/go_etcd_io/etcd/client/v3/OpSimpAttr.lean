/-
The `op_simps` simp set: the option models of `InvOp.lean` (`opFold`, the `Op*Model`s, their
`*Init`s, `OpFull.newOp`, `OpModel.zero`, the `with*M` transformers) and the cache's `txnOpOf`
(`cache/v3/InvEtcdTxn.lean`), tagged where they are defined. A proof about an option model's fields
is `simp [op_simps, ...]` with only its own definitions listed (`notes/dedup-plan.md`, C5). It must
be declared in a module of its own, apart from its uses. Lean-first (no Rocq counterpart).
-/
module

public import Lean

@[expose] public section

/-- The client's option models and transformers, unfolded. -/
register_simp_attr op_simps
