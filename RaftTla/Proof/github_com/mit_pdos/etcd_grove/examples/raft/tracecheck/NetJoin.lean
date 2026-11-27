/-
Lean-first (no Rocq counterpart). The trace check's wait-group idioms (`netJoin`, `join3`), now in
`Proof/github_com/mit_pdos/etcd_grove/examples/lib/join/NetJoin.lean` (namespace `Perennial.EtcdGrove`,
shared with the Antithesis harness, #33 S4); this module re-exports it for the trace check's files.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.join.NetJoin
