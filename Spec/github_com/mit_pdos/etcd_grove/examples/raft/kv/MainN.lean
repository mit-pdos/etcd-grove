/- Lean-first (no Rocq counterpart).

## `MainN(k)` (check.go), the top-level driver on `k` replicas (2026-11-15, kvraftN)

For `k` outside `[1, 1000]` it returns at once (2026-11-24, the range check: until then the spec
took `1 ≤ k < 2^62` and the top-level statement `1 ≤ k ≤ 1000`). Otherwise the voters `1 … k` (a
loop of `append`s), `StartCluster(voters)`, then `Check(kvs, lintest.CounterClock(), 4, 25)`, the
randomized linearizability test, then a panic unless porcupine answers `Ok`. It returns: it never
panics, so porcupine's check of the recorded trace always passes. Raft's cluster has fewer than
`2^62` voters (`cluster_alloc`), every id neither `0` nor one of raft's two reserved ids
(`ConfigValid`). Everything else is allocated in the proof, as for
`Main` (`Main.lean`: the storage registry, raft's ghost state, the store's invariant, the clock), from
package initialization and `context`'s `isClosedchanInit`, for executions of fewer than `2^61` steps
(`receiptBound GF ≤ 2^61`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.kv.Defs
public import Proof.github_com.anishathalye.porcupine.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kv

open Iris Iris.BI go_etcd_io.raft.v3
open github_com.anishathalye.porcupine

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kv.Assumptions]

/-- See the file header. -/
abbrev MainN.spec : Prop :=
  ∀ (k : w64),
  -- (2026-11-02, durability stage II (l), at the landing: raft's `RestartNode` takes `readyFits`;
  -- until then `2^63`)
  receiptBound GF ≤ 2 ^ 61 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kv ∗ context.isClosedchanInit }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kv.MainN)) (Val #k))
  {{ RET #(); True }}

end spec

end raft_kv
end EtcdGrove
end Perennial
