/-
**The instance's invariant at every member's KV names** (the partition plan's S3a, 2026-10-20).
Lean-first (no Rocq counterpart). The cluster's ghost state is the examples' shared `etcdstart.alloc3`
(since 2026-10-22, D33; until then this file's `cluster3_alloc`; allocated by `cluster3.StartCluster`
since 2026-11-05, when this file's lemmas on the directory moved to `cluster3/Dir.lean`), whose
members' KV names agree in state variable; `linkvInv_congr` makes the instance's invariant, allocated at the
first member's names (`linkvInv_alloc_boot`), the other members' too (D21 M4).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.partition.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_partition

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section alloc
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The instance's invariant at another member's KV names**: `linkvInv γ γk` reads `γk`'s state
variable (through `etcdKV`) only, which a cluster's members share (D21 M4;
`etcdstart.alloc3`'s equalities), so the invariant allocated at one member's names
(`linkvInv_alloc_boot`) is every member's. -/
theorem linkvInv_congr (γ : etcd_txnlin.LinkvNames) (γk γk' : KVNames) (hst : γk.st = γk'.st) :
    etcd_txnlin.linkvInv (GF := GF) γ γk = etcd_txnlin.linkvInv γ γk' := by
  unfold etcd_txnlin.linkvInv etcd_txnlin.linkvInvBody
  simp only [etcdKV_congr γk γk' hst]

end alloc

end etcd_partition
end EtcdGrove
end Perennial
