/-
**The instance's invariant at every member's KV names** (the partition plan's S3a, 2026-10-20).
Lean-first (no Rocq counterpart). The cluster's ghost state is the examples' shared `common.alloc3`
(since 2026-10-22, D33; until then this file's `cluster3_alloc`), whose members' KV names agree in
state variable and workload; `linkvInv_congr` makes the instance's invariant, allocated at the
first member's names (`linkvInv_alloc_boot`), the other members' too (D21 M4).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.common.Alloc3
public import Proof.github_com.mit_pdos.etcd_grove.examples.linkv3p.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkv3p

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section alloc
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The instance's invariant at another member's KV names**: `linkvInv γ γk` reads `γk`'s state
variable (through `etcdKV`) and workload only, which a cluster's members share (D21 M4;
`common.alloc3`'s equalities), so the invariant allocated at one member's names
(`linkvInv_alloc_boot`) is every member's. -/
theorem linkvInv_congr (γ : linkvtxn.LinkvNames) (γk γk' : KVNames) (hst : γk.st = γk'.st)
    (hwl : γk.wl = γk'.wl) :
    linkvtxn.linkvInv (GF := GF) γ γk = linkvtxn.linkvInv γ γk' := by
  unfold linkvtxn.linkvInv linkvtxn.linkvInvBody
  rw [hwl]
  simp only [etcdKV_congr γk γk' hst]

end alloc

end linkv3p
end EtcdGrove
end Perennial
