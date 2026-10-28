/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3compactor/Periodic__getCompactInterval.lean`. Lean-first (no Rocq
counterpart). The spec-first pilot's phase 1 (`notes/compactor-pilot-plan.md`): the spec is written,
the proof is phase 1's glue.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Periodic__getCompactInterval

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api v3compactor

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Assumptions]

theorem v3compactor.Periodic.getCompactInterval.wp_proof :
    v3compactor.Periodic.getCompactInterval.spec (GF := GF) (hG := hG) := by
  intro pc pd dq
  wp_start as Hp
  wp_auto
  -- (one `word` per declaration: two in sibling branches shared a cached proof the kernel rejected)
  have hH : sint.Z (W64 3600000000000) = 3600000000000 := by rfl
  wp_if_destruct
  · simp only [_root_.Perennial.time.Hour]
    (try wp_auto)
    iapply HΦ
    iframe
    ipureintro
    rw [hH] at *
    omega
  · (try wp_auto)
    iapply HΦ
    iframe
    ipureintro
    rw [hH] at *
    omega

end proof

end EtcdGrove
end Perennial
