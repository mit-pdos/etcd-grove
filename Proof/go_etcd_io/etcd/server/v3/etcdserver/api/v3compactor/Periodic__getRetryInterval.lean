/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3compactor/Periodic__getRetryInterval.lean`. Lean-first (no Rocq
counterpart). The spec-first pilot's phase 1 (`notes/compactor-pilot-plan.md`): the spec is written,
the proof is phase 1's glue.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Periodic__getRetryInterval

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

theorem v3compactor.Periodic.getRetryInterval.wp_proof :
    v3compactor.Periodic.getRetryInterval.spec (GF := GF) (hG := hG) := by
  intro pc pd dq Hpos
  wp_start as Hp
  wp_auto
  -- (no `word` across the branches: two in sibling branches shared a cached proof the kernel
  -- rejected)
  have hH : sint.Z (W64 3600000000000) = 3600000000000 := by rfl
  wp_if_destruct
  · simp only [_root_.Perennial.time.Hour, go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.retryDivisor]
    (try wp_auto)
    iapply HΦ
    iframe
    ipureintro
    have hD : sint.Z (BitVec.sdiv (W64 3600000000000) (W64 10)) = 360000000000 := by rfl
    unfold retryOf
    rw [hH] at *
    rw [show (W64 ((10 : Int))) = W64 10 from rfl] at *
    first | (rw [hD]; omega) | omega
  · (try simp only [go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.retryDivisor])
    (try wp_auto)
    iapply HΦ
    iframe
    ipureintro
    unfold retryOf
    rw [hH] at *
    change (BitVec.sdiv pd (W64 10)).toInt = min pd.toInt 3600000000000 / 10
    rw [BitVec.toInt_sdiv_of_ne_or_ne pd (W64 10) (Or.inr (by decide)),
      show (W64 10).toInt = 10 from rfl]
    change 0 < pd.toInt at Hpos
    rw [Int.tdiv_eq_ediv_of_nonneg (by omega)]
    change ¬3600000000000 < pd.toInt at Hif
    omega

end proof

end EtcdGrove
end Perennial
