/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3compactor/Periodic__getRetentions.lean`. Lean-first (no Rocq
counterpart). The spec-first pilot's phase 1 (`notes/compactor-pilot-plan.md`): the spec is written,
the proof is phase 1's glue.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Periodic__getRetentions
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

theorem v3compactor.Periodic.getRetentions.wp_proof
    (hPeriodic_getRetryInterval : v3compactor.Periodic.getRetryInterval.spec (GF := GF) (hG := hG)) :
    v3compactor.Periodic.getRetentions.spec (GF := GF) (hG := hG) := by
  intro pc pd dq H10
  wp_start as Hp
  (try wp_auto)
  wp_apply (hPeriodic_getRetryInterval pc pd dq (by omega)) $$ [$Hp] as %d ⟨%Hd, Hp⟩
  (try wp_auto)
  rw [if_neg (by rw [Hd]; unfold retryOf; omega)]
  (try wp_auto)
  iapply HΦ
  iframe
  ipureintro
  have hb := retentions_bound (sint.Z pd) H10 (by word)
  have hdiv : sint.Z (BitVec.sdiv pd d) = sint.Z pd / retryOf (sint.Z pd) := by
    have hd1 : 1 ≤ sint.Z d := by rw [Hd]; unfold retryOf; omega
    change (BitVec.sdiv pd d).toInt = pd.toInt / retryOf pd.toInt
    rw [BitVec.toInt_sdiv_of_ne_or_ne pd d (Or.inr (by intro h; subst h; exact absurd hd1 (by decide)))]
    rw [Int.tdiv_eq_ediv_of_nonneg (by change 10 ≤ pd.toInt at H10; omega)]
    rw [show d.toInt = sint.Z d from rfl, Hd]
  unfold retentionsOf
  rw [← hdiv] at hb ⊢
  word

end proof

end EtcdGrove
end Perennial
