/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3compactor/Periodic__getCompactInterval.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Periodic__getCompactInterval

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Assumptions]

theorem v3compactor.Periodic.getCompactInterval.wp_proof :
    v3compactor.Periodic.getCompactInterval.spec (GF := GF) (hG := hG) := by
  intro pc p i dq dq'
  unfold pdCompactInterval pdCapped
  by_cases hi : i = W64 0 <;> by_cases hc : sint.Z hourNs < sint.Z p <;> simp only [hi, hc, ↓reduceIte]
  all_goals
    haveI : go.NotInterface go.int64 := ⟨by unfold go.int64; trivial⟩
    wp_start as ⟨Hp, Hi⟩
    wp_auto
    wp_if_destruct
    all_goals
      try wp_auto
      try wp_if_destruct
      all_goals
        try simp only [_root_.Perennial.time.Hour, go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.retryDivisor]
        try wp_auto
        first
          | (exfalso; simp only [hourNs] at *; word)
          | (iapply HΦ; iframe)

/-- **The compatibility of etcd#18472's `getCompactInterval` with the old one**: at `interval =
0` (what every caller passed before etcd#18472, and what `--auto-compaction-interval` defaults
to), it returns what it returned before, `min(period, time.Hour)`. -/
theorem v3compactor.Periodic.getCompactInterval.spec_implies_old
    (h : v3compactor.Periodic.getCompactInterval.spec (GF := GF) (hG := hG)) :
    ∀ (pc : Loc) (p : w64) (dq dq' : DFrac),
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor ∗
        pdPeriodAddr pc ↦{dq} p ∗ pdIntervalAddr pc ↦{dq'} (W64 0) }}
      (App (Val (pc @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.Periodic.ty @!! go!"getCompactInterval")) (Val #()))
    {{ RET #(pdCompactIntervalOld p); pdPeriodAddr pc ↦{dq} p ∗ pdIntervalAddr pc ↦{dq'} (W64 0) }} := by
  intro pc p dq dq'
  rw [← pdCompactInterval_zero]
  exact h pc p (W64 0) dq dq'

end proof

end EtcdGrove
end Perennial
