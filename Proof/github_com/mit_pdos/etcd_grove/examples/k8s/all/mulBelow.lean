/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/k8s/all/mulBelow.lean`: for `b > 0`, Go's
truncated division of nonnegative `bound - 1` by `b` is the floor, and `a ≤ ⌊(bound-1)/b⌋ ↔ a*b < bound`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.all.mulBelow

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_all

open Iris Iris.BI Iris.ProofMode

/-- `a ≤ (bound - 1) / b` (Go's signed division) iff `a * b < bound`, for `a ≥ 0`, `b > 0`,
`bound > 0`. -/
theorem mulBelow_div_iff (a b bound : w64) (_ha : 0 ≤ sint.Z a) (hb : 0 < sint.Z b)
    (hbd : 0 < sint.Z bound) :
    sint.Z a ≤ sint.Z (BitVec.sdiv (bound - W64 1) b) ↔ sint.Z a * sint.Z b < sint.Z bound := by
  have hsub : sint.Z (bound - W64 1) = sint.Z bound - 1 := by word
  change sint.Z a ≤ (BitVec.sdiv (bound - W64 1) b).toInt ↔ _
  rw [BitVec.toInt_sdiv_of_ne_or_ne _ _ (Or.inr (by
    intro h; have : sint.Z b = -1 := by rw [h]; rfl
    omega))]
  change sint.Z a ≤ (sint.Z (bound - W64 1)).tdiv (sint.Z b) ↔ _
  rw [hsub, Int.tdiv_eq_ediv_of_nonneg (by omega), Int.le_ediv_iff_mul_le hb]
  omega

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.all.Assumptions]

theorem mulBelow.wp_proof : mulBelow.spec (GF := GF) (hG := hG) := by
  intro a b bound ha hb hbd
  wp_start as #Hpkg
  (try wp_auto)
  wp_if_destruct
  · -- `b == 0` (`wp_if_destruct` substituted `b`)
    (try wp_auto)
    have h0 : decide (sint.Z a * sint.Z (W64 0) < sint.Z bound) = true := by
      rw [show sint.Z (W64 0) = 0 from rfl, Int.mul_zero]; exact decide_eq_true hbd
    rw [← h0]
    iapply HΦ
    itrivial
  · have hb0 : ¬ sint.Z b = 0 := by intro h; apply Hif; word
    (try wp_auto)
    rw [ite_eq_right_of_eq_false _ _ (eq_false hb0)]
    (try wp_auto)
    have hiff := mulBelow_div_iff a b bound ha (by omega) hbd
    rw [show decide (sint.Z a ≤ sint.Z (BitVec.sdiv (bound - W64 1) b)) =
      decide (sint.Z a * sint.Z b < sint.Z bound) from decide_eq_decide.2 hiff]
    iapply HΦ
    itrivial

end proof

end k8s_all
end EtcdGrove
end Perennial
