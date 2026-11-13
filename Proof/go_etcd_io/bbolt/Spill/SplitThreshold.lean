/-
`splitThreshold` (U9a, `notes/bbolt-proof-plan.md`): the WP of the trusted model
(`TrustedCode/go_etcd_io/bbolt.lean`, D17): for a fill percent that is not a NaN and a page size
below `2 ^ 53`, the threshold is in `[0, pageSize]` (otherwise the model diverges, which a WP
allows).
-/
module

public import Spec.go_etcd_io.bbolt.Data
public import Proof.go_etcd_io.bbolt.PkgInit

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt


open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

/-- The model's NaN test on a `float64`'s bits is `float64IsNaN`. -/
private theorem nan_bits (f : w64) (h1 : f &&& W64 9218868437227405312 = W64 9218868437227405312)
    (h2 : ¬ f &&& W64 4503599627370495 = W64 0) : float64IsNaN f := by
  have h1' : f &&& 0x7FF0000000000000#64 = 0x7FF0000000000000#64 := h1
  -- bit by bit (not `bv_decide`, whose proof rests on native evaluation)
  have e1 : (f >>> 52) &&& 0x7FF#64 = 0x7FF#64 := by
    have hc : ∀ i, i < 11 → (0x7FF0000000000000#64).getLsbD (52 + i) = true ∧
        (0x7FF#64).getLsbD i = true := by decide
    have hz : ∀ i, i < 64 → ¬ i < 11 → (0x7FF#64).getLsbD i = false := by decide
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have h := congrArg (fun x => x.getLsbD (52 + i)) h1'
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight] at h ⊢
    by_cases hi11 : i < 11
    · obtain ⟨ha, hb⟩ := hc i hi11
      rw [ha, Bool.and_true] at h; rw [hb, Bool.and_true, h]
    · rw [hz i hi hi11, Bool.and_false]
  have e2 := congrArg BitVec.toNat e1
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at e2
  have e3 : f.toNat % 2 ^ 52 ≠ 0 := by
    intro h; apply h2; apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (W64 4503599627370495).toNat = 2 ^ 52 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, h]; rfl
  refine ⟨?_, e3⟩
  rw [show (0x7FF#64).toNat = 2 ^ 11 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod] at e2
  exact e2

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `splitThreshold(ps, f)`: for a non-NaN `f` and `ps < 2 ^ 53`, a threshold in `[0, ps]`. -/
abbrev splitThreshold.spec : Prop :=
  ∀ (ps f : w64), ¬ float64IsNaN f → uint.Z ps < 2 ^ 53 →
  {{ (True : IProp GF) }}
    (App (App (Val #(functions splitThreshold [])) (Val #ps)) (Val #f))
  {{ (t : w64), RET #t; ⌜0 ≤ sint.Z t ∧ sint.Z t ≤ uint.Z ps⌝ }}

omit sem package_sem in
/-- The model's divergence: `(rec: f <> := f #()) #()` never returns. -/
private theorem wp_diverge (Φ : val → IProp GF) :
    ⊢ WP (glv(rec: "diverge" <> := "diverge" #()) #()) {{ Φ }} := by
  iloeb as IH
  wp_call
  iexact IH

theorem splitThreshold.wp_proof : splitThreshold.spec (GF := GF) (hG := hG) := by
  intro ps f Hnan Hps
  wp_start as _
  wp_apply wp_ArbitraryInt as %t _
  have Hps' : ¬ uint.Z (W64 (2 ^ 53)) ≤ uint.Z ps := by word
  wp_if_destruct
  · try wp_auto
    have Hfr : f &&& W64 4503599627370495 = W64 0 :=
      Classical.byContradiction fun h => Hnan (nan_bits f Hif h)
    rw [decide_eq_true Hfr]
    simp only [Bool.not_true]
    try wp_auto
    wp_if_destruct
    · exact absurd Hif Hps'
    try wp_auto
    wp_if_destruct
    · try wp_auto
      wp_if_destruct
      · iapply HΦ; ipureintro; constructor <;> word
      · iapply wp_diverge
    · try wp_auto
      iapply wp_diverge
  · try wp_auto
    wp_if_destruct
    · exact absurd Hif Hps'
    try wp_auto
    wp_if_destruct
    · try wp_auto
      wp_if_destruct
      · iapply HΦ; ipureintro; constructor <;> word
      · iapply wp_diverge
    · try wp_auto
      iapply wp_diverge

end proof

end bbolt
end EtcdGrove
end Perennial
