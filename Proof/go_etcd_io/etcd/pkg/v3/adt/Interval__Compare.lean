/-
Proof of `Spec/go_etcd_io/etcd/pkg/v3/adt/Interval__Compare.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.adt.Interval__Compare
public import Spec.go_etcd_io.etcd.pkg.v3.adt.StringAffineComparable__Compare

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.pkg.v3.adt

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.adt.Assumptions]

theorem adt.Interval.Compare.wp_proof : adt.Interval.Compare.spec (GF := GF) (hG := hG) := by
  intro K hK p dq vb ve db de b e q dq' vb' ve' db' de' b' e'
  wp_start as ⟨Hp, Hkb, Hke, Hq, Hkb', Hke'⟩
  icases adt.ivl_split _ _ _ $$ Hp with ⟨Hpb, Hpe, %Hpn⟩
  icases adt.ivl_split _ _ _ $$ Hq with ⟨Hqb, Hqe, %Hqn⟩
  simp only [adt.KeyRep.ivl_Begin, adt.KeyRep.ivl_End]
  wp_auto
  wp_apply hK db db' vb vb' b b' $$ [Hkb Hkb'] as ⟨Hkb, Hkb'⟩
  · iframe
  wp_apply hK db de' vb ve' b e' $$ [Hkb Hke'] as ⟨Hkb, Hke'⟩
  · iframe
  wp_apply hK de db' ve vb' e b' $$ [Hke Hkb'] as ⟨Hke, Hkb'⟩
  · iframe
  have hz : ∀ a c, sint.Z (W64 (adt.affCmp a c)) = adt.affCmp a c := by
    intro a c; have := adt.affCmp_bounds a c; word
  have h0 : sint.Z (W64 0) = 0 := rfl
  have hc : ∀ r : Int, ((adt.affCmp b b' < 0 ∧ adt.affCmp e b' ≤ 0) → r = -1) →
      (¬ (adt.affCmp b b' < 0 ∧ adt.affCmp e b' ≤ 0) → adt.affCmp b e' ≥ 0 → r = 1) →
      (¬ (adt.affCmp b b' < 0 ∧ adt.affCmp e b' ≤ 0) → ¬ adt.affCmp b e' ≥ 0 → r = 0) →
      adt.ivlCmp (b, e) (b', e') = r := by
    intro r h1 h2 h3
    unfold adt.ivlCmp
    split
    · exact (h1 ‹_›).symm
    · split
      · exact (h2 ‹_› ‹_›).symm
      · exact (h3 ‹_› ‹_›).symm
  -- the three returns: `-1`, `1` and `0` (twice each for the last two)
  wp_if_destruct <;> (try wp_if_destruct) <;> (try wp_if_destruct)
  all_goals
    simp only [hz, h0] at *
    first
      | rw [← hc (-1) (by intros; omega) (by intros; omega) (by intros; omega)]
      | rw [← hc 1 (by intros; omega) (by intros; omega) (by intros; omega)]
      | rw [← hc 0 (by intros; omega) (by intros; omega) (by intros; omega)]
    iapply HΦ
    iframe Hkb Hke Hkb' Hke'
    isplitl [Hpb Hpe]
    · iapply adt.ivl_combine _ _ _ Hpn; simp only [adt.KeyRep.ivl_Begin, adt.KeyRep.ivl_End]
      iframe Hpb Hpe
    · iapply adt.ivl_combine _ _ _ Hqn; simp only [adt.KeyRep.ivl_Begin, adt.KeyRep.ivl_End]
      iframe Hqb Hqe

end proof

end EtcdGrove
end Perennial
