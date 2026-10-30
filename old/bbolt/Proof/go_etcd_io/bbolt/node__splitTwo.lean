module
public import Spec.go_etcd_io.bbolt.node__splitTwo
public import Spec.go_etcd_io.bbolt.node__sizeLessThan
public import Spec.go_etcd_io.bbolt.node__splitIndex
public import Spec.go_etcd_io.bbolt.TxStats__IncSplit
public import Proof.go_etcd_io.bbolt.FloatConv

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]
variable [float_sem : go.FloatConvSemantics]

theorem split_sint_nat (x : w64) (h : 0 ≤ sint.Z x) : ((sint.nat x : Nat) : Int) = sint.Z x := by
  word

theorem split_sint_zero : sint.Z (W64 0) = 0 := by word

theorem split_sint_nat_k (k : Nat) (h : sint.Z (W64 (k : Int)) = k) : sint.nat (W64 (k : Int)) = k := by
  word

theorem node.splitTwo.wp_proof (hSLT : node.sizeLessThan.spec (GF := GF) (hG := hG))
    (hSI : node.splitIndex.spec (GF := GF) (hG := hG))
    (hInc : TxStats.IncSplit.spec (GF := GF) (hG := hG)) :
    node.splitTwo.spec (GF := GF) (hG := hG) := by
  intro nl nv ins bv dqb st pv pcs ps
  wp_start as ⟨Hn, Hins, Hcap, Hb, Hst, Hpar⟩
  ihave %Hl := ownSlice_len _ _ _ $$ Hins
  try wp_auto
  by_cases h4 : sint.Z nv.inodes'.len ≤ sint.Z (W64 4)
  · rw [decide_eq_true h4]
    try wp_auto
    iapply HΦ
    iframe
    ileft
    iframe
    ipureintro; rfl
  rw [decide_eq_false h4]
  try wp_auto
  wp_apply hSLT nl nv (DFrac.own 1) ins (DFrac.own 1) ps $$ [Hn Hins] as ⟨Hn, Hins⟩
  · iframe
  by_cases hs : sizeLessThanFrom (W64 16) ps (W64 16) ins = true
  · rw [hs]
    try wp_auto
    iapply HΦ
    iframe
    ileft
    iframe
    ipureintro; rfl
  rw [Bool.not_eq_true] at hs
  rw [hs]
  try wp_auto
  wp_join iprop(∃ (f : w64), fillPercent_ptr ↦ f) at next with [fillPercent] as ⟨%f, fillPercent⟩
  · try wp_auto
    generalize (float64Leb bv.FillPercent' (W64 4591870180066957722) &&
      !decide (bv.FillPercent' = W64 4591870180066957722)) = b1
    cases b1
    · try wp_auto
      generalize (float64Leb (W64 4607182418800017408) bv.FillPercent' &&
        !decide (bv.FillPercent' = W64 4607182418800017408)) = b2
      cases b2
      · try wp_auto
        isplitl []
        · ipureintro; rfl
        iexists _; iexact fillPercent
      · try wp_auto
        isplitl []
        · ipureintro; rfl
        iexists _; iexact fillPercent
    · try wp_auto
      isplitl []
      · ipureintro; rfl
      iexists _; iexact fillPercent
  try wp_auto
  wp_apply hSI nl nv (DFrac.own 1) ins (DFrac.own 1) _ $$ [Hn Hins] as ⟨Hn, Hins⟩
  · iframe
  obtain ⟨k, hk, hk2, hk3⟩ := splitIndexOf_range (go.float64ToInt64 (float64Mul (go.float64OfUint64 ps) f))
    ins (by have := Hl.1; word) (by have := Hl.1; word)
  rw [hk]
  try wp_auto
  wp_join iprop(n_ptr ↦ nl ∗ ∃ (pl : Loc) (pv0 : node) (pcs0 : List Loc),
      nl ↦ ({ nv with parent' := pl } : node) ∗ pl ↦ pv0 ∗ pv0.children' ↦* pcs0 ∗
      ownSliceCap Loc pv0.children' (DFrac.own 1) ∗
      ⌜pl ≠ null ∧ ((nv.parent' = null ∧ pv0 = newParent nv pv0.children' ∧ pcs0 = [nl]) ∨
        (nv.parent' ≠ null ∧ pl = nv.parent' ∧ pv0 = pv ∧ pcs0 = pcs))⌝)
    at next with [n Hn Hpar] as ⟨n, %pl, %pv0, %pcs0, Hn, Hpl, Hpcs, Hpcap, %Hpl0⟩
  · by_cases hp : nv.parent' = null
    · rw [decide_eq_true hp]
      try wp_auto
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl ⟨Hsl, Hslcap⟩
      try wp_auto
      icases typedPointsto_not_null_dup _ _ _ $$ «$r0» with ⟨Hr0, %Hnn⟩
      isplitl []
      · ipureintro; rfl
      iframe
      ipureintro
      exact ⟨Hnn, Or.inl ⟨hp, rfl, rfl⟩⟩
    · rw [decide_eq_false hp]
      try wp_auto
      isimp only [parentOwn, hp, ↓reduceIte] at Hpar
      icases Hpar with ⟨Hp, Hpc, Hpcap⟩
      isplitl []
      · ipureintro; rfl
      iframe
      ipureintro
      exact ⟨hp, Or.inr ⟨hp, rfl, rfl, rfl⟩⟩
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl2 ⟨Hsl2, -⟩
  wp_apply wp_slice_append $$ [$Hpcs $Hpcap $Hsl2] as %s' ⟨Hpcs, Hpcap, -⟩
  try wp_auto
  ihave %Hcw := ownSliceCap_wf _ _ $$ Hcap
  have hkz : sint.Z (W64 (k : Int)) = k := by have := Hl.1; word
  have hln := split_sint_nat _ Hl.2
  have hz0 := split_sint_zero
  rw [if_pos (by have := Hl.1; omega)]
  try wp_auto
  rw [if_pos (by have := Hl.1; omega)]
  try wp_auto
  wp_apply hInc $$ [Hst] as %st' ⟨%Hst', Hst⟩
  · iframe
  try wp_auto
  icases typedPointsto_not_null_dup _ _ _ $$ «$r0» with ⟨Hr0, %Hnn⟩
  have hkk := split_sint_nat_k k hkz
  ihave Hins := (ownSlice_split_all (W64 (k : Int)) nv.inodes' (DFrac.own 1) ins
    ⟨by omega, by have := Hl.1; omega⟩).1 $$ Hins
  rw [hkk]
  icases Hins with ⟨HL, HR⟩
  ihave Hcap := (ownSliceCap_slice nv.inodes' (W64 (k : Int)) (DFrac.own 1)
    ⟨by omega, by have := Hl.1; omega, Hcw.2⟩).1 $$ Hcap
  iapply HΦ
  iframe Hb
  iright
  iexists k, pl, ({ pv0 with children' := s' } : node), pcs0 ++ [«$r0_ptr»]
  isplitr
  · ipureintro
    refine ⟨hk2, hk3, Hnn, Hpl0.1, ?_⟩
    rcases Hpl0.2 with ⟨hp, hpv, hpc⟩ | ⟨hp, hpl, hpv, hpc⟩
    · refine Or.inl ⟨hp, ?_, by rw [hpc]; rfl⟩
      rw [hpv]; rfl
    · exact Or.inr ⟨hp, hpl, by rw [hpv], by rw [hpc]⟩
  simp only [splitLeft, splitRight, inodesL, inodesR]
  rw [Hst']
  iframe

end proof

end bbolt
end EtcdGrove
end Perennial
