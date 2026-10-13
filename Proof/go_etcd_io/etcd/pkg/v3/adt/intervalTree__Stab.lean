module

public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalTree__Stab
public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalTree__Visit

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.pkg.v3.adt

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.adt.Assumptions]

theorem adt.intervalTree.Stab.wp_proof
    (h_Visit : adt.intervalTree.Visit.spec (GF := GF) (hG := hG)) :
    adt.intervalTree.Stab.spec (GF := GF) (hG := hG) := by
  intro t L b e q
  wp_start as ⟨Ht, %hq⟩
  icases adt.ownIvt_read _ _ _ $$ Ht with ⟨%tv, %T, Hr, Hc, Hs, Hn, %Hp, Hback⟩
  wp_auto
  obtain ⟨hTL, -, -, hcnt, hlen⟩ := Hp
  ihave Ht := Hback $$ [Hr Hc Hs Hn]
  · iframe
  wp_if_destruct
  · -- an empty tree
    have hL : L = [] := by
      rw [hcnt] at Hif
      exact List.eq_nil_of_length_eq_zero (by word)
    subst hL
    ispecialize HΦ $$ %slice.nil %([] : List Loc)
    iapply HΦ
    simp only [adt.stab, List.filter_nil, List.zip_nil_left, List.length_nil]
    isplitl []
    · iapply ownSlice_nil
    isplitl []
    · iapply ownSliceCap_nil
    isplitl []
    · ipureintro; trivial
    isplitl []
    · iapply BigSepL.bigSepL_nil.2; itrivial
    iintro -
    iexact Ht
  let I : List (Loc × adt.Entry) → IProp GF := fun acc =>
    iprop(∃ sl : GoSlice, ivs_ptr ↦ sl ∗ sl ↦* acc.map Prod.fst ∗ ownSliceCap Loc sl (DFrac.own 1) ∗
      [∗list] x ∈ acc, ⌜x.1 ≠ null⌝ ∗
        x.1 ↦{DFrac.own q} ({ Ivl' := adt.affIvl x.2.1.1 x.2.1.2, Val' := x.2.2 } : IntervalValue))
  wp_apply (h_Visit t L b e q _ I hq) $$ [Ht ivs] as %ps ⟨%hpl, HI, Hwand⟩
  · iframe Ht
    isplitr [ivs]
    · iunfold adt.ivVisitorOk
      imodintro
      iintro %pv %z %acc %Φ'
      imodintro
      iintro ⟨%_, HIa, Hpv⟩ HΦ'
      icases HIa with ⟨%sl, Hivs, Hsl, Hcap, Hacc⟩
      wp_auto
      wp_apply wp_slice_literal (l := [pv])
      isplitr
      · ipureintro; rfl
      iintro %zsl ⟨Hz, -⟩
      wp_auto
      wp_apply wp_slice_append $$ [$Hsl $Hcap $Hz] as %sl1 ⟨Hsl, Hcap, -⟩
      ihave %Hpvn := typedPointsto_not_null _ _ _ $$ Hpv
      iapply HΦ'
      iexists sl1
      simp only [List.map_append, List.map_cons, List.map_nil]
      iframe Hivs Hsl Hcap
      iapply BigSepL.bigSepL_snoc.2
      iframe Hacc Hpv
      ipureintro; exact Hpvn
    iexists slice.nil
    simp only [List.map_nil]
    iframe ivs
    isplitl []
    · iapply ownSlice_nil
    isplitl []
    · iapply ownSliceCap_nil
    iapply BigSepL.bigSepL_nil.2; itrivial
  icases HI with ⟨%sl, Hivs, Hsl, Hcap, Hacc⟩
  wp_auto
  rw [List.map_fst_zip (by omega)]
  ispecialize HΦ $$ %sl %ps
  iapply HΦ
  iframe Hsl Hcap Hacc Hwand
  ipureintro; exact hpl

end proof

end EtcdGrove
end Perennial
