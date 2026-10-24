/-
`intervalTree.Stab` (`interval_tree.go`) over a comparator: the proof of
`Spec/.../adt/intervalTree__Stab_gen.lean` (unit 4, generalized in the auth plan's S2b). Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalTree__Stab_gen
public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalTree__Visit_gen

@[expose] public section

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

theorem adt.intervalTree.Stab_gen.wp_proof
    (h_Visit_gen : adt.intervalTree.Visit_gen.spec (GF := GF) (hG := hG)) :
    adt.intervalTree.Stab_gen.spec (GF := GF) (hG := hG) := by
  intro K hK t L vb ve db de b e q
  wp_start as ⟨Ht, Hkb, Hke, %hq⟩
  icases adt.ownIvtK_read K _ _ _ $$ Ht with ⟨%tv, %T, Hr, Hc, Hs, Hn, %Hp, Hback⟩
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
    iframe Hkb Hke
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
      [∗list] x ∈ acc, ⌜x.1 ≠ null⌝ ∗ K.ivAt x.1 q x.2)
  wp_apply (h_Visit_gen K hK t L vb ve db de b e q _ I (fun _ => iprop(False)))
    $$ [Ht Hkb Hke ivs] as ⟨Hkb, Hke, %ps, %es, %r, %hpl, HI, Hwand⟩
  · iframe Ht Hkb Hke
    isplitr [ivs]
    · iunfold adt.ivVisitorOkK
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
      ihave %Hpvn := K.ivAt_not_null _ _ _ $$ Hpv
      ispecialize HΦ' $$ %true
      iapply HΦ'
      simp only [↓reduceIte]
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
  cases r with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    iexfalso; iexact HI
  | true =>
  simp only [↓reduceIte]
  obtain ⟨-, hpl, hes⟩ := hpl
  rw [hes hq] at hpl ⊢
  icases HI with ⟨%sl, Hivs, Hsl, Hcap, Hacc⟩
  wp_auto
  rw [List.map_fst_zip (by omega)]
  ispecialize HΦ $$ %sl %ps
  iapply HΦ
  iframe Hkb Hke Hsl Hcap Hacc Hwand
  ipureintro; exact hpl

end proof

end EtcdGrove
end Perennial
