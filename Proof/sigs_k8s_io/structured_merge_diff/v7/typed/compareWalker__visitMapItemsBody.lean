/-
`typed.compareWalker.visitMapItems`: a member of the recursion cluster `typed.compareWalkerRec` (`compareWalkerRec.lean`); its proof is the
projection of the cluster's (its body is `compareWalker__visitMapItemsBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker__visitMapItemsBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.MapZipUsing
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsBMapZip
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsBPers
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsA2
public import Proof.sigs_k8s_io.structured_merge_diff.v7.schema.LawProofs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open sigs_k8s_io.structured_merge_diff.v7

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : typed.Assumptions]

set_option synthInstance.maxHeartbeats 200000 in
set_option synthInstance.maxSize 4096 in
theorem typed.compareWalker.visitMapItems.wp_proofBody
    (h_MapZipUsing : value.MapZipUsing.spec (GF := GF)) :
    typed.compareWalker.visitMapItems.specBody (GF := GF) := by
  unfold typed.compareWalker.visitMapItems.specBody typed.compareWalkerRec.specI
    typed.compareWalker.compare.specI typed.compareWalker.compareListItem.specI
    typed.compareWalker.doList.specI typed.compareWalker.doMap.specI
    typed.compareWalker.visitListItems.specI typed.compareWalker.visitMapItem.specI
    typed.compareWalker.visitMapItems.specI
  iintro #IH
  icases IH with ⟨-, -, -, -, -, #HV, -⟩
  iintro %w %sc %S %st %c %C %tp %fs %e %rel %lm %rm %ol %or_ %sp
  wp_start as ⟨Hown, #Hm, #Hl, #Hr, %Hpre⟩
  obtain ⟨Hfind, Hleaf, Hcl, Hcr, Hcard⟩ := Hpre
  ihave %hL := LawBMZ.isMapO_sorted lm ol $$ Hl
  ihave %hR := LawBMZ.isMapO_sorted rm or_ $$ Hr
  iunfold cwOwn at Hown
  icases Hown with ⟨%ps, Hcore, Hp, Hsp, Ha, Hc⟩
  iunfold cwCore at Hcore
  icases Hcore with ⟨%tr0, Hw, #Htr0, #Hsc0, %Hwf⟩
  have Hnd : (fs.map (·.1)).Nodup := Schema.WF_fields_nodup_law_holds S _ fs e rel Hwf Hfind
  let f := LawBMZ.resC S fs e st.path (kvsOrEmpty ol) (kvsOrEmpty or_)
  have hfin := LawBMZ.cmpMapOut_eq S fs e st.path _ _ hL hR
  rw [hfin] at Hcard ⊢
  wp_auto
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface)) as %om Hom
  try wp_auto
  ipersist w
  ipersist t
  ipersist out
  wp_func_lits
  wp_apply h_MapZipUsing st.alloc lm rm ol or_ (W64 0) _
    (fun done => iprop(∃ (psj : fieldpath.Path) (spj : Loc) (trj : schema.TypeRef) (el : GoSlice),
      errs_ptr ↦ el ∗ noErrs el ∗
      w ↦ (typed.compareWalker.mk st.lhs st.rhs sc trj psj c st.inLeaf spj st.alloc) ∗
      isTypeRef trj st.t ∗ ownPath psj st.path ∗ spareWalkers typed.compareWalker spj ∗
      ⌜sp ≠ null → spj = sp⌝ ∗ ownCmp c (C.union (Cmp.unionAll (done.map f))) ∗
      ⌜∀ k ∈ done, k ∈ zipKeys ol or_⌝))
    iprop(False) $$ [Ha errs Hw Hp Hsp Hc] as %b ⟨Ha, Hpost⟩
  · iframe Ha
    isplitr; iexact Hl
    isplitr; iexact Hr
    isplitr; ipureintro; left; rfl
    isplitr; ipureintro; intro h; exact absurd h (by decide)
    isplitr
    · iunfold zipFnOk
      simp only [LawBMZ.optValF_isValO]
      imodintro
      iintro %done %k %vl %vr %Hst %Φ' !> ⟨Ha, ⟨%psj, %spj, %trj, %el, errs, Hel, Hw, #Htrj, Hp, Hsp, %Hspj, Hc, %Hdone⟩, Hvl, Hvr⟩ HΦ'
      simp only [mapIterStep, Bool.false_eq_true, ↓reduceIte] at Hst
      obtain ⟨hk, hkd⟩ := Hst
      obtain ⟨t', hft, hsome, hcl, hcr⟩ :=
        LawBMZ.key_conf S st.t fs e rel Hfind ol or_ Hcl Hcr k hk
      have hfk : f k = cmpO S t' (st.path ++ [.field k]) (lookupKV k (kvsOrEmpty ol))
          (lookupKV k (kvsOrEmpty or_)) := by
        simp only [f, LawBMZ.resC, hft]
      have hsub : ∀ k' ∈ done ++ [k], k' ∈ LawBMZ.zkeys (kvsOrEmpty ol) (kvsOrEmpty or_) := by
        intro k' hk'
        rw [← LawBMZ.zipKeys_eq]
        rcases List.mem_append.1 hk' with h | h
        · exact Hdone k' h
        · simp only [List.mem_singleton] at h; subst h; exact hk
      have hcard2 := LawBMZ.cardLt_keys C f (done ++ [k]) _ hsub _ Hcard
      rw [← LawBMZ.unionAll_snoc, hfk] at hcard2
      wp_auto
      wp_apply HV $$ %w %sc %S %st %c %(C.union (Cmp.unionAll (done.map f))) %tp %fs %e %rel %om %k %t'
        %vl %vr %(DFrac.own 1) %(DFrac.own 1) %_ %_ %spj [Ha Hw Hp Hsp Hc Hvl Hvr]
        as %errs2 ⟨Herrs2, Hvl, Hvr, %spk, Hown2, %Hspk⟩
      · iframe Hvl Hvr
        isplitl [Ha Hw Hp Hsp Hc]
        · unfold cwOwn cwCore
          iexists psj
          iframe
          iframe #
          ipureintro; exact Hwf
        isplitr; iexact Hm
        ipureintro
        exact ⟨Hnd, hft, hsome, hcl, hcr, Hleaf, hcard2⟩
      wp_apply LawA2.wp_append_noErrs el errs2 $$ [Hel Herrs2] as %el' Hel'
      · iframe
      try wp_auto
      iunfold cwOwn at Hown2
      icases Hown2 with ⟨%ps3, Hcore3, Hp3, Hsp3, Ha, Hc⟩
      iunfold cwCore at Hcore3
      icases Hcore3 with ⟨%tr3, Hw, #Htr3, -, -⟩
      iapply HΦ'
      simp only [↓reduceIte]
      iframe Ha Hvl Hvr
      iexists ps3, spk, tr3, el'
      rw [← LawBMZ.unionAll_snoc, hfk]
      iframe
      iframe #
      ipureintro
      refine ⟨fun h => ?_, fun k' hk' => ?_⟩
      · have h1 := Hspj h; subst h1; exact Hspk h
      · rw [LawBMZ.zipKeys_eq]; exact hsub k' hk'
    iexists ps, sp, tr0, _
    rw [LawBMZ.cmp_union_nil]
    iframe
    isplitr
    · iapply noErrs_nil
    iframe #
    isplitr
    · ipureintro; exact fun _ => rfl
    ipureintro; simp
  iunfold mapIterPost at Hpost
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    iexfalso; iexact Hpost
  · simp only [↓reduceIte]
    icases Hpost with ⟨%done, %Hdone, %psj, %spj, %trj, %el, errs, Hel, Hw, #Htrj, Hp, Hsp, %Hspj, Hc, -⟩
    simp only [mapIterDone, Bool.false_eq_true, ↓reduceIte] at Hdone
    rw [LawBMZ.unionAll_perm f Hdone, LawBMZ.zipKeys_eq]
    wp_auto
    iapply HΦ
    iframe
    iexists spj
    isplitl
    · unfold cwOwn cwCore
      iexists psj
      iframe
      iframe #
      ipureintro; exact Hwf
    ipureintro; exact Hspj

end proof

end smd
end EtcdGrove
end Perennial
