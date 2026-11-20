/-
`typed.mergingWalker.visitMapItems`: a member of the recursion cluster `typed.mergingWalkerRec` (`mergingWalkerRec.lean`); its proof is the
projection of the cluster's (its body is `mergingWalker__visitMapItemsBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker__visitMapItemsBody
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
theorem typed.mergingWalker.visitMapItems.wp_proofBody
    (h_MapZipUsing : value.MapZipUsing.spec (GF := GF)) :
    typed.mergingWalker.visitMapItems.specBody (GF := GF) := by
  unfold typed.mergingWalker.visitMapItems.specBody typed.mergingWalkerRec.specI
    typed.mergingWalker.merge.specI typed.mergingWalker.doList.specI
    typed.mergingWalker.doMap.specI typed.mergingWalker.mergeListItem.specI
    typed.mergingWalker.visitListItems.specI typed.mergingWalker.visitMapItem.specI
    typed.mergingWalker.visitMapItems.specI
  iintro #IH
  icases IH with ⟨-, -, -, -, -, #HV, -⟩
  iintro %w %sc %S %st %tp %fs %e %rel %lm %rm %ol %or_ %sp
  wp_start as ⟨Hown, #Hm, #Hl, #Hr, %Hpre⟩
  obtain ⟨Hfind, Hout, Hleaf, Hcl, Hcr⟩ := Hpre
  ihave %hL := LawBMZ.isMapO_sorted lm ol $$ Hl
  ihave %hR := LawBMZ.isMapO_sorted rm or_ $$ Hr
  iunfold mwOwn at Hown
  icases Hown with ⟨%ps, Hcore, Hp, Hsp, Ha⟩
  iunfold mwCore at Hcore
  icases Hcore with ⟨%tr0, %rule0, %o0, Hw, #Htr0, #Hsc0, %Hwf, #Hrule0, #Ho0⟩
  have Hnd : (fs.map (·.1)).Nodup := Schema.WF_fields_nodup_law_holds S _ fs e rel Hwf Hfind
  let g := LawBMZ.resM S fs e (kvsOrEmpty ol) (kvsOrEmpty or_)
  have hfin := LawBMZ.mergeMapOut_eq S fs e _ _ hL hR
  rw [hfin]
  wp_auto
  wp_apply (wp_map_make1 (K := GoString) (V := GoInterface)) as %om Hom
  try wp_auto
  ipersist w
  ipersist t
  ipersist out
  wp_func_lits
  wp_apply h_MapZipUsing st.alloc lm rm ol or_ (W64 0) _
    (fun done => iprop(∃ (psj : fieldpath.Path) (spj : Loc) (el : GoSlice) (M : GMap GoString GoInterface),
      errs_ptr ↦ el ∗ noErrs el ∗ mwCore w sc S st psj spj st.alloc ∗ ownPath psj st.path ∗
      spareWalkers typed.mergingWalker spj ∗ ⌜sp ≠ null → spj = sp⌝ ∗
      om ↦$ M ∗ ⌜LawBMZ.MInv M done g⌝ ∗
      (□ ∀ (k : GoString) (x : UVal), ⌜k ∈ done ∧ g k = some x⌝ -∗
        ∃ i, ⌜M !! k = some i⌝ ∗ isIface i x) ∗
      ⌜∀ k ∈ done, k ∈ zipKeys ol or_⌝))
    iprop(False) $$ [Ha errs Hw Hp Hsp Hom] as %b ⟨Ha, Hpost⟩
  · iframe Ha
    isplitr; iexact Hl
    isplitr; iexact Hr
    isplitr; ipureintro; left; rfl
    isplitr; ipureintro; intro h; exact absurd h (by decide)
    isplitr
    · iunfold zipFnOk
      simp only [LawBMZ.optValF_isValO]
      imodintro
      iintro %done %k %vl %vr %Hst %Φ' !> ⟨Ha, ⟨%psj, %spj, %el, %M, errs, Hel, Hcore, Hp, Hsp, %Hspj, Hom, %HM, #HMi, %Hdone⟩, Hvl, Hvr⟩ HΦ'
      simp only [mapIterStep, Bool.false_eq_true, ↓reduceIte] at Hst
      obtain ⟨hk, hkd⟩ := Hst
      obtain ⟨t', hft, hsome, hcl, hcr⟩ :=
        LawBMZ.key_conf S st.t fs e rel Hfind ol or_ Hcl Hcr k hk
      have hgk : g k = mergeO S t' (lookupKV k (kvsOrEmpty ol)) (lookupKV k (kvsOrEmpty or_)) :=
        LawBMZ.resM_eq S fs e _ _ k t' hft
      have hsub : ∀ k' ∈ done ++ [k], k' ∈ zipKeys ol or_ := by
        intro k' hk'
        rcases List.mem_append.1 hk' with h | h
        · exact Hdone k' h
        · simp only [List.mem_singleton] at h; subst h; exact hk
      wp_auto
      wp_apply HV $$ %w %sc %S %st %tp %fs %e %rel %om %M %k %t'
        %vl %vr %(DFrac.own 1) %(DFrac.own 1) %_ %_ %spj [Ha Hcore Hp Hsp Hom Hvl Hvr]
        as %errs2 ⟨Herrs2, ⟨%spk, Hown2, %Hspk⟩, Hvl, Hvr, Hres⟩
      · iframe Hvl Hvr Hom
        isplitl [Ha Hcore Hp Hsp]
        · unfold mwOwn
          iexists psj
          iframe
        isplitr; iexact Hm
        ipureintro
        exact ⟨Hnd, hft, hsome, hcl, hcr, Hleaf⟩
      wp_apply LawA2.wp_append_noErrs el errs2 $$ [Hel Herrs2] as %el' Hel'
      · iframe
      try wp_auto
      iunfold mwOwn at Hown2
      icases Hown2 with ⟨%ps3, Hcore3, Hp3, Hsp3, Ha⟩
      iapply HΦ'
      simp only [↓reduceIte]
      iframe Ha Hvl Hvr
      have hspk : sp ≠ null → spk = sp := by
        intro h; have h1 := Hspj h; subst h1; exact Hspk h
      cases hm : mergeO S t' (lookupKV k (kvsOrEmpty ol)) (lookupKV k (kvsOrEmpty or_)) with
      | none =>
        have hg : g k = none := by rw [hgk, hm]
        simp only
        iexists ps3, spk, el', M
        iframe
        isplitr
        · ipureintro; exact hspk
        isplitr
        · ipureintro; exact LawBMZ.minv_none HM hg
        isplitr
        · imodintro
          iintro %k' %x ⟨%hk1, %hk2⟩
          rcases List.mem_append.1 hk1 with h | h
          · iapply HMi; ipureintro; exact ⟨h, hk2⟩
          · simp only [List.mem_singleton] at h; subst h; rw [hg] at hk2; cases hk2
        ipureintro; exact hsub
      | some x =>
        have hg : g k = some x := by rw [hgk, hm]
        simp only
        icases Hres with ⟨%i, Hom, #Hi⟩
        iexists ps3, spk, el', (<[k := i]> M)
        iframe
        isplitr
        · ipureintro; exact hspk
        isplitr
        · ipureintro; exact LawBMZ.minv_some i HM hg
        isplitr
        · imodintro
          iintro %k' %x' ⟨%hk1, %hk2⟩
          by_cases hkk : k = k'
          · subst hkk
            rw [hg] at hk2; cases hk2
            iexists i
            isplitr
            · ipureintro; exact GMap.lookup_insert M k i
            · iexact Hi
          · rcases List.mem_append.1 hk1 with h | h
            · have hh : k' ∈ done ∧ g k' = some x' := ⟨h, hk2⟩
              ihave ⟨%i', %hi', #Hi'⟩ := HMi $$ %k' %x' %hh
              iexists i'
              isplitr
              · ipureintro; rw [GMap.lookup_insert_ne M i hkk]; exact hi'
              · iexact Hi'
            · simp only [List.mem_singleton] at h; exact absurd h.symm hkk
        ipureintro; exact hsub
    iexists ps, sp, _, ∅
    iframe
    isplitr
    · iapply noErrs_nil
    isplitl
    · unfold mwCore
      iexists tr0, rule0, o0
      iframe
      iframe #
      ipureintro; exact Hwf
    isplitr
    · ipureintro; exact fun _ => rfl
    isplitr
    · ipureintro; exact LawBMZ.minv_nil g
    isplitr
    · imodintro; iintro %k %x %h; simp at h
    ipureintro; simp
  iunfold mapIterPost at Hpost
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    iexfalso; iexact Hpost
  simp only [↓reduceIte]
  icases Hpost with ⟨%done, %Hdone, %psj, %spj, %el, %M, errs, Hel, Hcore, Hp, Hsp, %Hspj, Hom, %HM, #HMi, -⟩
  simp only [mapIterDone, Bool.false_eq_true, ↓reduceIte] at Hdone
  rw [LawBMZ.zipKeys_eq] at Hdone
  have hemp := LawBMZ.minv_empty HM Hdone
  have hsorted := LawBMZ.entriesOf_sorted g _ (LawBMZ.zkeys_sorted _ _ hL hR)
  try wp_auto
  iunfold mwCore at Hcore
  icases Hcore with ⟨%tr1, %rule1, %o1, Hw, #Htr1, -, -, #Hrule1, #Ho1⟩
  rw [Hout]
  simp only [outRep]
  icases Ho1 with %ho1
  subst ho1
  wp_apply (wp_map_len_lt om M (DFrac.own 1)) $$ Hom as ⟨Hom, %Hsz⟩
  cases hE : (LawBMZ.entriesOf g (LawBMZ.zkeys (kvsOrEmpty ol) (kvsOrEmpty or_))).isEmpty
  · have hne : M.size ≠ 0 := fun h => by rw [hemp.1 h] at hE; cases hE
    have hpos : decide (sint.Z (W64 0) < sint.Z (W64 (M.size : Nat))) = true := by
      apply decide_eq_true
      have h1 : 0 < M.size := Nat.pos_of_ne_zero hne
      have h2 : M.size < 2 ^ 63 := Hsz
      have h3 : sint.Z (W64 (M.size : Int)) = (M.size : Int) := by word
      rw [h3]
      have h4 : sint.Z (W64 0) = 0 := by word
      rw [h4]
      omega
    rw [hpos]
    simp only [Bool.false_eq_true, ↓reduceIte]
    iapply wp_fupd
    wp_auto
    ipersist Hom
    ipersist i
    imodintro
    ihave #Hiface := LawBMZ.isIface_entries om M
      (LawBMZ.entriesOf g (LawBMZ.zkeys (kvsOrEmpty ol) (kvsOrEmpty or_))) hsorted
      (fun k => LawBMZ.minv_final HM Hdone k) $$ Hom []
    · imodintro
      iintro %k %x %hkx
      rw [LawBMZ.lkv_entriesOf] at hkx
      by_cases hk : k ∈ LawBMZ.zkeys (kvsOrEmpty ol) (kvsOrEmpty or_)
      · simp only [hk, ↓reduceIte] at hkx
        have hh : k ∈ done ∧ g k = some x := ⟨Hdone.mem_iff.2 hk, hkx⟩
        iapply HMi $$ %k %x %hh
      · simp only [hk, ↓reduceIte] at hkx; cases hkx
    simp only
    iapply HΦ
    isplitl [Hel]
    · iexact Hel
    iexists spj
    isplitl
    · unfold mwOwn mwCore
      iexists psj
      iframe
      iframe #
      simp only [outRep]
      isplitr
      · ipureintro; exact Hwf
      iexists _
      isplitr
      · iexact i
      iexact Hiface
    ipureintro; exact Hspj
  · have hz : M.size = 0 := hemp.2 hE
    have hpos : decide (sint.Z (W64 0) < sint.Z (W64 (M.size : Nat))) = false := by
      rw [hz]; rfl
    rw [hpos]
    simp only [↓reduceIte]
    wp_auto
    iapply HΦ
    isplitl [Hel]
    · iexact Hel
    iexists spj
    isplitl
    · have hst : MWSt.mk st.lhs st.rhs st.t st.path none st.inLeaf st.alloc = st := by
        cases st; simp_all
      rw [hst]
      unfold mwOwn mwCore
      iexists psj
      iframe
      iframe #
      rw [Hout]
      simp only [outRep]
      ipureintro; exact ⟨Hwf, trivial⟩
    ipureintro; exact Hspj

end proof

end smd
end EtcdGrove
end Perennial
