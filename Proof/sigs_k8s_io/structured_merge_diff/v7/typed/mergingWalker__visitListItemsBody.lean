/-
`typed.mergingWalker.visitListItems`: a member of the recursion cluster `typed.mergingWalkerRec` (`mergingWalkerRec.lean`); its proof is the
projection of the cluster's (its body is `mergingWalker__visitListItemsBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker__visitListItemsBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.MakePathElementMap
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElement__Equals
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElementMap__Get
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElementMap__Insert
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElementValueMap__Get
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructured__AtUsing
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructured__AtUsing_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructured__Length
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructured__Length_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker__indexListPathElements
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsBList2M
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsA2
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsA3
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsBPers
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

set_option maxHeartbeats 10000000 in
set_option synthInstance.maxHeartbeats 200000 in
set_option synthInstance.maxSize 4096 in
theorem typed.mergingWalker.visitListItems.wp_proofBody
    (h_MakePathElementMap : fieldpath.MakePathElementMap.spec (GF := GF))
    (h_PathElement_Equals : fieldpath.PathElement.Equals.spec (GF := GF))
    (h_PathElementMap_Get : fieldpath.PathElementMap.Get.spec (GF := GF))
    (h_PathElementMap_Insert : fieldpath.PathElementMap.Insert.spec (GF := GF))
    (h_PathElementValueMap_Get : fieldpath.PathElementValueMap.Get.spec (GF := GF))
    (h_listUnstructured_AtUsing : value.listUnstructured.AtUsing.spec (GF := GF))
    (h_listUnstructured_AtUsing_ptr : value.listUnstructured.AtUsing_ptr.spec (GF := GF))
    (h_listUnstructured_Length : value.listUnstructured.Length.spec (GF := GF))
    (h_listUnstructured_Length_ptr : value.listUnstructured.Length_ptr.spec (GF := GF))
    (h_mergingWalker_indexListPathElements : typed.mergingWalker.indexListPathElements.spec (GF := GF)) :
    typed.mergingWalker.visitListItems.specBody (GF := GF) := by
  unfold typed.mergingWalker.visitListItems.specBody typed.mergingWalkerRec.specI
    typed.mergingWalker.merge.specI typed.mergingWalker.doList.specI
    typed.mergingWalker.doMap.specI typed.mergingWalker.mergeListItem.specI
    typed.mergingWalker.visitListItems.specI typed.mergingWalker.visitMapItem.specI
    typed.mergingWalker.visitMapItems.specI
  iintro #IH
  icases IH with ⟨-, -, -, #HML, -, -, -⟩
  iintro %w %sc %S %st %tp %e %ks %ll %rl %ol %or_ %sp
  wp_start as ⟨Hown, #Hlr, Hl, Hr, %Hpre⟩
  obtain ⟨Hfind, Hout, Hleaf, Hcl, Hcr⟩ := Hpre
  iunfold mwOwn at Hown
  icases Hown with ⟨%ps, Hcore, Hp, Hsp, Ha⟩
  iunfold mwCore at Hcore
  icases Hcore with ⟨%tr, %rule, %o, Hw, #Htr, #Hsc, %Hwf, #Hrule, #Ho⟩
  obtain ⟨-, hksnd, fs, em, rel', hfe, -⟩ := LawB.list_wf S Hwf st.t e .associative ks Hfind (by decide)
  have hkne : ks ≠ [] := by
    rintro rfl
    have hw := LawB.find_wf S Hwf _ _ Hfind
    simp [Atom.wf] at hw
  have hside : ∀ o : Option (List UVal), confO S st.t (o.map UVal.list) →
      (∀ v ∈ o.getD [], conforms S e v ∧ itemKeyOk ks v) ∧ (keysOf ks (o.getD [])).Nodup := by
    intro o ho
    rcases o with _ | vs
    · simp [keysOf]
    · obtain ⟨hall, hassoc⟩ := conforms_item_law_holds S st.t e .associative ks vs Hfind ho
      obtain ⟨hks, hnd⟩ := hassoc rfl
      exact ⟨fun v hv => ⟨hall v hv, hks v hv⟩, hnd⟩
  have hsideL := hside ol Hcl
  have hsideR := hside or_ Hcr
  obtain ⟨ls, hls⟩ : ∃ ls, ol.getD [] = ls := ⟨_, rfl⟩
  obtain ⟨rs, hrs⟩ : ∃ rs, or_.getD [] = rs := ⟨_, rfl⟩
  rw [hls] at ⊢
  rw [hrs] at ⊢
  ihave #HlO := LawBL2.isListO_box ll ol $$ Hl
  ihave #HrO := LawBL2.isListO_box rl or_ $$ Hr
  wp_auto
  wp_bind (If _ _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ rhs_ptr ↦ rl ∗
      ∃ n : w64, rLen_ptr ↦ n ∗ ⌜n.toInt = rs.length⌝))) $$ [rhs rLen]
  · rcases or_ with _ | vsr
    · iunfold isListO at HrO
      icases HrO with %Hrl
      subst Hrl
      wp_auto
      isplitr; · ipureintro; rfl
      iframe
      ipureintro; subst hrs; rfl
    · iunfold isListO at HrO
      icases LawBL2.isListV_dispatchU h_listUnstructured_Length h_listUnstructured_Length_ptr
        h_listUnstructured_AtUsing h_listUnstructured_AtUsing_ptr rl vsr $$ [] with ⟨%ri, %Hri, #HLenR, -⟩
      · iframe #; iPkgInit
      subst Hri
      wp_auto
      wp_apply HLenR as %nr0 %Hnr0
      try wp_auto
      isplitr; · ipureintro; rfl
      iframe
      ipureintro; subst hrs; exact Hnr0
  iintro %v ⟨%hv, rhs, %nr, rLen, %Hnr⟩
  subst hv
  wp_auto
  wp_bind (If _ _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ lhs_ptr ↦ ll ∗
      ∃ n : w64, lLen_ptr ↦ n ∗ ⌜n.toInt = ls.length⌝))) $$ [lhs lLen]
  · rcases ol with _ | vsl
    · iunfold isListO at HlO
      icases HlO with %Hll
      subst Hll
      wp_auto
      isplitr; · ipureintro; rfl
      iframe
      ipureintro; subst hls; rfl
    · iunfold isListO at HlO
      icases LawBL2.isListV_dispatchU h_listUnstructured_Length h_listUnstructured_Length_ptr
        h_listUnstructured_AtUsing h_listUnstructured_AtUsing_ptr ll vsl $$ [] with ⟨%li, %Hli, #HLenL, -⟩
      · iframe #; iPkgInit
      subst Hli
      wp_auto
      wp_apply HLenL as %nl0 %Hnl0
      try wp_auto
      isplitr; · ipureintro; rfl
      iframe
      ipureintro; subst hls; exact Hnl0
  iintro %v ⟨%hv, lhs, %nl, lLen, %Hnl⟩
  subst hv
  wp_auto
  wp_bind (If _ _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ rLen_ptr ↦ nr ∗
      ∃ x : w64, outLen_ptr ↦ x ∗ ⌜0 ≤ sint.Z x⌝))) $$ [outLen rLen]
  · wp_if_destruct
    all_goals
      try wp_auto
      isplitr; · ipureintro; first | rfl | trivial
      iframe; ipureintro
      first | (show 0 ≤ BitVec.toInt nr; omega) | (show 0 ≤ BitVec.toInt nl; omega)
  iintro %v ⟨%hv, rLen, %ol0, outLen, %Hol0⟩
  subst hv
  wp_auto
  wp_apply (wp_slice_make3 (V := GoInterface) (W64 0) ol0 ⟨by decide, Hol0⟩) as %osl0 ⟨Hosl0, Hocap0, -⟩
  try wp_auto
  wp_apply h_mergingWalker_indexListPathElements w _ sc S tp e ks fs em rel' rl or_ false st.t.name
    $$ [Hw Ha] as %rpes %robs %rerrs ⟨Hw, Ha, Hrerr, ⟨%esR, HesR, #HpR⟩, ⟨%MR, HMR, HMRi⟩⟩
  · iframe; iframe #
    isplitr
    · ipureintro; rfl
    ipureintro
    refine ⟨Hwf, hkne, hfe, Hfind, ?_⟩
    rw [hrs]; rw [hrs] at hsideR; exact hsideR
  ihave #HMRi := LawBL2.itemMap_box _ _ $$ HMRi
  try wp_auto
  ihave Herr0 := noErrs_nil (GF := GF)
  wp_apply LawA2.wp_append_noErrs _ _ $$ [Herr0 Hrerr] as %errs1 Herrs1
  · iframe; iexact Herr0
  try wp_auto
  wp_apply h_mergingWalker_indexListPathElements w _ sc S tp e ks fs em rel' ll ol true st.t.name
    $$ [Hw Ha] as %lpes %lobs %lerrs ⟨Hw, Ha, Hlerr, ⟨%esL, HesL, #HpL⟩, ⟨%ML, HMLv, HMLi⟩⟩
  · iframe; iframe #
    isplitr
    · ipureintro; rfl
    ipureintro
    refine ⟨Hwf, hkne, hfe, Hfind, ?_⟩
    rw [hls]; rw [hls] at hsideL; exact hsideL
  ihave #HMLi := LawBL2.itemMap_box _ _ $$ HMLi
  try wp_auto
  wp_apply LawA2.wp_append_noErrs _ _ $$ [Herrs1 Hlerr] as %errs2 Herrs2
  · iframe
  try wp_auto
  iunfold noErrs at Herrs2
  iunfold ownErrs at Herrs2
  icases Herrs2 with ⟨Herrs2s, Herrs2c⟩
  ihave %Herrs2l := ownSlice_len _ _ _ $$ Herrs2s
  have hz : errs2.len = W64 0 := by simp at Herrs2l; word
  rw [hz]
  simp only [_root_.decide_true, Bool.not_true]
  wp_auto
  -- the keys of both sides
  obtain ⟨hallL, hndL⟩ := hsideL
  obtain ⟨hallR, hndR⟩ := hsideR
  rw [hls] at hallL hndL
  rw [hrs] at hallR hndR
  have hkL := LawBL2.keysOf_get ks ls (fun v hv => (hallL v hv).2)
  have hkR := LawBL2.keysOf_get ks rs (fun v hv => (hallR v hv).2)
  obtain ⟨L, hLdef⟩ : ∃ L, keysOf ks ls = L := ⟨_, rfl⟩
  obtain ⟨R, hRdef⟩ : ∃ R, keysOf ks rs = R := ⟨_, rfl⟩
  rw [hLdef] at hkL hndL
  rw [hRdef] at hkR hndR
  imod ownSlice_persist _ _ _ $$ HesR with #HesR
  imod ownSlice_persist _ _ _ $$ HesL with #HesL
  ihave %HesRl := ownSlice_len _ _ _ $$ HesR
  ihave %HesLl := ownSlice_len _ _ _ $$ HesL
  ihave %HpRl := isPEs_length_law_holds _ _ $$ HpR
  ihave %HpLl := isPEs_length_law_holds _ _ $$ HpL
  ihave #HpRat := LawBL2.isPEs_at _ _ $$ HpR
  ihave #HpLat := LawBL2.isPEs_at _ _ $$ HpL
  wp_apply (wp_slice_make3 (V := Loc) (W64 0) nr ⟨by decide, by show 0 ≤ BitVec.toInt nr; omega⟩)
    as %so0 ⟨Hso0, Hsocap0, -⟩
  try wp_auto
  rw [hrs, hRdef, hls, hLdef]
  rw [hrs, hRdef] at HpRl
  rw [hls, hLdef] at HpLl
  simp only [List.replicate_zero]
  rename_i igo_ptr
  irename : (igo_ptr ↦ zero_val w64 : IProp GF) => igo
  ihave HOL : ownPEVMap observedLHS_ptr ML $$ [observedLHS HMLv]
  · unfold ownPEVMap; iexists _; iframe
  ihave HI1 : (∃ (j : w64) (so : GoSlice) (idxs : List Nat) (iv : w64),
      "i" ∷ i_ptr ↦ j ∗ "igo" ∷ igo_ptr ↦ iv ∗ "sharedOrder" ∷ sharedOrder_ptr ↦ so ∗
      "Hso" ∷ so ↦* idxs.map (fun x : Nat => sliceIndexRef fieldpath.PathElement (x : Int) rpes) ∗
      "Hsocap" ∷ ownSliceCap Loc so (DFrac.own 1) ∗ "HOL" ∷ ownPEVMap observedLHS_ptr ML ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ R.length ∧ (∀ x ∈ idxs, x < R.length) ∧
        LawBL2.shKeys R idxs = (R.take (sint.nat j)).filter (fun k => decide (k ∈ L))⌝ : IProp GF)
    $$ [i igo sharedOrder Hso0 Hsocap0 HOL]
  · iexists _, _, [], _
    iframe
    simp only [List.map_nil]
    isplitl [Hso0]
    · iexact Hso0
    iframe
    ipureintro
    refine ⟨by decide, by simp, by simp, ?_⟩
    have h0 : sint.nat (W64 0) = 0 := rfl
    rw [h0]; simp [LawBL2.shKeys]
  wp_for HI1
  by_cases Hif : sint.Z j < sint.Z rpes.len
  · rw [if_pos (by simp [Hif])]
    have hjl : sint.nat j < R.length := by
      have : sint.Z j < sint.Z rpes.len := Hif
      have h1 := HesRl.1; have h2 := HesRl.2; rw [HpRl] at h1; word
    obtain ⟨ej, hej⟩ : ∃ ej, esR[sint.nat j]? = some ej :=
      ⟨_, List.getElem?_eq_getElem (by rw [HpRl]; exact hjl)⟩
    obtain ⟨kj, hkj⟩ : ∃ kj, R[sint.nat j]? = some kj := ⟨_, List.getElem?_eq_getElem hjl⟩
    ihave #Hpej := HpRat $$ %(sint.nat j) %ej %kj %(And.intro hej hkj)
    ihave ⟨#Hel, -⟩ := ownSlice_elem_acc (sint.Z j) ej rpes DFrac.discard esR Hj.1
      (by rw [show (sint.Z j).toNat = sint.nat j from rfl]; exact hej) $$ HesR
    have hb : (0 ≤ sint.Z j ∧ sint.Z j < sint.Z rpes.len) := ⟨Hj.1, Hif⟩
    wp_auto
    simp only [hb, and_self, ↓reduceIte]
    wp_auto
    simp only [hb, and_self, ↓reduceIte]
    wp_auto
    wp_apply h_PathElementValueMap_Get observedLHS_ptr ML ej kj $$ [HOL] as %x1 %ok1 ⟨HOL, %Hok1⟩
    · iframe; iframe #
    ihave %HMLk := LawBL2.itemMap_isSome _ _ kj $$ HMLi
    have hjn : sint.nat (j + W64 1) = sint.nat j + 1 := by
      have := HesRl.1; have := HesRl.2; word
    have htk : R.take (sint.nat j + 1) = R.take (sint.nat j) ++ [kj] := by
      rw [List.take_add_one, hkj]; rfl
    have hjR : (sint.nat j : Int) < R.length := by omega
    by_cases hkL : kj ∈ L
    · have hsome : (ML kj).isSome = true := by
        rw [HMLk, LawBL2.itemOf_isSome, hLdef]; exact hkL
      obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hsome
      rw [hy] at Hok1
      obtain ⟨-, rfl⟩ := Hok1
      wp_auto
      wp_apply (wp_slice_literal (V := Loc) [sliceIndexRef fieldpath.PathElement (sint.Z j) rpes])
      isplitr
      · ipureintro; rfl
      iintro %sl2 ⟨Hsl2, -⟩
      try wp_auto
      wp_apply (wp_slice_append (V := Loc) so _ _ [sliceIndexRef fieldpath.PathElement (sint.Z j) rpes]
        (DFrac.own 1)) $$ [Hso Hsocap Hsl2] as %so' ⟨Hso', Hsocap', -⟩
      · iframe
      try wp_auto
      wp_for_post
      iframe
      iexists _, _, idxs ++ [sint.nat j], _
      iframe
      simp only [List.map_append, List.map_cons, List.map_nil]
      have hjZ : ((sint.nat j : Nat) : Int) = sint.Z j := by have := Hj.1; word
      rw [hjZ]
      isplitl [Hso']
      · iexact Hso'
      iframe
      ipureintro
      refine ⟨by word, by word, ?_, ?_⟩
      · intro x hx; rcases List.mem_append.1 hx with h | h
        · exact Hj.2.2.1 x h
        · simp at h; subst h; exact hjl
      · rw [hjn, htk, List.filter_append, ← Hj.2.2.2]
        simp [LawBL2.shKeys, List.filterMap_append, hkj, hkL]
    · have hnone : (ML kj).isSome = false := by
        rw [HMLk]; cases h : (itemOf ks ls kj).isSome
        · rfl
        · rw [LawBL2.itemOf_isSome, hLdef] at h; exact absurd h hkL
      rw [Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at hnone
      rw [hnone] at Hok1
      obtain ⟨-, rfl⟩ := Hok1
      wp_auto
      wp_for_post
      iframe
      iexists _, _, idxs, _
      iframe
      ipureintro
      refine ⟨by word, by word, Hj.2.2.1, ?_⟩
      rw [hjn, htk, List.filter_append, ← Hj.2.2.2]
      simp [hkL]
  rw [if_neg (by simp [Hif, false_neq_true])]
  simp only [decide_eq_false Hif, Bool.false_eq_true, ↓reduceIte]
  have hjR : sint.nat j = R.length := by
    have h1 := HesRl.1; have h2 := HesRl.2; rw [HpRl] at h1
    have h3 := Hj.2.1; have : ¬ sint.Z j < sint.Z rpes.len := Hif; word
  have hsh0 : LawBL2.shKeys R idxs = R.filter (fun k => decide (k ∈ L)) := by
    rw [Hj.2.2.2, hjR, List.take_length]
  wp_auto
  imod ownSlice_persist _ _ _ $$ Hso with #Hso
  ihave %Hsol := ownSlice_len _ _ _ $$ Hso
  ihave %Hsowf := ownSlice_wf _ _ _ $$ Hso
  wp_join (iprop(∃ (nsp : Loc) (sps : List Loc) (so' : GoSlice),
      nextShared_ptr ↦ nsp ∗ sharedOrder_ptr ↦ so' ∗ so' ↦*{DFrac.discard} sps ∗
      ⌜LawBL2.shRep (GF := GF) R rpes nsp sps (R.filter (fun k => decide (k ∈ L)))⌝) : IProp GF)
    at (If _ _ _) with [nextShared sharedOrder] as ⟨%nsp0, %sps0, %so1, nextShared, sharedOrder, #Hso1, %Hsh0⟩
  · by_cases hnil : idxs = []
    · have Hsol' := Hsol; have hsh0' := hsh0
      rw [hnil] at Hsol' hsh0'
      rw [hnil]
      have h0 : so.len = W64 0 := by simp at Hsol'; word
      rw [h0]
      wp_auto
      wp_join_done
      iexists _, [], _
      iframe
      simp only [List.map_nil]
      isplitr
      · iexact Hso
      ipureintro
      exact ⟨[], by simp, hsh0', rfl, rfl⟩
    · obtain ⟨i0, is, hid⟩ := List.exists_cons_of_ne_nil hnil
      have Hsol' := Hsol; have hsh0' := hsh0
      rw [hid] at Hsol' hsh0'
      rw [hid]
      have hpos : decide (sint.Z (W64 0) < sint.Z so.len) = true := by
        simp at Hsol'; simp only [decide_eq_true_eq]; have := Hsol'.1; have := Hsol'.2; word
      rw [hpos]
      wp_auto
      have hb0 : (0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z so.len) := by
        simp at Hsol'; refine ⟨by decide, ?_⟩; have := Hsol'.1; have := Hsol'.2; word
      simp only [hb0, and_self, ↓reduceIte]
      wp_apply (wp_load_slice_index (V := Loc) so (sint.Z (W64 0)) _ DFrac.discard
        (sliceIndexRef fieldpath.PathElement (i0 : Int) rpes) (by decide)) $$ [Hso] as -
      · iframe #; ipureintro; rfl
      try wp_auto
      have hb2 : (0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) ≤ sint.Z so.len ∧ sint.Z so.len ≤ sint.Z so.cap) := by
        simp at Hsol'; refine ⟨by decide, ?_, Hsowf.2⟩; have := Hsol'.1; have := Hsol'.2; word
      simp only [hb2, and_self, ↓reduceIte]
      wp_auto
      simp only [List.map_cons]
      ihave #Hso2 := LawBL2.ownSlice_tail_pers so _ _ $$ Hso
      wp_join_done
      iexists _, _, _
      iframe
      isplitr
      · iexact Hso2
      ipureintro
      exact ⟨i0 :: is, by rw [← hid]; exact Hj.2.2.1, hsh0', rfl, rfl⟩
  wp_apply h_MakePathElementMap _ $$ [] as %mv0 Hmv0
  · iframe #; ipureintro; exact HesRl.2
  try wp_auto
  ihave HOR : ownPEVMap observedRHS_ptr MR $$ [observedRHS HMR]
  · unfold ownPEVMap; iexists _; iframe
  ihave Hown : mwOwn w sc S st sp $$ [Hw Ha Hp Hsp]
  · unfold mwOwn mwCore
    iexists ps
    iframe
    iframe #
    ipureintro; exact Hwf
  ihave HI2 : (∃ (lI rI : w64) (done sh mg : List PE) (MG : PEMap GoInterface) (mv : fieldpath.PathElementMap)
      (nsp : Loc) (sps : List Loc) (so' osl : GoSlice) (xs : List GoInterface) (spj : Loc),
      "lI" ∷ lI_ptr ↦ lI ∗ "rI" ∷ rI_ptr ↦ rI ∗
      "nextShared" ∷ nextShared_ptr ↦ nsp ∗ "sharedOrder" ∷ sharedOrder_ptr ↦ so' ∗ "#Hso'" ∷ so' ↦*□ sps ∗
      "mergedRHS" ∷ mergedRHS_ptr ↦ mv ∗ "Hmv" ∷ ownPEMapV mv MG ∗
      "out" ∷ out_ptr ↦ osl ∗ "Hosl" ∷ osl ↦* xs ∗ "Hocap" ∷ ownSliceCap GoInterface osl (DFrac.own 1) ∗
      "#Hxs" ∷ □ (∀ q : GoInterface × UVal,
        ⌜q ∈ xs.zip (done.filterMap (LawBL2.mItem S e ks ls rs))⌝ -∗ isIface q.1 q.2) ∗
      "Hown" ∷ mwOwn w sc S st spj ∗ "HOL" ∷ ownPEVMap observedLHS_ptr ML ∗
      "HOR" ∷ ownPEVMap observedRHS_ptr MR ∗
      "%HI" ∷ ⌜LawBL2.shRep (GF := GF) R rpes nsp sps sh ∧ (∀ k, (MG k).isSome ↔ k ∈ mg) ∧
        (∀ k ∈ mg, k ∈ R.take (sint.nat rI)) ∧
        xs.length = (done.filterMap (LawBL2.mItem S e ks ls rs)).length ∧ (sp ≠ null → spj = sp) ∧
        0 ≤ sint.Z lI ∧ sint.nat lI ≤ L.length ∧ 0 ≤ sint.Z rI ∧ sint.nat rI ≤ R.length ∧
        LawBL2.MInv (fun x => decide (x ∈ R)) (mergeKeys L R) done (L.drop (sint.nat lI))
          (R.drop (sint.nat rI)) sh mg⌝ : IProp GF)
    $$ [lI rI nextShared sharedOrder mergedRHS Hmv0 out Hosl0 Hocap0 Hown HOL HOR]
  · iexists (W64 0), (W64 0), [], _, [], PEMap.empty, _, _, _, _, _, [], sp
    iframe
    iframe #
    simp only [List.filterMap_nil, List.zip_nil_right]
    isplitr
    · imodintro; iintro %q %hq; simp at hq
    ipureintro
    have h0 : sint.nat (W64 0) = 0 := rfl
    rw [h0, List.drop_zero, List.drop_zero]
    refine ⟨Hsh0, by simp [PEMap.empty], by simp, by simp, fun _ => trivial, by decide, by simp, by decide,
      by simp, ?_⟩
    exact LawBL2.MInv_init L R
  wp_for HI2
  sorry

end proof

end smd
end EtcdGrove
end Perennial
