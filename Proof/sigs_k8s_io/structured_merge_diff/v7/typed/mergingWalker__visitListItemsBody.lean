/-
`typed.mergingWalker.visitListItems`: a member of the recursion cluster `typed.mergingWalkerRec` (`mergingWalkerRec.lean`); its proof is the
projection of the cluster's (its body is `mergingWalker__visitListItemsBody.lean`).

The proof: the set-up (both sides' `Length`, `out`'s capacity, the two `indexListPathElements`,
the shared order built by the range loop, its first pop), the loop invariant `HI2` (the merged
order `LawBL2.MInv`, the shared order `LawBL2.shRep`, `mergedRHS` holding the merged keys, `out`
holding the done keys' merges `LawBL2.mItem`), and the exit (`MInv_done`: the merged list is
`mergeListOut`). One iteration is joined (`wp_join`) after each of its three statements: the
first (both sides) merges equal heads (`MInv_eq`) or skips an out-of-order shared key
(`MInv_skip`), both `continue`; the second (the left side) merges a left-only key (`MInv_left`,
`continue`) or passes a merged one; the third (the right side) merges a right key (`MInv_right`,
or `MInv_nextL_nil` when the right side is done), popping the shared order when its head is
merged. The inner `errs = append(errs, errs...)` on one empty slice goes through
`wp_slice_append_dfrac` at the discarded fraction. An iteration that does nothing (a shared left
key not merged yet, the right side done) keeps the invariant: the loop is partial correctness.
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
  ihave #HMRp := LawBL2.itemMap_box _ _ $$ HMRi
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
  ihave #HMLp := LawBL2.itemMap_box _ _ $$ HMLi
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
  rcases HI with ⟨Hsh, HMG, HMGR, Hxsl, Hspj, HlI0, HlIL, HrI0, HrIR, HMI⟩
  have hlpl : sint.nat lpes.len = L.length := by rw [← HpLl, HesLl.1]
  have hrpl : sint.nat rpes.len = R.length := by rw [← HpRl, HesRl.1]
  wp_join (Q := fun v => iprop(⌜v = #(decide (sint.nat lI < L.length ∨ sint.nat rI < R.length))⌝ ∗
      rI_ptr ↦ rI ∗ rLen_ptr ↦ rpes.len)) at (If _ _ _) with [rI rLen]
  · wp_if_destruct
    · iframe
      ipureintro
      have : sint.nat lI < L.length := by have := HesLl.2; word
      simp [this]
    · iframe
      ipureintro
      have : ¬ sint.nat lI < L.length := by have := HesLl.2; word
      have h2 : (sint.nat rI < R.length) ↔ sint.Z rI < sint.Z rpes.len := by
        have := HesRl.2; constructor <;> intro h <;> word
      by_cases h3 : sint.nat rI < R.length
      · simp [this, h3, h2.1 h3]
      · have h4 : ¬ sint.Z rI < sint.Z rpes.len := fun h => h3 (h2.2 h)
        simp [this, h3, h4]
  iintro ⟨%hv, rI, rLen⟩
  rw [hv]
  by_cases hcond : sint.nat lI < L.length ∨ sint.nat rI < R.length
  · simp only [hcond, decide_true, ↓reduceIte]
    -- one iteration
    wp_auto
    wp_join (Q := fun v => iprop(lhsPEs_ptr ↦ lpes ∗ rhsPEs_ptr ↦ rpes ∗ lLen_ptr ↦ lpes.len ∗
        rLen_ptr ↦ rpes.len ∗ w_ptr ↦ w ∗ t_ptr ↦ tp ∗ lhs_ptr ↦ ll ∗
        ((⌜v = continueVal⌝ ∗ (∃ (lI rI : w64) (done sh mg : List PE) (MG : PEMap GoInterface) (mv : fieldpath.PathElementMap)
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
          (R.drop (sint.nat rI)) sh mg⌝ : IProp GF)) ∨
         (⌜v = executeVal ∧ ∀ l L' r R', L.drop (sint.nat lI) = l :: L' → R.drop (sint.nat rI) = r :: R' →
            l ≠ r ∧ LawBL2.skipC (fun x => decide (x ∈ R)) sh l = false⌝ ∗
          lI_ptr ↦ lI ∗ rI_ptr ↦ rI ∗ nextShared_ptr ↦ nsp ∗ sharedOrder_ptr ↦ so' ∗
          mergedRHS_ptr ↦ mv ∗ ownPEMapV mv MG ∗ out_ptr ↦ osl ∗ osl ↦* xs ∗
          ownSliceCap GoInterface osl (DFrac.own 1) ∗ mwOwn w sc S st spj ∗
          ownPEVMap observedLHS_ptr ML ∗ ownPEVMap observedRHS_ptr MR))))
      at (If _ _ _) with [lhsPEs rhsPEs lLen rLen w t lhs lI rI nextShared sharedOrder mergedRHS Hmv out
        Hosl Hocap Hown HOL HOR]
    · wp_if_destruct
      · wp_if_destruct
        · -- both in range
          have hlL : sint.nat lI < L.length := by word
          have hrR : sint.nat rI < R.length := by word
          obtain ⟨el, hel⟩ : ∃ x, esL[sint.nat lI]? = some x :=
            ⟨_, List.getElem?_eq_getElem (by rw [HpLl]; exact hlL)⟩
          obtain ⟨kl, hkl⟩ : ∃ x, L[sint.nat lI]? = some x := ⟨_, List.getElem?_eq_getElem hlL⟩
          obtain ⟨er, her⟩ : ∃ x, esR[sint.nat rI]? = some x :=
            ⟨_, List.getElem?_eq_getElem (by rw [HpRl]; exact hrR)⟩
          obtain ⟨kr, hkr⟩ : ∃ x, R[sint.nat rI]? = some x := ⟨_, List.getElem?_eq_getElem hrR⟩
          ihave #Hpel := HpLat $$ %(sint.nat lI) %el %kl %(And.intro hel hkl)
          ihave #Hper := HpRat $$ %(sint.nat rI) %er %kr %(And.intro her hkr)
          ihave ⟨#Hell, -⟩ := ownSlice_elem_acc (sint.Z lI) el lpes DFrac.discard esL HlI0
            (by rw [show (sint.Z lI).toNat = sint.nat lI from rfl]; exact hel) $$ HesL
          ihave ⟨#Helr, -⟩ := ownSlice_elem_acc (sint.Z rI) er rpes DFrac.discard esR HrI0
            (by rw [show (sint.Z rI).toNat = sint.nat rI from rfl]; exact her) $$ HesR
          have hbl : (0 ≤ sint.Z lI ∧ sint.Z lI < sint.Z lpes.len) := ⟨HlI0, by word⟩
          have hbr : (0 ≤ sint.Z rI ∧ sint.Z rI < sint.Z rpes.len) := ⟨HrI0, by word⟩
          have hdL := LawBL2.drop_cons L (sint.nat lI) kl hkl
          have hdR := LawBL2.drop_cons R (sint.nat rI) kr hkr
          simp only [hbl, hbr, and_self, ↓reduceIte]
          wp_auto
          simp only [hbl, hbr, and_self, ↓reduceIte]
          wp_auto
          wp_method_call; wp_call; wp_auto
          wp_apply h_PathElement_Equals el er kl kr $$ [] as %beq %Hbeq
          · iframe #
          obtain ⟨xl, hxl⟩ : ∃ x, ls[sint.nat lI]? = some x :=
            ⟨_, List.getElem?_eq_getElem (by rw [← hkL.1]; exact hlL)⟩
          have hkxl : keyOf ks xl = some kl := by rw [← hkL.2 _ _ hxl, hkl]
          have hil : itemOf ks ls kl = some xl :=
            LawBL2.itemOf_at ks ls (fun v hv => (hallL v hv).2) (by rw [hLdef]; exact hndL) _ _ _ hxl hkxl
          have hcl : conforms S e xl := (hallL xl (List.mem_of_getElem? hxl)).1
          cases beq
          · -- not equal: the skip test
            have hne : kl ≠ kr := fun h => by simpa using Hbeq.2 h
            wp_auto
            wp_apply h_PathElementValueMap_Get observedRHS_ptr MR el kl $$ [HOR] as %x2 %ok2 ⟨HOR, %Hok2⟩
            · iframe; iframe #
            ihave %HMRk := LawBL2.itemMap_isSome _ _ kl $$ HMRp
            have hR1 := LawBL2.itemOf_isSome ks rs kl
            rw [hRdef] at hR1
            have hok2 : ok2 = decide (kl ∈ R) := by
              cases hm : MR kl with
              | none =>
                rw [hm] at Hok2 HMRk
                rw [Hok2.2]
                have : kl ∉ R := fun h => by rw [← hR1, ← HMRk] at h; cases h
                simp [this]
              | some y =>
                rw [hm] at Hok2 HMRk
                rw [Hok2.2]
                have : kl ∈ R := by rw [← hR1, ← HMRk]; rfl
                simp [this]
            subst hok2
            by_cases hin : kl ∈ R
            · rw [decide_eq_true hin]
              wp_auto
              rcases LawBL2.shRep_head Hsh with ⟨hnull, hsh⟩ | ⟨i, hi, hnsp, hsh⟩
              · subst hnull
                wp_auto
                iframe; iright; iframe; ipureintro
                refine ⟨rfl, fun l L' r R' hL hR => ?_⟩
                rw [hdL, List.cons.injEq] at hL; rw [hdR, List.cons.injEq] at hR
                obtain ⟨rfl, -⟩ := hL; obtain ⟨rfl, -⟩ := hR
                refine ⟨hne, ?_⟩
                simp [LawBL2.skipC, hsh]
              · subst hnsp
                obtain ⟨es, hes⟩ : ∃ x, esR[i]? = some x :=
                  ⟨_, List.getElem?_eq_getElem (by rw [HpRl]; exact hi)⟩
                ihave #Hpes := HpRat $$ %i %es %(R[i]) %(And.intro hes (List.getElem?_eq_getElem hi))
                ihave ⟨#Hesi, -⟩ := ownSlice_elem_acc ((i : Nat) : Int) es rpes DFrac.discard esR (by omega)
                  (by simpa using hes) $$ HesR
                ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hesi
                rw [decide_eq_false Hnn]
                wp_auto
                simp only [hbl, and_self, ↓reduceIte]
                wp_auto
                wp_method_call; wp_call; wp_auto
                wp_apply h_PathElement_Equals es el R[i] kl $$ [] as %beq2 %Hbeq2
                · iframe #
                cases beq2
                · have hne2 : R[i] ≠ kl := fun h => by simpa using Hbeq2.2 h
                  wp_auto
                  have hln : sint.nat (lI + W64 1) = sint.nat lI + 1 := by have := HesLl.2; word
                  iframe
                  ileft
                  isplitr
                  · ipureintro; rfl
                  iexists (lI + W64 1), done, sh, mg, sps
                  iframe
                  iframe #
                  ipureintro
                  refine ⟨Hsh, HMG, HMGR, Hxsl, Hspj, by word, by word, HrI0, HrIR, ?_⟩
                  rw [hln]
                  rw [hdL, hdR] at HMI
                  rw [hdR]
                  exact LawBL2.MInv_skip hne
                    (by simp [LawBL2.skipC, hin, hsh, List.getElem?_eq_getElem hi, hne2]) HMI
                · have heq2 : R[i] = kl := Hbeq2.1 rfl
                  wp_auto
                  iframe; iright; iframe; ipureintro
                  refine ⟨rfl, fun l L' r R' hL hR => ?_⟩
                  rw [hdL, List.cons.injEq] at hL; rw [hdR, List.cons.injEq] at hR
                  obtain ⟨rfl, -⟩ := hL; obtain ⟨rfl, -⟩ := hR
                  refine ⟨hne, ?_⟩
                  simp [LawBL2.skipC, hsh, List.getElem?_eq_getElem hi, heq2]
            · rw [decide_eq_false hin]
              wp_auto
              iframe; iright; iframe; ipureintro
              refine ⟨rfl, fun l L' r R' hL hR => ?_⟩
              rw [hdL, List.cons.injEq] at hL; rw [hdR, List.cons.injEq] at hR
              obtain ⟨rfl, -⟩ := hL; obtain ⟨rfl, -⟩ := hR
              refine ⟨hne, ?_⟩
              simp [LawBL2.skipC, hin]
          have hkk : kl = kr := Hbeq.1 rfl
          subst hkk
          obtain ⟨xr, hxr⟩ : ∃ x, rs[sint.nat rI]? = some x :=
            ⟨_, List.getElem?_eq_getElem (by rw [← hkR.1]; exact hrR)⟩
          have hkxr : keyOf ks xr = some kl := by rw [← hkR.2 _ _ hxr, hkr]
          have hir : itemOf ks rs kl = some xr :=
            LawBL2.itemOf_at ks rs (fun v hv => (hallR v hv).2) (by rw [hRdef]; exact hndR) _ _ _ hxr hkxr
          have hcr : conforms S e xr := (hallR xr (List.mem_of_getElem? hxr)).1
          ihave ⟨%vl, %Hvl, #Hvl⟩ := LawBL2.itemMap_some _ _ kl xl hil $$ HMLp
          ihave ⟨%vr, %Hvr, #Hvr⟩ := LawBL2.itemMap_some _ _ kl xr hir $$ HMRp
          wp_auto
          ihave HMGo : ownPEMap mergedRHS_ptr MG $$ [mergedRHS Hmv]
          · unfold ownPEMap; iexists _; iframe
          wp_apply h_PathElementMap_Insert mergedRHS_ptr MG el kl _ $$ [HMGo] as HMGo
          · iframe; iframe #; ipureintro
            apply LawBL2.peMap_cardLt MG (R.take (sint.nat rI)) _ (fun k hk => HMGR k ((HMG k).1 hk))
            rw [List.length_take]; have := HesRl.2; word
          try wp_auto
          wp_apply h_PathElementValueMap_Get observedLHS_ptr ML el kl $$ [HOL] as %x1 %ok1 ⟨HOL, %Hok1⟩
          · iframe; iframe #
          rw [Hvl] at Hok1
          obtain ⟨hx1, rfl⟩ := Hok1
          rw [hx1]
          try wp_auto
          wp_apply h_PathElementValueMap_Get observedRHS_ptr MR el kl $$ [HOR] as %x2 %ok2 ⟨HOR, %Hok2⟩
          · iframe; iframe #
          rw [Hvr] at Hok2
          obtain ⟨hx2, rfl⟩ := Hok2
          rw [hx2]
          try wp_auto
          wp_apply HML $$ %w %sc %S %st %tp %e %ElemRel.associative %ks %el %kl %vl %vr %DFrac.discard
              %DFrac.discard %(some xl) %(some xr) %spj [Hown] as %o %errs ⟨⟨%spj', Hown, %Hspj'⟩, #Ho, Herrs, -, -⟩
          · iframe; iframe #
            simp only [isValO]
            iframe #
            ipureintro
            exact ⟨Or.inl rfl, hcl, hcr, Hleaf⟩
          have hmi : LawBL2.mItem S e ks ls rs kl = mergeO S e (some xl) (some xr) := by
            unfold LawBL2.mItem; rw [hil, hir]
          iunfold noErrs at Herrs
          iunfold ownErrs at Herrs
          icases Herrs with ⟨Herrs, Herrc⟩
          imod ownSlice_persist _ _ _ $$ Herrs with #Herrs
          wp_apply (wp_slice_append_dfrac (V := typed.ValidationError) errs [] DFrac.discard errs [] DFrac.discard)
            $$ [Herrc] as %e3 -
          · iframe; iframe #; ipureintro; exact DFrac.valid_discard
          try wp_auto
          wp_join iprop(∃ (osl' : GoSlice) (xs' : List GoInterface), out_ptr ↦ osl' ∗ osl' ↦* xs' ∗
              ownSliceCap GoInterface osl' (DFrac.own 1) ∗
              (□ ∀ q : GoInterface × UVal,
                ⌜q ∈ xs'.zip ((done ++ [kl]).filterMap (LawBL2.mItem S e ks ls rs))⌝ -∗ isIface q.1 q.2) ∗
              ⌜xs'.length = ((done ++ [kl]).filterMap (LawBL2.mItem S e ks ls rs)).length⌝)
            at (If _ _ _) with [out Hosl Hocap mergeOut] as ⟨%osl', %xs', out, Hosl, Hocap, #Hxs', %Hxsl'⟩
          · rw [LawBL2.fm_snoc, hmi]
            rcases hm : mergeO S e (some xl) (some xr) with _ | x
            · simp only [outRep]
              icases Ho with %ho
              subst ho
              wp_auto
              wp_join_done
              iexists osl, xs
              simp only [Option.toList, List.append_nil]
              iframe; iframe #
              ipureintro; exact Hxsl
            · simp only [outRep]
              icases Ho with ⟨%i, #Hoi, #Hix⟩
              ihave %Hon := typedPointsto_not_null _ _ _ $$ Hoi
              rw [decide_eq_false Hon]
              wp_auto
              wp_apply (wp_slice_literal (V := GoInterface) [i])
              isplitr
              · ipureintro; rfl
              iintro %sl2 ⟨Hsl2, -⟩
              try wp_auto
              wp_apply (wp_slice_append (V := GoInterface) osl _ _ [i] (DFrac.own 1))
                $$ [Hosl Hocap Hsl2] as %osl2 ⟨Hosl2, Hocap2, -⟩
              · iframe
              try wp_auto
              wp_join_done
              iexists osl2, xs ++ [i]
              iframe
              simp only [Option.toList]
              isplitr
              · imodintro; iintro %q %hq
                rcases LawBL2.zip_snoc_mem _ _ Hxsl _ _ q hq with h | h
                · iapply Hxs; ipureintro; exact h
                · subst h; iexact Hix
              ipureintro; simp [Hxsl]
          ihave %Hso'l := ownSlice_len _ _ _ $$ Hso'
          ihave %Hso'wf := ownSlice_wf _ _ _ $$ Hso'
          wp_join iprop(∃ (nsp' : Loc) (sps' : List Loc) (so'' : GoSlice), nextShared_ptr ↦ nsp' ∗
              sharedOrder_ptr ↦ so'' ∗ so'' ↦*□ sps' ∗ ⌜LawBL2.shRep (GF := GF) R rpes nsp' sps' sh.tail⌝)
            at (If _ _ _) with [nextShared sharedOrder] as ⟨%nsp', %sps', %so'', nextShared, sharedOrder, #Hso'', %Hsh'⟩
          · rcases sps with _ | ⟨p, ps⟩
            · have h0 : so'.len = W64 0 := by simp at Hso'l; word
              rw [h0]
              wp_auto
              wp_join_done
              iexists _, [], _
              iframe
              isplitr
              · iexact Hso'
              ipureintro; exact LawBL2.shRep_pop_nil Hsh
            · have hpos : decide (sint.Z (W64 0) < sint.Z so'.len) = true := by
                simp at Hso'l; simp only [decide_eq_true_eq]; have := Hso'l.1; have := Hso'l.2; word
              rw [hpos]
              wp_auto
              have hb0 : (0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z so'.len) := by
                simp at Hso'l; refine ⟨by decide, ?_⟩; have := Hso'l.1; have := Hso'l.2; word
              simp only [hb0, and_self, ↓reduceIte]
              wp_apply (wp_load_slice_index (V := Loc) so' (sint.Z (W64 0)) _ DFrac.discard p (by decide)) $$ [Hso'] as -
              · iframe #; ipureintro; rfl
              try wp_auto
              have hb2 : (0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) ≤ sint.Z so'.len ∧ sint.Z so'.len ≤ sint.Z so'.cap) := by
                simp at Hso'l; refine ⟨by decide, ?_, Hso'wf.2⟩; have := Hso'l.1; have := Hso'l.2; word
              simp only [hb2, and_self, ↓reduceIte]
              wp_auto
              ihave #Hso2 := LawBL2.ownSlice_tail_pers so' _ _ $$ Hso'
              wp_join_done
              iexists _, _, _
              iframe
              isplitr
              · iexact Hso2
              ipureintro; exact LawBL2.shRep_pop_cons Hsh
          have hln : sint.nat (lI + W64 1) = sint.nat lI + 1 := by have := HesLl.2; word
          have hrn : sint.nat (rI + W64 1) = sint.nat rI + 1 := by have := HesRl.2; word
          iunfold ownPEMap at HMGo
          icases HMGo with ⟨%mv', mergedRHS, Hmv⟩
          iframe
          ileft
          isplitr
          · ipureintro; rfl
          iexists (lI + W64 1), (rI + W64 1), done ++ [kl], sh.tail, kl :: mg, _, mv', nsp', sps', so'', osl',
            xs', spj'
          iframe
          iframe #
          ipureintro
          refine ⟨Hsh', ?_, ?_, Hxsl', ?_, by word, by word, by word, by word, ?_⟩
          · intro k
            simp only [PEMap.insert, List.mem_cons]
            by_cases hk : k = kl
            · simp [hk]
            · simp [hk, HMG]
          · intro k hk
            rw [hrn, List.take_add_one, hkr]
            rcases List.mem_cons.1 hk with rfl | hk
            · simp
            · exact List.mem_append_left _ (HMGR k hk)
          · intro h
            have h1 := Hspj h
            rw [Hspj' (by rw [h1]; exact h), h1]
          · rw [hln, hrn]
            rw [hdL, hdR] at HMI
            exact LawBL2.MInv_eq HMI
        · iframe; iright; iframe; ipureintro
          refine ⟨trivial, fun l L' r R' _ hR => ?_⟩
          exfalso; rw [LawBL2.drop_nil _ _ (by word)] at hR; cases hR
      · iframe; iright; iframe; ipureintro
        refine ⟨trivial, fun l L' r R' hL _ => ?_⟩
        exfalso; rw [LawBL2.drop_nil _ _ (by word)] at hL; cases hL
    iintro ⟨lhsPEs, rhsPEs, lLen, rLen, w, t, lhs, Hc1⟩
    icases Hc1 with (⟨%Hv, HI2⟩ | ⟨⟨%Hv, %HP1⟩, lI, rI, nextShared, sharedOrder, mergedRHS, Hmv, out, Hosl,
      Hocap, Hown, HOL, HOR⟩)
    · subst Hv
      wp_auto
      wp_for_post
      iframe
    subst Hv
    wp_auto
    wp_join (Q := fun v => iprop(lhsPEs_ptr ↦ lpes ∗ rhsPEs_ptr ↦ rpes ∗ lLen_ptr ↦ lpes.len ∗
        rLen_ptr ↦ rpes.len ∗ w_ptr ↦ w ∗ t_ptr ↦ tp ∗ lhs_ptr ↦ ll ∗
        ((⌜v = continueVal⌝ ∗ (∃ (lI rI : w64) (done sh mg : List PE) (MG : PEMap GoInterface) (mv : fieldpath.PathElementMap)
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
          (R.drop (sint.nat rI)) sh mg⌝ : IProp GF)) ∨
         (∃ (lI' : w64) (mvx : fieldpath.PathElementMap), ⌜v = executeVal ∧ 0 ≤ sint.Z lI' ∧ sint.nat lI' ≤ L.length ∧
            L.drop (sint.nat lI') = LawBL2.nextL (L.drop (sint.nat lI)) mg ∧
            ∀ l L', L.drop (sint.nat lI) = l :: L' → decide (l ∈ R) = true⌝ ∗
          lI_ptr ↦ lI' ∗ rI_ptr ↦ rI ∗ nextShared_ptr ↦ nsp ∗ sharedOrder_ptr ↦ so' ∗
          mergedRHS_ptr ↦ mvx ∗ ownPEMapV mvx MG ∗ out_ptr ↦ osl ∗ osl ↦* xs ∗
          ownSliceCap GoInterface osl (DFrac.own 1) ∗ mwOwn w sc S st spj ∗
          ownPEVMap observedLHS_ptr ML ∗ ownPEVMap observedRHS_ptr MR))))
      at (If _ _ _) with [lhsPEs rhsPEs lLen rLen w t lhs lI rI nextShared sharedOrder mergedRHS Hmv out
        Hosl Hocap Hown HOL HOR]
    · wp_if_destruct
      · have hlL : sint.nat lI < L.length := by word
        obtain ⟨el, hel⟩ : ∃ x, esL[sint.nat lI]? = some x :=
          ⟨_, List.getElem?_eq_getElem (by rw [HpLl]; exact hlL)⟩
        obtain ⟨kl, hkl⟩ : ∃ x, L[sint.nat lI]? = some x := ⟨_, List.getElem?_eq_getElem hlL⟩
        ihave #Hpel := HpLat $$ %(sint.nat lI) %el %kl %(And.intro hel hkl)
        ihave ⟨#Hell, -⟩ := ownSlice_elem_acc (sint.Z lI) el lpes DFrac.discard esL HlI0
          (by rw [show (sint.Z lI).toNat = sint.nat lI from rfl]; exact hel) $$ HesL
        have hbl : (0 ≤ sint.Z lI ∧ sint.Z lI < sint.Z lpes.len) := ⟨HlI0, by word⟩
        have hdL := LawBL2.drop_cons L (sint.nat lI) kl hkl
        have hln : sint.nat (lI + W64 1) = sint.nat lI + 1 := by have := HesLl.2; word
        obtain ⟨xl, hxl⟩ : ∃ x, ls[sint.nat lI]? = some x :=
          ⟨_, List.getElem?_eq_getElem (by rw [← hkL.1]; exact hlL)⟩
        have hkxl : keyOf ks xl = some kl := by rw [← hkL.2 _ _ hxl, hkl]
        have hil : itemOf ks ls kl = some xl :=
          LawBL2.itemOf_at ks ls (fun v hv => (hallL v hv).2) (by rw [hLdef]; exact hndL) _ _ _ hxl hkxl
        have hcl : conforms S e xl := (hallL xl (List.mem_of_getElem? hxl)).1
        simp only [hbl, and_self, ↓reduceIte]
        wp_auto
        wp_apply h_PathElementValueMap_Get observedRHS_ptr MR el kl $$ [HOR] as %x2 %ok2 ⟨HOR, %Hok2⟩
        · iframe; iframe #
        ihave %HMRk := LawBL2.itemMap_isSome _ _ kl $$ HMRp
        have hR1 := LawBL2.itemOf_isSome ks rs kl
        rw [hRdef] at hR1
        have hok2 : ok2 = decide (kl ∈ R) := by
          cases hm : MR kl with
          | none =>
            rw [hm] at Hok2 HMRk
            rw [Hok2.2]
            have : kl ∉ R := fun h => by rw [← hR1, ← HMRk] at h; cases h
            simp [this]
          | some y =>
            rw [hm] at Hok2 HMRk
            rw [Hok2.2]
            have : kl ∈ R := by rw [← hR1, ← HMRk]; rfl
            simp [this]
        subst hok2
        by_cases hin : kl ∈ R
        · rw [decide_eq_true hin]
          wp_auto
          ihave HMGo : ownPEMap mergedRHS_ptr MG $$ [mergedRHS Hmv]
          · unfold ownPEMap; iexists _; iframe
          wp_apply h_PathElementMap_Get mergedRHS_ptr MG el kl $$ [HMGo] as %x3 %ok3 ⟨HMGo, %Hok3⟩
          · iframe; iframe #
          have hok3 : ok3 = decide (kl ∈ mg) := by
            have h3 := HMG kl
            cases hm : MG kl with
            | none =>
              rw [hm] at Hok3 h3
              rw [Hok3.2]
              have : kl ∉ mg := fun h => by have := h3.2 h; cases this
              simp [this]
            | some y =>
              rw [hm] at Hok3 h3
              rw [Hok3.2]
              simp [h3.1 rfl]
          subst hok3
          iunfold ownPEMap at HMGo
          icases HMGo with ⟨%mv', mergedRHS, Hmv⟩
          by_cases hmg : kl ∈ mg
          · rw [decide_eq_true hmg]
            wp_auto
            iframe; iright; iframe; ipureintro
            refine ⟨rfl, by word, by word, ?_, ?_⟩
            · rw [hln, hdL]; simp [LawBL2.nextL, hmg]
            · intro l L' h; rw [hdL, List.cons.injEq] at h; obtain ⟨rfl, -⟩ := h; simp [hin]
          · rw [decide_eq_false hmg]
            wp_auto
            iframe; iright; iframe; ipureintro
            refine ⟨rfl, HlI0, HlIL, ?_, ?_⟩
            · rw [hdL]; simp [LawBL2.nextL, hmg]
            · intro l L' h; rw [hdL, List.cons.injEq] at h; obtain ⟨rfl, -⟩ := h; simp [hin]
        · rw [decide_eq_false hin]
          wp_auto
          have hlsne : ls ≠ [] := by intro h; rw [h] at hxl; simp at hxl
          rcases hol : ol with _ | vsl
          · exfalso; rw [hol] at hls; exact hlsne hls.symm
          rw [hol] at hls
          simp only [Option.getD_some] at hls
          iunfold isListO at HlO
          icases LawBL2.isListV_dispatchU h_listUnstructured_Length h_listUnstructured_Length_ptr
            h_listUnstructured_AtUsing h_listUnstructured_AtUsing_ptr ll vsl $$ [] with ⟨%li, %Hli, -, #HAt⟩
          · iframe #; iPkgInit
          subst Hli
          iunfold mwOwn at Hown
          icases Hown with ⟨%ps2, Hcore, Hp, Hsp, Ha⟩
          iunfold mwCore at Hcore
          icases Hcore with ⟨%tr2, %rule2, %o2, Hw, #Htr2, #Hsc2, %Hwf2, #Hrule2, #Ho2⟩
          wp_auto
          wp_apply HAt $$ %st.alloc %lI %xl [Ha] as %lv ⟨Ha, Hlv⟩
          · iframe; ipureintro; exact ⟨HlI0, by rw [hls]; exact hxl⟩
          try wp_auto
          ihave Hown : mwOwn w sc S st spj $$ [Hw Hp Hsp Ha]
          · unfold mwOwn mwCore; iexists ps2; iframe; iframe #; ipureintro; exact Hwf2
          wp_apply HML $$ %w %sc %S %st %tp %e %ElemRel.associative %ks %el %kl %lv %GoInterface.nil
              %(DFrac.own 1) %DFrac.discard %(some xl) %none %spj [Hown Hlv]
            as %o %errs ⟨⟨%spj', Hown, %Hspj'⟩, #Ho, Herrs, -, -⟩
          · iframe; iframe #
            simp only [isValO]
            iframe
            ipureintro
            exact ⟨trivial, Or.inl rfl, hcl, trivial, Hleaf⟩
          have hmi : LawBL2.mItem S e ks ls rs kl = mergeO S e (some xl) none := by
            unfold LawBL2.mItem; rw [hil, LawBL2.itemOf_none ks rs kl (by rw [hRdef]; exact hin)]
          iunfold noErrs at Herrs
          iunfold ownErrs at Herrs
          icases Herrs with ⟨Herrs, Herrc⟩
          imod ownSlice_persist _ _ _ $$ Herrs with #Herrs
          wp_apply (wp_slice_append_dfrac (V := typed.ValidationError) errs [] DFrac.discard errs [] DFrac.discard)
            $$ [Herrc] as %e3 -
          · iframe; iframe #; ipureintro; exact DFrac.valid_discard
          try wp_auto
          wp_join iprop(∃ (osl' : GoSlice) (xs' : List GoInterface), out_ptr ↦ osl' ∗ osl' ↦* xs' ∗
              ownSliceCap GoInterface osl' (DFrac.own 1) ∗
              (□ ∀ q : GoInterface × UVal,
                ⌜q ∈ xs'.zip ((done ++ [kl]).filterMap (LawBL2.mItem S e ks ls rs))⌝ -∗ isIface q.1 q.2) ∗
              ⌜xs'.length = ((done ++ [kl]).filterMap (LawBL2.mItem S e ks ls rs)).length⌝)
            at (If _ _ _) with [out Hosl Hocap mergeOut] as ⟨%osl', %xs', out, Hosl, Hocap, #Hxs', %Hxsl'⟩
          · rw [LawBL2.fm_snoc, hmi]
            rcases hm : mergeO S e (some xl) none with _ | x
            · simp only [outRep]
              icases Ho with %ho
              subst ho
              wp_auto
              wp_join_done
              iexists osl, xs
              simp only [Option.toList, List.append_nil]
              iframe; iframe #
              ipureintro; exact Hxsl
            · simp only [outRep]
              icases Ho with ⟨%i, #Hoi, #Hix⟩
              ihave %Hon := typedPointsto_not_null _ _ _ $$ Hoi
              rw [decide_eq_false Hon]
              wp_auto
              wp_apply (wp_slice_literal (V := GoInterface) [i])
              isplitr
              · ipureintro; rfl
              iintro %sl2 ⟨Hsl2, -⟩
              try wp_auto
              wp_apply (wp_slice_append (V := GoInterface) osl _ _ [i] (DFrac.own 1))
                $$ [Hosl Hocap Hsl2] as %osl2 ⟨Hosl2, Hocap2, -⟩
              · iframe
              try wp_auto
              wp_join_done
              iexists osl2, xs ++ [i]
              iframe
              simp only [Option.toList]
              isplitr
              · imodintro; iintro %q %hq
                rcases LawBL2.zip_snoc_mem _ _ Hxsl _ _ q hq with h | h
                · iapply Hxs; ipureintro; exact h
                · subst h; iexact Hix
              ipureintro; simp [Hxsl]
          iframe
          ileft
          isplitr
          · ipureintro; rfl
          iexists done ++ [kl], sh, mg, sps, osl', xs', spj'
          iframe
          iframe #
          ipureintro
          refine ⟨Hsh, HMG, HMGR, Hxsl', ?_, by word, by word, HrI0, HrIR, ?_⟩
          · intro h
            have h1 := Hspj h
            rw [Hspj' (by rw [h1]; exact h), h1]
          · rw [hln]
            rw [hdL] at HMI
            refine LawBL2.MInv_left (by simp [hin]) ?_ HMI
            intro h
            exact hin (List.mem_of_mem_drop (List.mem_of_mem_head? h))
      · iframe; iright; iframe; ipureintro
        have hLd : L.drop (sint.nat lI) = [] := LawBL2.drop_nil _ _ (by word)
        refine ⟨trivial, HlI0, HlIL, by rw [hLd]; rfl, fun l L' h => by rw [hLd] at h; cases h⟩
    iintro ⟨lhsPEs, rhsPEs, lLen, rLen, w, t, lhs, Hc2⟩
    icases Hc2 with (⟨%Hv, HI2⟩ | ⟨%lI', %mvx, ⟨%Hv, %HlI'0, %HlI'L, %HdL', %HinR⟩, lI, rI, nextShared, sharedOrder,
      mergedRHS, Hmv, out, Hosl, Hocap, Hown, HOL, HOR⟩)
    · subst Hv
      wp_auto
      wp_for_post
      iframe
    subst Hv
    wp_auto
    wp_if_destruct
    · -- a right key
      have hrR : sint.nat rI < R.length := by word
      obtain ⟨er, her⟩ : ∃ x, esR[sint.nat rI]? = some x :=
        ⟨_, List.getElem?_eq_getElem (by rw [HpRl]; exact hrR)⟩
      obtain ⟨kr, hkr⟩ : ∃ x, R[sint.nat rI]? = some x := ⟨_, List.getElem?_eq_getElem hrR⟩
      ihave #Hper := HpRat $$ %(sint.nat rI) %er %kr %(And.intro her hkr)
      ihave ⟨#Helr, -⟩ := ownSlice_elem_acc (sint.Z rI) er rpes DFrac.discard esR HrI0
        (by rw [show (sint.Z rI).toNat = sint.nat rI from rfl]; exact her) $$ HesR
      have hbr : (0 ≤ sint.Z rI ∧ sint.Z rI < sint.Z rpes.len) := ⟨HrI0, by word⟩
      have hdR := LawBL2.drop_cons R (sint.nat rI) kr hkr
      have hrn : sint.nat (rI + W64 1) = sint.nat rI + 1 := by have := HesRl.2; word
      obtain ⟨xr, hxr⟩ : ∃ x, rs[sint.nat rI]? = some x :=
        ⟨_, List.getElem?_eq_getElem (by rw [← hkR.1]; exact hrR)⟩
      have hkxr : keyOf ks xr = some kr := by rw [← hkR.2 _ _ hxr, hkr]
      have hir : itemOf ks rs kr = some xr :=
        LawBL2.itemOf_at ks rs (fun v hv => (hallR v hv).2) (by rw [hRdef]; exact hndR) _ _ _ hxr hkxr
      have hcr : conforms S e xr := (hallR xr (List.mem_of_getElem? hxr)).1
      have hcl : confO S e (itemOf ks ls kr) := by
        cases h : itemOf ks ls kr with
        | none => trivial
        | some x => exact (hallL x (LawBL2.itemOf_mem h)).1
      ihave ⟨%vr, %Hvr, #Hvr⟩ := LawBL2.itemMap_some _ _ kr xr hir $$ HMRp
      ihave #Hvl := LawBL2.itemMap_valO _ _ kr $$ HMLp
      simp only [hbr, and_self, ↓reduceIte]
      wp_auto
      ihave HMGo : ownPEMap mergedRHS_ptr MG $$ [mergedRHS Hmv]
      · unfold ownPEMap; iexists _; iframe
      wp_apply h_PathElementMap_Insert mergedRHS_ptr MG er kr _ $$ [HMGo] as HMGo
      · iframe; iframe #; ipureintro
        apply LawBL2.peMap_cardLt MG (R.take (sint.nat rI)) _ (fun k hk => HMGR k ((HMG k).1 hk))
        rw [List.length_take]; have := HesRl.2; word
      try wp_auto
      wp_apply h_PathElementValueMap_Get observedLHS_ptr ML er kr $$ [HOL] as %x1 %ok1 ⟨HOL, %Hok1⟩
      · iframe; iframe #
      have hx1 : x1 = (ML kr).getD interface.nil := by
        cases h : ML kr with
        | none => rw [h] at Hok1; exact Hok1.1
        | some y => rw [h] at Hok1; exact Hok1.1
      rw [hx1]
      try wp_auto
      wp_apply h_PathElementValueMap_Get observedRHS_ptr MR er kr $$ [HOR] as %x2 %ok2 ⟨HOR, %Hok2⟩
      · iframe; iframe #
      rw [Hvr] at Hok2
      obtain ⟨hx2, rfl⟩ := Hok2
      rw [hx2]
      try wp_auto
      wp_apply HML $$ %w %sc %S %st %tp %e %ElemRel.associative %ks %er %kr %((ML kr).getD interface.nil) %vr
          %DFrac.discard %DFrac.discard %(itemOf ks ls kr) %(some xr) %spj [Hown]
        as %o %errs ⟨⟨%spj', Hown, %Hspj'⟩, #Ho, Herrs, -, -⟩
      · iframe; iframe #
        simp only [isValO]
        iframe #
        ipureintro
        exact ⟨Or.inr rfl, hcl, hcr, Hleaf⟩
      have hmi : LawBL2.mItem S e ks ls rs kr = mergeO S e (itemOf ks ls kr) (some xr) := by
        unfold LawBL2.mItem; rw [hir]
      iunfold noErrs at Herrs
      iunfold ownErrs at Herrs
      icases Herrs with ⟨Herrs, Herrc⟩
      imod ownSlice_persist _ _ _ $$ Herrs with #Herrs
      wp_apply (wp_slice_append_dfrac (V := typed.ValidationError) errs [] DFrac.discard errs [] DFrac.discard)
        $$ [Herrc] as %e3 -
      · iframe; iframe #; ipureintro; exact DFrac.valid_discard
      try wp_auto
      wp_join iprop(∃ (osl' : GoSlice) (xs' : List GoInterface), out_ptr ↦ osl' ∗ osl' ↦* xs' ∗
          ownSliceCap GoInterface osl' (DFrac.own 1) ∗
          (□ ∀ q : GoInterface × UVal,
            ⌜q ∈ xs'.zip ((done ++ [kr]).filterMap (LawBL2.mItem S e ks ls rs))⌝ -∗ isIface q.1 q.2) ∗
          ⌜xs'.length = ((done ++ [kr]).filterMap (LawBL2.mItem S e ks ls rs)).length⌝)
        at (If _ _ _) with [out Hosl Hocap mergeOut] as ⟨%osl', %xs', out, Hosl, Hocap, #Hxs', %Hxsl'⟩
      · rw [LawBL2.fm_snoc, hmi]
        rcases hm : mergeO S e (itemOf ks ls kr) (some xr) with _ | x
        · simp only [outRep]
          icases Ho with %ho
          subst ho
          wp_auto
          wp_join_done
          iexists osl, xs
          simp only [Option.toList, List.append_nil]
          iframe; iframe #
          ipureintro; exact Hxsl
        · simp only [outRep]
          icases Ho with ⟨%i, #Hoi, #Hix⟩
          ihave %Hon := typedPointsto_not_null _ _ _ $$ Hoi
          rw [decide_eq_false Hon]
          wp_auto
          wp_apply (wp_slice_literal (V := GoInterface) [i])
          isplitr
          · ipureintro; rfl
          iintro %sl2 ⟨Hsl2, -⟩
          try wp_auto
          wp_apply (wp_slice_append (V := GoInterface) osl _ _ [i] (DFrac.own 1))
            $$ [Hosl Hocap Hsl2] as %osl2 ⟨Hosl2, Hocap2, -⟩
          · iframe
          try wp_auto
          wp_join_done
          iexists osl2, xs ++ [i]
          iframe
          simp only [Option.toList]
          isplitr
          · imodintro; iintro %q %hq
            rcases LawBL2.zip_snoc_mem _ _ Hxsl _ _ q hq with h | h
            · iapply Hxs; ipureintro; exact h
            · subst h; iexact Hix
          ipureintro; simp [Hxsl]
      wp_join iprop(∃ (nsp' : Loc) (sps' : List Loc) (so'' : GoSlice), nextShared_ptr ↦ nsp' ∗
          sharedOrder_ptr ↦ so'' ∗ so'' ↦*□ sps' ∗
          ⌜LawBL2.shRep (GF := GF) R rpes nsp' sps' (if sh.head? = some kr then sh.tail else sh)⌝)
        at (If _ _ _) with [nextShared sharedOrder pe] as ⟨%nsp2, %sps2, %so2, nextShared, sharedOrder, #Hso2, %Hsh2⟩
      · rcases LawBL2.shRep_head Hsh with ⟨hnull, hsh⟩ | ⟨i, hi, hnsp, hsh⟩
        · subst hnull
          wp_auto
          wp_join_done
          iexists _, _, _
          iframe
          isplitr
          · iexact Hso'
          ipureintro
          subst hsh
          simpa using Hsh
        · subst hnsp
          obtain ⟨es, hes⟩ : ∃ x, esR[i]? = some x :=
            ⟨_, List.getElem?_eq_getElem (by rw [HpRl]; exact hi)⟩
          ihave #Hpes := HpRat $$ %i %es %(R[i]) %(And.intro hes (List.getElem?_eq_getElem hi))
          ihave ⟨#Hesi, -⟩ := ownSlice_elem_acc ((i : Nat) : Int) es rpes DFrac.discard esR (by omega)
            (by simpa using hes) $$ HesR
          ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hesi
          rw [decide_eq_false Hnn]
          wp_auto
          wp_method_call; wp_call; wp_auto
          wp_apply h_PathElement_Equals es er R[i] kr $$ [] as %beq3 %Hbeq3
          · iframe #
          cases beq3
          · have hne3 : R[i] ≠ kr := fun h => by simpa using Hbeq3.2 h
            wp_auto
            wp_join_done
            iexists _, _, _
            iframe
            isplitr
            · iexact Hso'
            ipureintro
            rw [if_neg (by rw [hsh, List.getElem?_eq_getElem hi]; simpa using hne3)]
            exact Hsh
          · have heq3 : R[i] = kr := Hbeq3.1 rfl
            wp_auto
            ihave %Hso'l := ownSlice_len _ _ _ $$ Hso'
            ihave %Hso'wf := ownSlice_wf _ _ _ $$ Hso'
            wp_join iprop(∃ (nsp' : Loc) (sps' : List Loc) (so'' : GoSlice), nextShared_ptr ↦ nsp' ∗
                sharedOrder_ptr ↦ so'' ∗ so'' ↦*□ sps' ∗ ⌜LawBL2.shRep (GF := GF) R rpes nsp' sps' sh.tail⌝)
              at (If _ _ _) with [nextShared sharedOrder] as ⟨%nsp', %sps', %so'', nextShared, sharedOrder, #Hso'', %Hsh'⟩
            · rcases sps with _ | ⟨p, ps⟩
              · have h0 : so'.len = W64 0 := by simp at Hso'l; word
                rw [h0]
                wp_auto
                wp_join_done
                iexists _, [], _
                iframe
                isplitr
                · iexact Hso'
                ipureintro; exact LawBL2.shRep_pop_nil Hsh
              · have hpos : decide (sint.Z (W64 0) < sint.Z so'.len) = true := by
                  simp at Hso'l; simp only [decide_eq_true_eq]; have := Hso'l.1; have := Hso'l.2; word
                rw [hpos]
                wp_auto
                have hb0 : (0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z so'.len) := by
                  simp at Hso'l; refine ⟨by decide, ?_⟩; have := Hso'l.1; have := Hso'l.2; word
                simp only [hb0, and_self, ↓reduceIte]
                wp_apply (wp_load_slice_index (V := Loc) so' (sint.Z (W64 0)) _ DFrac.discard p (by decide)) $$ [Hso'] as -
                · iframe #; ipureintro; rfl
                try wp_auto
                have hb2 : (0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) ≤ sint.Z so'.len ∧ sint.Z so'.len ≤ sint.Z so'.cap) := by
                  simp at Hso'l; refine ⟨by decide, ?_, Hso'wf.2⟩; have := Hso'l.1; have := Hso'l.2; word
                simp only [hb2, and_self, ↓reduceIte]
                wp_auto
                ihave #Hso2 := LawBL2.ownSlice_tail_pers so' _ _ $$ Hso'
                wp_join_done
                iexists _, _, _
                iframe
                isplitr
                · iexact Hso2
                ipureintro; exact LawBL2.shRep_pop_cons Hsh
            wp_join_done
            iexists _, _, _
            iframe
            isplitr
            · iexact Hso''
            ipureintro
            rw [if_pos (by rw [hsh, List.getElem?_eq_getElem hi, heq3])]
            exact Hsh'
      wp_for_post
      iunfold ownPEMap at HMGo
      icases HMGo with ⟨%mv', mergedRHS, Hmv⟩
      iframe
      iexists lI', (rI + W64 1), done ++ [kr], (if sh.head? = some kr then sh.tail else sh), kr :: mg, _, mv',
        nsp2, sps2, so2, osl', xs', spj'
      iframe
      iframe #
      ipureintro
      refine ⟨Hsh2, ?_, ?_, Hxsl', ?_, HlI'0, HlI'L, by word, by word, ?_⟩
      · intro k
        simp only [PEMap.insert, List.mem_cons]
        by_cases hk : k = kr
        · simp [hk]
        · simp [hk, HMG]
      · intro k hk
        rw [hrn, List.take_add_one, hkr]
        rcases List.mem_cons.1 hk with rfl | hk
        · simp
        · exact List.mem_append_left _ (HMGR k hk)
      · intro h
        have h1 := Hspj h
        rw [Hspj' (by rw [h1]; exact h), h1]
      · rw [hrn, HdL']
        rw [hdR] at HMI
        refine LawBL2.MInv_right ?_ HMI
        intro l L' h
        obtain ⟨h1, h2⟩ := HP1 l L' kr _ h hdR
        exact ⟨HinR l L' h, h1, h2⟩
    · have hRd : R.drop (sint.nat rI) = [] := LawBL2.drop_nil _ _ (by word)
      wp_for_post
      iframe
      iexists lI', rI, done, sh, mg, MG, mvx, nsp, sps, so', osl, xs, spj
      iframe
      iframe #
      ipureintro
      refine ⟨Hsh, HMG, HMGR, Hxsl, Hspj, HlI'0, HlI'L, HrI0, HrIR, ?_⟩
      rw [HdL', hRd]
      rw [hRd] at HMI
      exact LawBL2.MInv_nextL_nil HinR HMI
  · simp only [hcond, decide_false]
    rw [if_neg (by simp [false_neq_true])]
    rw [if_pos (by simp)]
    have hLd : L.drop (sint.nat lI) = [] := LawBL2.drop_nil _ _ (by omega)
    have hRd : R.drop (sint.nat rI) = [] := LawBL2.drop_nil _ _ (by omega)
    rw [hLd, hRd] at HMI
    have hdone := LawBL2.MInv_done HMI
    subst hdone
    have hout := LawBL2.mergeListOut_eq S e ks ls rs
    rw [hLdef, hRdef] at hout
    rw [hout]
    ihave %Hoslen := ownSlice_len _ _ _ $$ Hosl
    iunfold mwOwn at Hown
    icases Hown with ⟨%ps2, Hcore, Hp, Hsp, Ha⟩
    iunfold mwCore at Hcore
    icases Hcore with ⟨%tr2, %rule2, %o2, Hw, #Htr2, -, -, #Hrule2, #Ho2⟩
    rw [Hout]
    simp only [outRep]
    icases Ho2 with %ho2
    subst ho2
    cases hE : ((mergeKeys L R).filterMap (LawBL2.mItem S e ks ls rs)).isEmpty
    · have hpos : decide (sint.Z osl.len > sint.Z (W64 0)) = true := by
        have : xs.length ≠ 0 := by
          rw [Hxsl]; intro h; rw [List.length_eq_zero_iff] at h; rw [h] at hE; cases hE
        simp only [decide_eq_true_eq]; have := Hoslen.1; have := Hoslen.2; word
      wp_auto
      rw [hpos]
      imod ownSlice_persist _ _ _ $$ Hosl with #Hosl
      iapply wp_fupd
      wp_auto
      ipersist i
      imodintro
      simp only [Bool.false_eq_true, ↓reduceIte]
      iapply HΦ
      isplitl [Herrs2s Herrs2c]
      · unfold noErrs ownErrs; iframe
      iexists spj
      isplitl
      · unfold mwOwn mwCore
        iexists ps2
        iframe
        iframe #
        simp only [outRep]
        isplitr
        · ipureintro; exact Hwf
        iexists _
        isplitr
        · iexact i
        iapply isIface_list_law_holds osl xs _ Hxsl $$ Hosl
        iapply LawA3.sepL_of_forall
        iexact Hxs
      ipureintro; exact Hspj
    · have hpos : decide (sint.Z osl.len > sint.Z (W64 0)) = false := by
        have : xs.length = 0 := by
          rw [Hxsl]; rw [List.length_eq_zero_iff]; exact List.isEmpty_iff.1 hE
        simp only [decide_eq_false_iff_not]; have := Hoslen.1; have := Hoslen.2; word
      wp_auto
      rw [hpos]
      wp_auto
      simp only [↓reduceIte]
      iapply HΦ
      isplitl [Herrs2s Herrs2c]
      · unfold noErrs ownErrs; iframe
      iexists spj
      isplitl
      · have hst : MWSt.mk st.lhs st.rhs st.t st.path none st.inLeaf st.alloc = st := by
          rw [← Hout]
        rw [hst]
        unfold mwOwn mwCore
        iexists ps2
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
