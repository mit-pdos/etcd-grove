/-
`typed.compareWalker.visitListItems`: a member of the recursion cluster `typed.compareWalkerRec` (`compareWalkerRec.lean`); its proof is the
projection of the cluster's (its body is `compareWalker__visitListItemsBody.lean`).

The proof: both sides' `Length` (a nil side has none), then three loops. The first indexes the left
items by key in `lValues` (`LawBL2C.slMapRep`: each key's one-element `[]value.Value`), appending
each key to `allPEs`; the keys are distinct (conformance), so `Get` never finds one and the
duplicate branch is not taken. The second does the same for the right side, appending the keys the
left lacks. The third walks `allPEs` (`L ++ R.filter (· ∉ L)`, `cmpListOut`'s order), takes each
key's items (`LawBL2C.slotRep`), always in the one-to-one case of the `switch` (both lists at most
one long, not both empty), and compares them in a child walker (`compareListItem`), the
comparison growing by one key at a time (`LawBL2C.unionAll_snoc`, bounded by `cardLt_keys`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker__visitListItemsBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.MakePathElementMap
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElementMap__Get
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElementMap__Insert
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__Insert
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructured__At
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructured__At_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructured__Length
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructured__Length_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.listItemToPathElement
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.Equals
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsA
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsA2
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsA3
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsBPers
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsBList2C
public import Proof.sigs_k8s_io.structured_merge_diff.v7.schema.LawProofs
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.LawProofsDispatch
public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsRep

@[expose] public section

set_option linter.iris.style.nameCheck false

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

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 8192 in
theorem typed.compareWalker.visitListItems.wp_proofBody
    (h_MakePathElementMap : fieldpath.MakePathElementMap.spec (GF := GF))
    (h_PathElementMap_Get : fieldpath.PathElementMap.Get.spec (GF := GF))
    (h_PathElementMap_Insert : fieldpath.PathElementMap.Insert.spec (GF := GF))
    (h_Set_Insert : fieldpath.Set.Insert.spec (GF := GF))
    (h_listUnstructured_At : value.listUnstructured.At.spec (GF := GF))
    (h_listUnstructured_At_ptr : value.listUnstructured.At_ptr.spec (GF := GF))
    (h_listUnstructured_Length : value.listUnstructured.Length.spec (GF := GF))
    (h_listUnstructured_Length_ptr : value.listUnstructured.Length_ptr.spec (GF := GF))
    (h_listItemToPathElement : typed.listItemToPathElement.spec (GF := GF))
    (h_Equals : value.Equals.spec (GF := GF)) :
    typed.compareWalker.visitListItems.specBody (GF := GF) := by
  unfold typed.compareWalker.visitListItems.specBody typed.compareWalkerRec.specI
    typed.compareWalker.compare.specI typed.compareWalker.compareListItem.specI
    typed.compareWalker.doList.specI typed.compareWalker.doMap.specI
    typed.compareWalker.visitListItems.specI typed.compareWalker.visitMapItem.specI
    typed.compareWalker.visitMapItems.specI
  iintro #IH
  iintro %w %sc %S %st %c %C %tp %e %ks %ll %rl %ol %or_ %sp
  wp_start as ⟨Hown, #Hlr, Hl, Hr, %Hpre⟩
  icases IH with ⟨-, #HcLI, -, -, -, -, -⟩
  obtain ⟨Hfind, Hleaf, Hcl, Hcr, Hcard⟩ := Hpre
  iunfold cwOwn at Hown
  icases Hown with ⟨%ps, Hcore, Hp, Hsp, Ha, Hcmp⟩
  iunfold cwCore at Hcore
  icases Hcore with ⟨%tr, Hw, #Htr, #Hsc, %Hwf⟩
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
  rw [hls, hrs] at Hcard
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
      icases LawA3.isListV_dispatchL h_listUnstructured_Length h_listUnstructured_Length_ptr
        h_listUnstructured_At h_listUnstructured_At_ptr rl vsr $$ [] with ⟨%ri, %Hri, #HLenR, -⟩
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
      icases LawA3.isListV_dispatchL h_listUnstructured_Length h_listUnstructured_Length_ptr
        h_listUnstructured_At h_listUnstructured_At_ptr ll vsl $$ [] with ⟨%li, %Hli, #HLenL, -⟩
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
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ lLen_ptr ↦ nl ∗
      ∃ x : w64, maxLength_ptr ↦ x ∗ ⌜0 ≤ sint.Z x⌝))) $$ [maxLength lLen]
  · wp_if_destruct
    all_goals
      try wp_auto
      isplitr; · ipureintro; first | rfl | trivial
      iframe; ipureintro
      first | (show 0 ≤ BitVec.toInt nr; omega) | (show 0 ≤ BitVec.toInt nl; omega)
  iintro %v ⟨%hv, lLen, %ml0, maxLength, %Hml0⟩
  subst hv
  wp_auto
  wp_apply (wp_slice_make3 (V := fieldpath.PathElement) (W64 0) ml0 ⟨by decide, Hml0⟩) as %asl0 ⟨Hasl0, Hacap0, -⟩
  try wp_auto
  wp_apply h_MakePathElementMap nl $$ [] as %lv0 Hlv0
  · iframe #; ipureintro; show 0 ≤ BitVec.toInt nl; omega
  try wp_auto
  -- the keys of both sides
  obtain ⟨hallL, hndL⟩ := hsideL
  obtain ⟨hallR, hndR⟩ := hsideR
  rw [hls] at hallL hndL
  rw [hrs] at hallR hndR
  have hkL := LawBL2.keysOf_get ks ls (fun v hv => (hallL v hv).2)
  have hkR := LawBL2.keysOf_get ks rs (fun v hv => (hallR v hv).2)
  have htkL := LawBL2C.keysOf_take ks ls (fun v hv => (hallL v hv).2)
  have htkR := LawBL2C.keysOf_take ks rs (fun v hv => (hallR v hv).2)
  obtain ⟨L, hLdef⟩ : ∃ L, keysOf ks ls = L := ⟨_, rfl⟩
  obtain ⟨R, hRdef⟩ : ∃ R, keysOf ks rs = R := ⟨_, rfl⟩
  rw [hLdef] at hkL hndL htkL
  rw [hRdef] at hkR hndR htkR
  have hlen63 : ls.length < 2 ^ 63 := by have := nl.toInt_lt; omega
  have hlen63r : rs.length < 2 ^ 63 := by have := nr.toInt_lt; omega
  -- the first loop: the left side's items by key
  ihave HI1 : (∃ (j : w64) (lv : fieldpath.PathElementMap) (ML : PEMap GoInterface) (asl : GoSlice)
      (es : List fieldpath.PathElement),
      "i" ∷ i_ptr ↦ j ∗ "lValues" ∷ lValues_ptr ↦ lv ∗ "Hlv" ∷ ownPEMapV lv ML ∗
      "#HML" ∷ □ LawBL2C.slMapRep (itemOf ks (ls.take (sint.nat j))) ML ∗
      "allPEs" ∷ allPEs_ptr ↦ asl ∗ "Hasl" ∷ asl ↦* es ∗
      "Hacap" ∷ ownSliceCap fieldpath.PathElement asl (DFrac.own 1) ∗
      "#Hes" ∷ □ isPEs es (L.take (sint.nat j)) ∗
      "%HMLs" ∷ ⌜∀ k, (ML k).isSome ↔ k ∈ L.take (sint.nat j)⌝ ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ ls.length⌝ : IProp GF)
    $$ [i lValues Hlv0 allPEs Hasl0 Hacap0]
  · iexists _, _, _, _, []
    iframe
    have h0 : itemOf ks (ls.take (sint.nat (W64 0))) = fun _ => none := by
      funext k; rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero]; simp [itemOf]
    rw [h0]
    simp only [List.replicate_zero]
    isplitr
    · imodintro; iapply LawBL2C.slMapRep_empty
    isplitl [Hasl0]
    · iexact Hasl0
    isplitr
    · imodintro
      simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero]
      iapply (show iprop(True) ⊢ isPEs (GF := GF) [] [] from isPEs_nil_law_holds)
      ipureintro; trivial
    isplitr
    · ipureintro; intro k; rw [show sint.nat (W64 0) = 0 from rfl]; simp [PEMap.empty]
    ipureintro; exact ⟨by decide, by simp⟩
  wp_for HI1
  wp_if_destruct
  · have hjl : sint.nat j < ls.length := by
      have : sint.Z j < sint.Z nl := Hif
      have h2 : sint.Z nl = ls.length := Hnl
      have := Hj.1; word
    have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
    obtain ⟨x, hx⟩ : ∃ x, ls[sint.nat j]? = some x := ⟨_, List.getElem?_eq_getElem hjl⟩
    have hxin : x ∈ ls := List.mem_of_getElem? hx
    have hcx : conforms S e x := (hallL x hxin).1
    obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 (show (keyOf ks x).isSome from (hallL x hxin).2)
    have hLk : L[sint.nat j]? = some k := by rw [hkL.2 _ _ hx, hk]
    rcases hol : ol with _ | vsl
    · exfalso; rw [hol] at hls; simp at hls; subst hls; simp at hjl
    rw [hol] at hls
    simp only [Option.getD_some] at hls
    iunfold isListO at HlO
    icases LawA3.isListV_dispatchL h_listUnstructured_Length h_listUnstructured_Length_ptr
      h_listUnstructured_At h_listUnstructured_At_ptr ll vsl $$ [] with ⟨%li, %Hli, -, #HAtL⟩
    · iframe #; iPkgInit
    subst Hli
    wp_auto
    wp_apply HAtL $$ %j %x as %child Hch
    · ipureintro; exact ⟨Hj.1, by rw [hls]; exact hx⟩
    try wp_auto
    wp_apply h_listItemToPathElement st.alloc sc S tp e ks fs em rel' child (DFrac.own 1) x st.t.name
      $$ [Ha Hch] as %pe1 %err Hpost
    · iframe; iframe #; ipureintro; exact ⟨Hwf, hkne, hfe, Hfind, hcx, by rw [hk]; rfl⟩
    rw [hk]
    icases Hpost with ⟨Ha, Hch, %herr, #Hpe1⟩
    subst herr
    try wp_auto
    have hkfresh : k ∉ L.take (sint.nat j) := by
      rw [← htkL]; exact LawA2.keyOf_fresh ks ls _ x k (by rw [hLdef]; exact hndL) hx hk
    have hMLk : ML k = none := by
      cases h : ML k with
      | none => rfl
      | some _ => exact absurd ((HMLs k).1 (by rw [h]; rfl)) hkfresh
    ihave HMo : ownPEMap lValues_ptr ML $$ [lValues Hlv]
    · unfold ownPEMap; iexists _; iframe
    wp_apply h_PathElementMap_Get lValues_ptr ML pe1 k $$ [HMo] as %x1 %ok1 ⟨HMo, %Hok1⟩
    · iframe; iframe #
    rw [hMLk] at Hok1
    obtain ⟨-, rfl⟩ := Hok1
    wp_auto
    imod isValF_persist_law_holds _ _ _ $$ Hch with #Hch
    wp_apply (wp_slice_literal (V := value.Value) [child])
    isplitr
    · ipureintro; rfl
    iintro %sl2 ⟨Hsl2, -⟩
    imod ownSlice_persist _ _ _ $$ Hsl2 with #Hsl2
    try wp_auto
    wp_apply h_PathElementMap_Insert lValues_ptr ML pe1 k _ $$ [HMo] as HMo
    · iframe; iframe #; ipureintro
      refine LawBL2.peMap_cardLt ML (L.take (sint.nat j)) _ (fun k' hk' => (HMLs k').1 hk') ?_
      have := List.length_take_le (sint.nat j) L
      omega
    try wp_auto
    wp_apply (wp_slice_literal (V := fieldpath.PathElement) [pe1])
    isplitr
    · ipureintro; rfl
    iintro %sl3 ⟨Hsl3, -⟩
    try wp_auto
    wp_apply (wp_slice_append (V := fieldpath.PathElement) asl _ _ [pe1] (DFrac.own 1))
      $$ [Hasl Hacap Hsl3] as %asl' ⟨Hasl', Hacap', -⟩
    · iframe
    try wp_auto
    wp_for_post
    iunfold ownPEMap at HMo
    icases HMo with ⟨%lv', lValues, Hlv⟩
    iframe
    have htk : L.take (sint.nat j + 1) = L.take (sint.nat j) ++ [k] := by
      rw [List.take_add_one, hLk]; rfl
    iexists (j + W64 1), _, _, asl', es ++ [pe1]
    rw [hj1, htk]
    iframe
    isplitr
    · imodintro
      iapply LawBL2C.slMapRep_insert _ _ ML k x _ child
        (LawBL2.itemOf_take_succ_eq ks ls _ x k hx hk (by rw [htkL]; exact hkfresh))
        (fun k' h => LawBL2.itemOf_take_succ_ne ks ls _ x k k' hx hk h)
      iframe #
    isplitr
    · imodintro
      iapply LawBL2C.isPEs_snoc
      iframe #
    ipureintro
    refine ⟨?_, by word, by word⟩
    intro k'
    simp only [PEMap.insert, List.mem_append, List.mem_singleton]
    by_cases h : k' = k
    · simp [h]
    · simp [h, HMLs k']
  · have hjL : sint.nat j = ls.length := by
      have : ¬ sint.Z j < sint.Z nl := Hif
      have h2 : sint.Z nl = ls.length := Hnl
      have := Hj.2; have := Hj.1; word
    have hLL : L.take ls.length = L := by rw [← hkL.1]; exact List.take_length
    rw [hjL, hLL] at HMLs
    rw [hjL, List.take_length, hLL]
    ihave HLo : ownPEMap lValues_ptr ML $$ [lValues Hlv]
    · unfold ownPEMap; iexists _; iframe
    wp_apply h_MakePathElementMap nr $$ [] as %rv0 Hrv0
    · iframe #; ipureintro; show 0 ≤ BitVec.toInt nr; omega
    try wp_auto
    -- the second loop: the right side's items by key, its new keys
    ihave HI2 : (∃ (j : w64) (rv : fieldpath.PathElementMap) (MR : PEMap GoInterface) (asl : GoSlice)
        (es : List fieldpath.PathElement),
        "i" ∷ i_ptr ↦ j ∗ "rValues" ∷ rValues_ptr ↦ rv ∗ "Hrv" ∷ ownPEMapV rv MR ∗
        "#HMR" ∷ □ LawBL2C.slMapRep (itemOf ks (rs.take (sint.nat j))) MR ∗
        "allPEs" ∷ allPEs_ptr ↦ asl ∗ "Hasl" ∷ asl ↦* es ∗
        "Hacap" ∷ ownSliceCap fieldpath.PathElement asl (DFrac.own 1) ∗
        "#Hes" ∷ □ isPEs es (L ++ (R.take (sint.nat j)).filter (fun x => decide (x ∉ L))) ∗
        "%HMRs" ∷ ⌜∀ k, (MR k).isSome ↔ k ∈ R.take (sint.nat j)⌝ ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ rs.length⌝ : IProp GF)
      $$ [i rValues Hrv0 allPEs Hasl Hacap]
    · iexists _, _, _, _, es
      iframe
      have h0 : itemOf ks (rs.take (sint.nat (W64 0))) = fun _ => none := by
        funext k; rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero]; simp [itemOf]
      rw [h0]
      isplitr
      · imodintro; iapply LawBL2C.slMapRep_empty
      rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero]
      simp only [List.filter_nil, List.append_nil]
      isplitr
      · iexact Hes
      ipureintro
      exact ⟨fun k => by simp [PEMap.empty], by decide, by simp⟩
    wp_for HI2
    wp_if_destruct
    · have hjl : sint.nat j < rs.length := by
        have : sint.Z j < sint.Z nr := Hif
        have h2 : sint.Z nr = rs.length := Hnr
        have := Hj.1; word
      have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
      obtain ⟨x, hx⟩ : ∃ x, rs[sint.nat j]? = some x := ⟨_, List.getElem?_eq_getElem hjl⟩
      have hxin : x ∈ rs := List.mem_of_getElem? hx
      have hcx : conforms S e x := (hallR x hxin).1
      obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 (show (keyOf ks x).isSome from (hallR x hxin).2)
      have hRk : R[sint.nat j]? = some k := by rw [hkR.2 _ _ hx, hk]
      rcases hor : or_ with _ | vsr
      · exfalso; rw [hor] at hrs; simp at hrs; subst hrs; simp at hjl
      rw [hor] at hrs
      simp only [Option.getD_some] at hrs
      iunfold isListO at HrO
      icases LawA3.isListV_dispatchL h_listUnstructured_Length h_listUnstructured_Length_ptr
        h_listUnstructured_At h_listUnstructured_At_ptr rl vsr $$ [] with ⟨%ri, %Hri, -, #HAtR⟩
      · iframe #; iPkgInit
      subst Hri
      wp_auto
      wp_apply HAtR $$ %j %x as %child Hch
      · ipureintro; exact ⟨Hj.1, by rw [hrs]; exact hx⟩
      try wp_auto
      wp_apply h_listItemToPathElement st.alloc sc S tp e ks fs em rel' child (DFrac.own 1) x st.t.name
        $$ [Ha Hch] as %pe1 %err Hpost
      · iframe; iframe #; ipureintro; exact ⟨Hwf, hkne, hfe, Hfind, hcx, by rw [hk]; rfl⟩
      rw [hk]
      icases Hpost with ⟨Ha, Hch, %herr, #Hpe1⟩
      subst herr
      try wp_auto
      have hkfresh : k ∉ R.take (sint.nat j) := by
        rw [← htkR]; exact LawA2.keyOf_fresh ks rs _ x k (by rw [hRdef]; exact hndR) hx hk
      have hMRk : MR k = none := by
        cases h : MR k with
        | none => rfl
        | some _ => exact absurd ((HMRs k).1 (by rw [h]; rfl)) hkfresh
      ihave HMo : ownPEMap rValues_ptr MR $$ [rValues Hrv]
      · unfold ownPEMap; iexists _; iframe
      wp_apply h_PathElementMap_Get rValues_ptr MR pe1 k $$ [HMo] as %x1 %ok1 ⟨HMo, %Hok1⟩
      · iframe; iframe #
      rw [hMRk] at Hok1
      obtain ⟨-, rfl⟩ := Hok1
      wp_auto
      imod isValF_persist_law_holds _ _ _ $$ Hch with #Hch
      wp_apply (wp_slice_literal (V := value.Value) [child])
      isplitr
      · ipureintro; rfl
      iintro %sl2 ⟨Hsl2, -⟩
      imod ownSlice_persist _ _ _ $$ Hsl2 with #Hsl2
      try wp_auto
      wp_apply h_PathElementMap_Insert rValues_ptr MR pe1 k _ $$ [HMo] as HMo
      · iframe; iframe #; ipureintro
        refine LawBL2.peMap_cardLt MR (R.take (sint.nat j)) _ (fun k' hk' => (HMRs k').1 hk') ?_
        have := List.length_take_le (sint.nat j) R
        omega
      try wp_auto
      wp_apply h_PathElementMap_Get lValues_ptr ML pe1 k $$ [HLo] as %x3 %ok3 ⟨HLo, %Hok3⟩
      · iframe; iframe #
      have hok3 : ok3 = decide (k ∈ L) := by
        cases h : ML k with
        | none =>
          rw [h] at Hok3; rw [Hok3.2]
          have : k ∉ L := fun hh => by have := (HMLs k).2 hh; rw [h] at this; cases this
          simp [this]
        | some y =>
          rw [h] at Hok3; rw [Hok3.2]
          simp [(HMLs k).1 (by rw [h]; rfl)]
      subst hok3
      have htk : R.take (sint.nat j + 1) = R.take (sint.nat j) ++ [k] := by
        rw [List.take_add_one, hRk]; rfl
      by_cases hkin : k ∈ L
      · rw [decide_eq_true hkin]
        wp_auto
        wp_for_post
        iunfold ownPEMap at HMo
        icases HMo with ⟨%rv', rValues, Hrv⟩
        iframe
        iexists (j + W64 1), _, _, asl, es
        rw [hj1, htk]
        iframe
        isplitr
        · imodintro
          iapply LawBL2C.slMapRep_insert _ _ MR k x _ child
            (LawBL2.itemOf_take_succ_eq ks rs _ x k hx hk (by rw [htkR]; exact hkfresh))
            (fun k' h => LawBL2.itemOf_take_succ_ne ks rs _ x k k' hx hk h)
          iframe #
        isplitr
        · imodintro
          simp only [List.filter_append, List.filter_cons, List.filter_nil, hkin, not_true_eq_false,
            decide_false, Bool.false_eq_true, ↓reduceIte, List.append_nil]
          iexact Hes
        ipureintro
        refine ⟨?_, by word, by word⟩
        intro k'
        simp only [PEMap.insert, List.mem_append, List.mem_singleton]
        by_cases h : k' = k
        · simp [h]
        · simp [h, HMRs k']
      · rw [decide_eq_false hkin]
        wp_auto
        wp_apply (wp_slice_literal (V := fieldpath.PathElement) [pe1])
        isplitr
        · ipureintro; rfl
        iintro %sl3 ⟨Hsl3, -⟩
        try wp_auto
        wp_apply (wp_slice_append (V := fieldpath.PathElement) asl _ _ [pe1] (DFrac.own 1))
          $$ [Hasl Hacap Hsl3] as %asl' ⟨Hasl', Hacap', -⟩
        · iframe
        try wp_auto
        wp_for_post
        iunfold ownPEMap at HMo
        icases HMo with ⟨%rv', rValues, Hrv⟩
        iframe
        iexists (j + W64 1), _, _, asl', es ++ [pe1]
        rw [hj1, htk]
        iframe
        isplitr
        · imodintro
          iapply LawBL2C.slMapRep_insert _ _ MR k x _ child
            (LawBL2.itemOf_take_succ_eq ks rs _ x k hx hk (by rw [htkR]; exact hkfresh))
            (fun k' h => LawBL2.itemOf_take_succ_ne ks rs _ x k k' hx hk h)
          iframe #
        isplitr
        · imodintro
          have hf : (R.take (sint.nat j) ++ [k]).filter (fun x => decide (x ∉ L)) =
              (R.take (sint.nat j)).filter (fun x => decide (x ∉ L)) ++ [k] := by
            simp [List.filter_append, hkin]
          rw [hf, ← List.append_assoc]
          iapply LawBL2C.isPEs_snoc
          iframe #
        ipureintro
        refine ⟨?_, by word, by word⟩
        intro k'
        simp only [PEMap.insert, List.mem_append, List.mem_singleton]
        by_cases h : k' = k
        · simp [h]
        · simp [h, HMRs k']
    · have hjR : sint.nat j = rs.length := by
        have : ¬ sint.Z j < sint.Z nr := Hif
        have h2 : sint.Z nr = rs.length := Hnr
        have := Hj.2; have := Hj.1; word
      have hRR : R.take rs.length = R := by rw [← hkR.1]; exact List.take_length
      rw [hjR, hRR] at HMRs
      rw [hjR, List.take_length, hRR]
      ihave HRo : ownPEMap rValues_ptr MR $$ [rValues Hrv]
      · unfold ownPEMap; iexists _; iframe
      -- the third loop: each key's items compared
      ihave Hown : cwOwn w sc S st c C sp $$ [Hw Hp Hsp Ha Hcmp]
      · unfold cwOwn cwCore; iexists ps; iframe; iframe #; ipureintro; exact Hwf
      ihave %Hesl := isPEs_length_law_holds _ _ $$ Hes
      ihave #Hpat := LawBL2.isPEs_at _ _ $$ Hes
      imod ownSlice_persist _ _ _ $$ Hasl with #Hasl
      ihave %Haslen := ownSlice_len _ _ _ $$ Hasl
      obtain ⟨P, hPdef⟩ : ∃ P, L ++ R.filter (fun x => decide (x ∉ L)) = P := ⟨_, rfl⟩
      rw [hPdef] at Hesl
      rw [hPdef]
      obtain ⟨f, hfdef⟩ : ∃ f : PE → Cmp, (fun pe => cmpF (fuelL ls rs) S e (st.path ++ [pe])
          (itemOf ks ls pe) (itemOf ks rs pe)) = f := ⟨_, rfl⟩
      have hout : cmpListOut (fuelL ls rs) S e ks st.path ls rs = Cmp.unionAll (P.map f) := by
        unfold cmpListOut; rw [hLdef, hRdef, hPdef, ← hfdef]
      rw [hout] at Hcard ⊢
      ihave HI3 : (∃ (j : w64) (pv : fieldpath.PathElement) (el : GoSlice) (spj : Loc),
          "i" ∷ i_ptr ↦ j ∗ "pe" ∷ pe_ptr ↦ pv ∗ "errs" ∷ errs_ptr ↦ el ∗ "Herrs" ∷ noErrs el ∗
          "Hown" ∷ cwOwn w sc S st c (C.union (Cmp.unionAll ((P.take (sint.nat j)).map f))) spj ∗
          "HLo" ∷ ownPEMap lValues_ptr ML ∗ "HRo" ∷ ownPEMap rValues_ptr MR ∗
          "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ es.length ∧ (sp ≠ null → spj = sp)⌝ : IProp GF)
        $$ [i pe errs Hown HLo HRo]
      · iexists _, _, _, sp
        iframe
        rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero, LawBL2C.cmp_union_nil]
        iframe
        isplitr
        · iapply (noErrs_nil (GF := GF))
        ipureintro; exact ⟨by decide, by simp, fun _ => rfl⟩
      wp_for HI3
      wp_if_destruct
      · have hjl : sint.nat j < P.length := by
          have h1 : sint.Z j < sint.Z asl.len := Hif
          have := Haslen.1; have := Haslen.2; have := Hj.1; rw [← Hesl]; word
        have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by
          have := Haslen.1; have := Haslen.2; have := Hj.1; word
        obtain ⟨pv1, hpv1⟩ : ∃ x, es[sint.nat j]? = some x :=
          ⟨_, List.getElem?_eq_getElem (by rw [Hesl]; exact hjl)⟩
        obtain ⟨k, hkP⟩ : ∃ x, P[sint.nat j]? = some x := ⟨_, List.getElem?_eq_getElem hjl⟩
        ihave #Hpe1 := Hpat $$ %(sint.nat j) %pv1 %k %(And.intro hpv1 hkP)
        have hb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z asl.len := ⟨Hj.1, Hif⟩
        simp only [hb, and_self, ↓reduceIte]
        wp_apply (wp_load_slice_index (V := fieldpath.PathElement) asl (sint.Z j) es DFrac.discard pv1 Hj.1)
          $$ [Hasl] as -
        · iframe #; ipureintro; rw [show (sint.Z j).toNat = sint.nat j from rfl]; exact hpv1
        try wp_auto
        wp_join iprop(∃ lsl : GoSlice, lList_ptr ↦ lsl ∗ LawBL2C.slotRep lsl (itemOf ks ls k) ∗
            ownPEMap lValues_ptr ML)
          at next with [lList HLo] as ⟨%lsl, lList, #Hlsl, HLo⟩
        · wp_apply h_PathElementMap_Get lValues_ptr ML pv1 k $$ [HLo] as %x1 %ok1 ⟨HLo, %Hok1⟩
          · iframe; iframe #
          have hiff := LawBL2.itemOf_isSome ks ls k
          rw [hLdef] at hiff
          cases hil : itemOf ks ls k with
          | none =>
            have hMk : ML k = none := by
              cases h : ML k with
              | none => rfl
              | some _ =>
                have h1 := (HMLs k).1 (by rw [h]; rfl)
                have h2 := hiff.2 h1
                rw [hil] at h2; cases h2
            rw [hMk] at Hok1
            obtain ⟨rfl, rfl⟩ := Hok1
            wp_auto
            wp_join_done
            iexists _
            iframe
            unfold LawBL2C.slotRep
            ipureintro; rfl
          | some x =>
            ihave ⟨%sl, %v, %hMk, #Hsl, #Hv⟩ := LawBL2C.slMapRep_some _ _ k x hil $$ HML
            rw [hMk] at Hok1
            obtain ⟨rfl, rfl⟩ := Hok1
            wp_auto
            wp_join_done
            iexists _
            iframe
            unfold LawBL2C.slotRep
            iexists v
            iframe #
        wp_join iprop(∃ rsl : GoSlice, rList_ptr ↦ rsl ∗ LawBL2C.slotRep rsl (itemOf ks rs k) ∗
            ownPEMap rValues_ptr MR)
          at next with [rList HRo] as ⟨%rsl, rList, #Hrsl, HRo⟩
        · wp_apply h_PathElementMap_Get rValues_ptr MR pv1 k $$ [HRo] as %x1 %ok1 ⟨HRo, %Hok1⟩
          · iframe; iframe #
          have hiff := LawBL2.itemOf_isSome ks rs k
          rw [hRdef] at hiff
          cases hil : itemOf ks rs k with
          | none =>
            have hMk : MR k = none := by
              cases h : MR k with
              | none => rfl
              | some _ =>
                have h1 := (HMRs k).1 (by rw [h]; rfl)
                have h2 := hiff.2 h1
                rw [hil] at h2; cases h2
            rw [hMk] at Hok1
            obtain ⟨rfl, rfl⟩ := Hok1
            wp_auto
            wp_join_done
            iexists _
            iframe
            unfold LawBL2C.slotRep
            ipureintro; rfl
          | some x =>
            ihave ⟨%sl, %v, %hMk, #Hsl, #Hv⟩ := LawBL2C.slMapRep_some _ _ k x hil $$ HMR
            rw [hMk] at Hok1
            obtain ⟨rfl, rfl⟩ := Hok1
            wp_auto
            wp_join_done
            iexists _
            iframe
            unfold LawBL2C.slotRep
            iexists v
            iframe #
        ihave %Hlsl' := LawBL2C.slotRep_len _ _ $$ Hlsl
        ihave %Hrsl' := LawBL2C.slotRep_len _ _ $$ Hrsl
        have hkPm : k ∈ P := List.mem_of_getElem? hkP
        have hsome : itemOf ks ls k ≠ none ∨ itemOf ks rs k ≠ none := by
          rw [← hPdef, List.mem_append] at hkPm
          rcases hkPm with h | h
          · left
            have := (LawBL2.itemOf_isSome ks ls k).2 (by rw [hLdef]; exact h)
            intro hn; rw [hn] at this; cases this
          · right
            have h' := (List.mem_filter.1 h).1
            have := (LawBL2.itemOf_isSome ks rs k).2 (by rw [hRdef]; exact h')
            intro hn; rw [hn] at this; cases this
        have hlen0 : ¬ (lsl.len = W64 0 ∧ rsl.len = W64 0) := by
          rintro ⟨h1, h2⟩
          have e1 : sint.Z lsl.len = 0 := by rw [h1]; rfl
          have e2 : sint.Z rsl.len = 0 := by rw [h2]; rfl
          rcases hsome with h | h
          · exact h (Hlsl'.2.1 e1)
          · exact h (Hrsl'.2.1 e2)
        have hl1 : sint.Z lsl.len ≤ sint.Z (W64 1) := Hlsl'.1
        have hr1 : sint.Z rsl.len ≤ sint.Z (W64 1) := Hrsl'.1
        by_cases hl0 : lsl.len = W64 0 <;>
          first
          | (rw [decide_eq_true hl0]; wp_auto; rw [decide_eq_false (fun h => hlen0 ⟨hl0, h⟩)]; wp_auto)
          | (rw [decide_eq_false hl0]; wp_auto)
        all_goals
          rw [decide_eq_true hl1]
          wp_auto
          rw [decide_eq_true hr1]
          wp_auto
          wp_join iprop(∃ lc : value.Value, lValue_ptr ↦ lc ∗ lList_ptr ↦ lsl ∗ isValO lc DFrac.discard (itemOf ks ls k))
            at (If _ _ _) with [lValue lList] as ⟨%lc, lValue, lList, Hlc⟩
          · cases hil : itemOf ks ls k with
            | none =>
              simp only [LawBL2C.slotRep]
              icases Hlsl with %hz
              have h0 : lsl.len = W64 0 := by word
              rw [h0]
              wp_auto
              wp_join_done
              iexists _
              iframe
              simp only [isValO]
              ipureintro; first | rfl | trivial
            | some x =>
              simp only [LawBL2C.slotRep]
              icases Hlsl with ⟨%v, #Hsl, #Hv⟩
              ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
              ihave %Hslwf := ownSlice_wf _ _ _ $$ Hsl
              have h0 : lsl.len ≠ W64 0 := by
                intro h; have h1 := Hsll.1; rw [h] at h1; simp only [List.length_singleton] at h1; word
              rw [decide_eq_false h0]
              wp_auto
              have hb0 : (0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z lsl.len) := by
                simp at Hsll; refine ⟨by decide, ?_⟩; have := Hsll.1; have := Hsll.2; word
              simp only [hb0, _root_.and_self, ↓reduceIte]
              wp_apply (wp_load_slice_index (V := value.Value) lsl (sint.Z (W64 0)) _ DFrac.discard v (by decide))
                $$ [Hsl] as -
              · iframe #; ipureintro; rfl
              try wp_auto
              wp_join_done
              iexists _
              iframe
              simp only [isValO]
              iexact Hv
          wp_join iprop(∃ lc : value.Value, rValue_ptr ↦ lc ∗ rList_ptr ↦ rsl ∗ isValO lc DFrac.discard (itemOf ks rs k))
            at (If _ _ _) with [rValue rList] as ⟨%rc, rValue, rList, Hrc⟩
          · cases hil : itemOf ks rs k with
            | none =>
              simp only [LawBL2C.slotRep]
              icases Hrsl with %hz
              have h0 : rsl.len = W64 0 := by word
              rw [h0]
              wp_auto
              wp_join_done
              iexists _
              iframe
              simp only [isValO]
              ipureintro; first | rfl | trivial
            | some x =>
              simp only [LawBL2C.slotRep]
              icases Hrsl with ⟨%v, #Hsl, #Hv⟩
              ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
              ihave %Hslwf := ownSlice_wf _ _ _ $$ Hsl
              have h0 : rsl.len ≠ W64 0 := by
                intro h; have h1 := Hsll.1; rw [h] at h1; simp only [List.length_singleton] at h1; word
              rw [decide_eq_false h0]
              wp_auto
              have hb0 : (0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z rsl.len) := by
                simp at Hsll; refine ⟨by decide, ?_⟩; have := Hsll.1; have := Hsll.2; word
              simp only [hb0, _root_.and_self, ↓reduceIte]
              wp_apply (wp_load_slice_index (V := value.Value) rsl (sint.Z (W64 0)) _ DFrac.discard v (by decide))
                $$ [Hsl] as -
              · iframe #; ipureintro; rfl
              try wp_auto
              wp_join_done
              iexists _
              iframe
              simp only [isValO]
              iexact Hv
          have hfk : f k = cmpO S e (st.path ++ [k]) (itemOf ks ls k) (itemOf ks rs k) := by
            rw [← hfdef]; exact LawBL2C.cmpF_item S e ks ls rs _ k
          have htk : P.take (sint.nat j + 1) = P.take (sint.nat j) ++ [k] := by
            rw [List.take_add_one, hkP]; rfl
          have hcard2 := LawBL2C.cardLt_keys C f (P.take (sint.nat j) ++ [k]) P
            (fun k' hk' => by rw [← htk] at hk'; exact List.mem_of_mem_take hk') _ Hcard
          rw [← LawBL2C.unionAll_snoc, hfk] at hcard2
          have hcl : confO S e (itemOf ks ls k) := by
            cases h : itemOf ks ls k with
            | none => trivial
            | some x => exact (hallL x (LawBL2.itemOf_mem h)).1
          have hcr : confO S e (itemOf ks rs k) := by
            cases h : itemOf ks rs k with
            | none => trivial
            | some x => exact (hallR x (LawBL2.itemOf_mem h)).1
          have hsome' : (itemOf ks ls k).isSome ∨ (itemOf ks rs k).isSome := by
            rcases hsome with h | h
            · left; exact Option.ne_none_iff_isSome.1 h
            · right; exact Option.ne_none_iff_isSome.1 h
          wp_apply HcLI $$ %w %sc %S %st %c %(C.union (Cmp.unionAll ((P.take (sint.nat j)).map f))) %tp %e
              %ElemRel.associative %ks %pv1 %k %lc %rc %DFrac.discard %DFrac.discard %(itemOf ks ls k)
              %(itemOf ks rs k) %spj [Hown Hlc Hrc] as %errs2 ⟨Herrs2, -, -, %spk, Hown, %Hspk⟩
          · iframe; iframe #; ipureintro
            exact ⟨hsome', hcl, hcr, Hleaf, hcard2.1, hcard2.2.1, hcard2.2.2⟩
          wp_apply LawA2.wp_append_noErrs el errs2 $$ [Herrs Herrs2] as %el' Hel'
          · iframe
          try wp_auto
          wp_for_post
          iframe
          iexists (j + W64 1), pv1, el', spk
          rw [hj1, htk, ← LawBL2C.unionAll_snoc, hfk]
          iframe
          ipureintro
          refine ⟨by word, by word, fun h => ?_⟩
          have h1 := Hj.2.2 h; subst h1; exact Hspk h
      · have hjP : sint.nat j = P.length := by
          have : ¬ sint.Z j < sint.Z asl.len := Hif
          have := Haslen.1; have := Haslen.2; have := Hj.1; have := Hj.2.1; rw [← Hesl]; word
        rw [hjP, List.take_length]
        iapply HΦ
        iframe
        ipureintro; exact Hj.2.2

end proof

end smd
end EtcdGrove
end Perennial
