/-
`typed.mergingWalker.indexListPathElements`: the items' keys in order and the map from each key to
its item (the keys distinct: no duplicate branch taken).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker__indexListPathElements
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.MakePathElementValueMap
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElementValueMap__Get
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElementValueMap__Insert
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructured__At
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructured__At_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructured__Length
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructured__Length_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.listItemToPathElement
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.NewValueInterface
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsA
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsA2
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsA3
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsBPers
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsBList2
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

theorem typed.mergingWalker.indexListPathElements.wp_proof
    (h_MakePathElementValueMap : fieldpath.MakePathElementValueMap.spec (GF := GF))
    (h_PathElementValueMap_Get : fieldpath.PathElementValueMap.Get.spec (GF := GF))
    (h_PathElementValueMap_Insert : fieldpath.PathElementValueMap.Insert.spec (GF := GF))
    (h_listUnstructured_At : value.listUnstructured.At.spec (GF := GF))
    (h_listUnstructured_At_ptr : value.listUnstructured.At_ptr.spec (GF := GF))
    (h_listUnstructured_Length : value.listUnstructured.Length.spec (GF := GF))
    (h_listUnstructured_Length_ptr : value.listUnstructured.Length_ptr.spec (GF := GF))
    (h_listItemToPathElement : typed.listItemToPathElement.spec (GF := GF))
    (h_NewValueInterface : value.NewValueInterface.spec (GF := GF)) :
    typed.mergingWalker.indexListPathElements.spec (GF := GF) := by
  intro w wv sc S tp e ks fs el r ll ol allowDup tn
  wp_start as ⟨Hw, Ha, #Hsc, %Hsc', #Hl, Hlo, %Hpre⟩
  obtain ⟨Hwf, hkne, hfe, htn, hall, hnd⟩ := Hpre
  subst Hsc'
  rcases ol with _ | vs
  · iunfold isListO at Hlo
    icases Hlo with %Hll
    subst Hll
    wp_auto
    wp_apply h_MakePathElementValueMap (W64 0) $$ [] as %ov Hov
    · ipureintro; decide
    try wp_auto
    wp_apply (wp_slice_make3 (V := fieldpath.PathElement) (W64 0) (W64 0) (by decide))
      as %sl0 ⟨Hsl0, Hcap0, -⟩
    try wp_auto
    ihave HI : ("i" ∷ i_ptr ↦ W64 0 : IProp GF) $$ [i]
    · iframe
    wp_for HI
    iapply HΦ
    iframe
    isplitr
    · iapply noErrs_nil
    simp only [List.replicate, Option.getD_none, keysOf, List.filterMap_nil]
    isplitr
    · have hnil : iprop(True) ⊢ isPEs (GF := GF) [] [] := isPEs_nil_law_holds
      iapply hnil; itrivial
    iintro %k
    simp only [itemOf, List.find?_nil, PEMap.empty]
    itrivial
  · iunfold isListO at Hlo
    ihave #Hlv := isListV_persistent_law_holds ll vs $$ Hlo
    icases LawA3.isListV_dispatchL h_listUnstructured_Length h_listUnstructured_Length_ptr
      h_listUnstructured_At h_listUnstructured_At_ptr ll vs $$ [] with ⟨%li, %Hli, #HLen, #HAt⟩
    · iframe #; iPkgInit
    subst Hli
    simp only [Option.getD_some] at hall hnd ⊢
    wp_auto
    wp_apply HLen as %n %Hn
    wp_apply h_MakePathElementValueMap n $$ [] as %ov Hov
    · ipureintro; show 0 ≤ n.toInt; omega
    try wp_auto
    have hlen63 : vs.length < 2 ^ 63 := by have := n.toInt_lt; omega
    wp_apply (wp_slice_make3 (V := fieldpath.PathElement) (W64 0) n (by
      constructor
      · decide
      · show (0 : Int) ≤ n.toInt; omega)) as %sl0 ⟨Hsl0, Hcap0, -⟩
    try wp_auto
    ipersist w
    ipersist t
    ipersist list
    ipersist length
    ihave HI : (∃ (j : w64) (sl : GoSlice) (es : List fieldpath.PathElement)
        (ovv : fieldpath.PathElementValueMap) (M : PEMap value.Value),
        "i" ∷ i_ptr ↦ j ∗ "pes" ∷ pes_ptr ↦ sl ∗ "Hsl" ∷ sl ↦* es ∗
        "Hcap" ∷ ownSliceCap fieldpath.PathElement sl (DFrac.own 1) ∗
        "Hes" ∷ isPEs es (keysOf ks (vs.take (sint.nat j))) ∗
        "observed" ∷ observed_ptr ↦ ovv ∗ "Hov" ∷ ownPEVMapV ovv M ∗
        "#HM" ∷ □ (∀ k, match itemOf ks (vs.take (sint.nat j)) k, M k with
          | none, none => iprop(True)
          | some x, some v => isVal v x
          | _, _ => iprop(False)) ∗
        "%HMk" ∷ ⌜∀ k, (M k).isSome → k ∈ keysOf ks (vs.take (sint.nat j))⌝ ∗
        "Hw" ∷ w ↦ wv ∗ "Ha" ∷ isAlloc wv.allocator' ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ vs.length⌝ : IProp GF)
      $$ [i pes Hsl0 Hcap0 observed Hov Hw Ha]
    · iexists _, _, _, _, _
      iframe
      have h0 : vs.take (sint.nat (W64 0)) = [] := by simp
      rw [h0]
      simp only [List.replicate, keysOf, List.filterMap_nil]
      isplitr
      · have hnil : iprop(True) ⊢ isPEs (GF := GF) [] [] := isPEs_nil_law_holds
        iapply hnil; itrivial
      isplitr
      · imodintro; iintro %k; simp only [itemOf, List.find?_nil, PEMap.empty]; itrivial
      ipureintro
      refine ⟨fun k hk => by simp [PEMap.empty] at hk, by decide, by simp⟩
    wp_for HI
    wp_if_destruct
    · have hjZ : sint.Z j < vs.length := by
        have : sint.Z j < sint.Z n := Hif
        have h2 : sint.Z n = vs.length := Hn
        omega
      have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
      have hjl : sint.nat j < vs.length := by have := Hj.1; word
      obtain ⟨x, hx⟩ : ∃ x, vs[sint.nat j]? = some x := ⟨vs[sint.nat j], List.getElem?_eq_getElem hjl⟩
      have hxin : x ∈ vs := List.mem_of_getElem? hx
      obtain ⟨hcx, hkx⟩ := hall x hxin
      obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 (show (keyOf ks x).isSome from hkx)
      have hfresh : k ∉ keysOf ks (vs.take (sint.nat j)) := LawA2.keyOf_fresh ks vs _ x k hnd hx hk
      wp_apply HAt $$ %j %x as %child Hch
      · ipureintro; exact ⟨Hj.1, hx⟩
      try wp_auto
      wp_apply h_listItemToPathElement wv.allocator' wv.schema' S tp e ks fs el r child (DFrac.own 1) x tn
        $$ [Ha Hch] as %pe1 %err Hpost
      · iframe; iframe #; ipureintro; exact ⟨Hwf, hkne, hfe, htn, hcx, by rw [hk]; rfl⟩
      rw [hk]
      icases Hpost with ⟨Ha, Hch, %herr, #Hpe1⟩
      subst herr
      try wp_auto
      have hMk : M k = none := by
        cases h : M k with
        | none => rfl
        | some _ => exact absurd (HMk k (by rw [h]; rfl)) hfresh
      wp_apply h_PathElementValueMap_Get observed_ptr M pe1 k $$ [observed Hov] as %gx %gok ⟨Hov, %hg⟩
      · iframe #; unfold ownPEVMap; iexists ovv; iframe
      rw [hMk] at hg
      obtain ⟨-, rfl⟩ := hg
      try wp_auto
      ihave ⟨Hch, %hptr⟩ := LawA3.isValF_shape child (DFrac.own 1) x $$ Hch
      wp_apply h_PathElementValueMap_Insert observed_ptr M pe1 k child $$ [Hov] as Hov
      · iframe; iframe #; ipureintro
        refine ⟨hptr, LawBL2.peMap_cardLt M (keysOf ks (vs.take (sint.nat j))) _ (fun k h => HMk k h) ?_⟩
        have := LawA2.keysOf_take_length ks vs (sint.nat j); omega
      try wp_auto
      imod isValF_persist_law_holds _ _ _ $$ Hch with #Hcv
      wp_apply (wp_slice_literal (V := fieldpath.PathElement) [pe1])
      isplitr
      · ipureintro; rfl
      iintro %osl ⟨Hosl, -⟩
      try wp_auto
      wp_apply (wp_slice_append (V := fieldpath.PathElement) sl es _ [pe1] (DFrac.own 1))
        $$ [Hsl Hcap Hosl] as %sl' ⟨Hsl, Hcap, -⟩
      · iframe
      try wp_auto
      ihave %hesl := isPEs_length_law_holds _ _ $$ Hes
      wp_for_post
      iframe
      unfold ownPEVMap
      icases Hov with ⟨%ovv2, observed, Hov⟩
      iexists (j + W64 1), sl', es ++ [pe1], ovv2, M.insert k child
      rw [hj1, LawA2.keysOf_take_succ ks vs _ x hx, hk]
      simp only [Option.toList_some]
      iframe
      isplitl [Hes]
      · iapply (isPEs_app_law_holds es [pe1] _ [k] hesl).2
        iframe
        iapply (isPEs_cons_law_holds pe1 [] k []).2
        iframe #
        have hnil : iprop(True) ⊢ isPEs (GF := GF) [] [] := isPEs_nil_law_holds
        iapply hnil; itrivial
      isplitr
      · iintro !> %k'
        by_cases hkk : k' = k
        · subst hkk
          rw [LawBL2.itemOf_take_succ_eq ks vs _ x k' hx hk hfresh]
          simp only [PEMap.insert, if_true]
          iexact Hcv
        · rw [LawBL2.itemOf_take_succ_ne ks vs _ x k k' hx hk hkk]
          simp only [PEMap.insert, hkk, if_false]
          iapply HM
      ipureintro
      refine ⟨?_, by word, by word⟩
      intro k' hk'
      by_cases hkk : k' = k
      · subst hkk; simp
      · simp only [PEMap.insert, hkk, if_false] at hk'
        exact List.mem_append_left _ (HMk k' hk')
    · have hjk : sint.nat j = vs.length := by
        have : ¬ sint.Z j < sint.Z n := Hif
        have h2 : sint.Z n = vs.length := Hn
        have := Hj.2
        word
      rw [hjk, List.take_length] at *
      try wp_auto
      try simp only [_root_.decide_true, ↓reduceIte]
      try wp_auto
      iapply HΦ
      iframe
      isplitr
      · iapply noErrs_nil
      iintro %k
      ispecialize HM $$ %k
      generalize itemOf ks vs k = a
      generalize M k = b
      cases a <;> cases b <;> iexact HM

end proof

end smd
end EtcdGrove
end Perennial
