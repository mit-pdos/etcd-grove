/-
`typed.compareWalker.visitListItems`: a member of the recursion cluster `typed.compareWalkerRec` (`compareWalkerRec.lean`); its proof is the
projection of the cluster's (its body is `compareWalker__visitListItemsBody.lean`).
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
  obtain ⟨Hfind, Hleaf, Hcl, Hcr, Hrm, Hmd, Had⟩ := Hpre
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
  obtain ⟨hallL, hndL⟩ := hside ol Hcl
  obtain ⟨hallR, hndR⟩ := hside or_ Hcr
  obtain ⟨ls, hls⟩ : ∃ ls, ol.getD [] = ls := ⟨_, rfl⟩
  obtain ⟨rs, hrs⟩ : ∃ rs, or_.getD [] = rs := ⟨_, rfl⟩
  rw [hls] at hallL hndL Hrm Hmd Had ⊢
  rw [hrs] at hallR hndR Hrm Hmd Had ⊢
  clear Hcl Hcr hside
  rcases ol with _ | vsl <;> rcases or_ with _ | vsr
  all_goals simp only [Option.getD_none, Option.getD_some] at hls hrs
  all_goals
    first
    | (iunfold isListO at Hl; icases Hl with %Hll; subst Hll)
    | (iunfold isListO at Hl
       subst vsl
       icases LawA3.isListV_dispatchL h_listUnstructured_Length h_listUnstructured_Length_ptr
         h_listUnstructured_At h_listUnstructured_At_ptr ll ls $$ [Hl] with ⟨%li, %Hli, #HLenL, #HAtL⟩
       · iframe; iPkgInit
       subst Hli)
  all_goals
    first
    | (iunfold isListO at Hr; icases Hr with %Hrl; subst Hrl)
    | (iunfold isListO at Hr
       subst vsr
       icases LawA3.isListV_dispatchL h_listUnstructured_Length h_listUnstructured_Length_ptr
         h_listUnstructured_At h_listUnstructured_At_ptr rl rs $$ [Hr] with ⟨%ri, %Hri, #HLenR, #HAtR⟩
       · iframe; iPkgInit
       subst Hri)
  all_goals wp_auto
  all_goals try (wp_apply HLenR as %nr0 %Hnr0)
  all_goals try wp_auto
  all_goals try (wp_apply HLenL as %nl0 %Hnl0)
  all_goals try wp_auto
  all_goals try (wp_if_destruct <;> try wp_auto)
  all_goals
    ihave ⟨%nr, rLen, %Hnr⟩ : (∃ nr : w64, rLen_ptr ↦ nr ∗ ⌜nr.toInt = rs.length⌝ : IProp GF) $$ [rLen]
    · iexists _; iframe; ipureintro
      first | exact Hnr0 | (subst hrs; rfl)
    ihave ⟨%nl, lLen, %Hnl⟩ : (∃ nl : w64, lLen_ptr ↦ nl ∗ ⌜nl.toInt = ls.length⌝ : IProp GF) $$ [lLen]
    · iexists _; iframe; ipureintro
      first | exact Hnl0 | (subst hls; rfl)
  all_goals
    wp_apply (wp_slice_make3 (V := fieldpath.PathElement) (W64 0) _ ?_) as %sl0 ⟨Hsl0, Hcap0, -⟩
  all_goals try (refine ⟨by decide, ?_⟩; first | decide | (show (0:Int) ≤ BitVec.toInt _; omega))
  all_goals sorry

end proof

end smd
end EtcdGrove
end Perennial
