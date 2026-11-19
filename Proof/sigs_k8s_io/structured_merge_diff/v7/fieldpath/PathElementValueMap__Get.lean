/-
`fieldpath.PathElementValueMap.Get`: proved over its callees' specs (the hypotheses).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElementValueMap__Get
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElementMap__Get
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Defs
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Vocab
import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsRep
import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsPESet

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
variable [package_sem : fieldpath.Assumptions]

theorem fieldpath.PathElementValueMap.Get.wp_proof
    (h_PathElementMap_Get : fieldpath.PathElementMap.Get.spec (GF := GF)) :
    fieldpath.PathElementValueMap.Get.spec (GF := GF) := fun l M e pe => by
  wp_start as ⟨Hs, #He⟩
  unfold ownPEVMap ownPEVMapV
  icases Hs with ⟨%v, Hl, Hmap, %hptr⟩
  icases fpA.pevmap_valueMap_upd l v (DFrac.own 1) $$ Hl with ⟨Hf, Hback⟩
  wp_auto
  wp_apply (h_PathElementMap_Get _ M e pe) $$ [Hf Hmap] as %x %ok ⟨Hmap, %hres⟩
  · isplitl [Hf Hmap]
    · unfold ownPEMap; iexists _; iframe
    · iexact He
  cases hM : M pe with
  | none =>
    rw [hM] at hres
    obtain ⟨rfl, rfl⟩ := hres
    wp_auto
    iapply HΦ
    isplitl [Hmap Hback]
    · unfold ownPEMap
      icases Hmap with ⟨%w, Hw, Hmv⟩
      iexists _
      isplitl [Hback Hw]
      · iapply Hback; iexact Hw
      iframe; ipureintro; exact hptr
    ipureintro
    exact ⟨rfl, rfl⟩
  | some y =>
    rw [hM] at hres
    obtain ⟨rfl, rfl⟩ := hres
    obtain ⟨p, rfl⟩ := hptr pe _ hM
    wp_auto
    have ht : go.typeSetContains (go.GoType.PointerType value.valueUnstructured.ty) value.Value.ty = true := by
      go_type_set
    rw [if_pos ht]
    wp_auto
    iapply HΦ
    isplitl [Hmap Hback]
    · unfold ownPEMap
      icases Hmap with ⟨%w, Hw, Hmv⟩
      iexists _
      isplitl [Hback Hw]
      · iapply Hback; iexact Hw
      iframe; ipureintro; exact hptr
    ipureintro
    exact ⟨rfl, rfl⟩

end proof

end smd
end EtcdGrove
end Perennial
