/-
`typed.removingWalker.doMap`: a member of the recursion cluster `typed.removingWalkerRec` (`removingWalkerRec.lean`); its proof is the
projection of the cluster's (its body is `removingWalker__doMapBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.removingWalker__doMapBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.MakePath
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__Empty
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__Has
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__WithPrefix
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.heapAllocator__Free
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.freelistAllocator__Free
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.mapUnstructuredString__Empty
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.mapUnstructuredString__Iterate
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__AsMapUsing_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__IsMap_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__Unstructured_ptr
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsA5
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsBPers
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsBList
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.LawProofsDispatch
public import Proof.sigs_k8s_io.structured_merge_diff.v7.LawProofs.Intro
public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsRep
public import Proof.sigs_k8s_io.structured_merge_diff.v7.schema.LawProofs

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

theorem typed.removingWalker.doMap.wp_proofBody
    (h_MakePath : fieldpath.MakePath.spec (GF := GF))
    (h_Set_Empty : fieldpath.Set.Empty.spec (GF := GF))
    (h_Set_Has : fieldpath.Set.Has.spec (GF := GF))
    (h_Set_WithPrefix : fieldpath.Set.WithPrefix.spec (GF := GF))
    (h_heapAllocator_Free : value.heapAllocator.Free.spec (GF := GF))
    (h_freelistAllocator_Free : value.freelistAllocator.Free.spec (GF := GF))
    (h_mapUnstructuredString_Empty : value.mapUnstructuredString.Empty.spec (GF := GF))
    (h_mapUnstructuredString_Iterate : value.mapUnstructuredString.Iterate.spec (GF := GF))
    (h_valueUnstructured_AsMapUsing_ptr : value.valueUnstructured.AsMapUsing_ptr.spec (GF := GF))
    (h_valueUnstructured_IsMap_ptr : value.valueUnstructured.IsMap_ptr.spec (GF := GF))
    (h_valueUnstructured_Unstructured_ptr : value.valueUnstructured.Unstructured_ptr.spec (GF := GF)) :
    typed.removingWalker.doMap.specBody (GF := GF) := by
  unfold typed.removingWalker.doMap.specBody typed.removingWalkerRec.specI
    typed.removeItemsWithSchema.specI typed.removingWalker.doList.specI
    typed.removingWalker.doMap.specI
  iintro #IH
  icases IH with ⟨#HRm, -, -⟩
  iintro %w %sc %S %v %dq %x %rp %R %a %t %tp %fs %e %rel
  wp_start as ⟨Hown, Hv, #Hmr, %Hpre⟩
  wp_method_call; wp_call
  obtain ⟨Hfind, Hc⟩ := Hpre
  ihave ⟨Hv, %hsh⟩ := LawA3.isValF_shape _ _ _ $$ Hv
  obtain ⟨p, rfl⟩ := hsh
  unfold rmOwn
  icases Hown with ⟨Hw, #Hsc, %Hwf, #HR, Ha⟩
  ihave ⟨Ha, %ia, %Hia, #Hfree⟩ := isAlloc_Free h_heapAllocator_Free h_freelistAllocator_Free a $$ [Ha]
  · iframe Ha; iPkgInit
  subst Hia
  wp_auto
  wp_bind (App (Val wrapDefer) _)
  wp_apply wp_with_defer as %defer defer
  try wp_auto
  wp_apply h_valueUnstructured_IsMap_ptr p dq x $$ [Hv] as %r1 ⟨Hv, %hr1⟩
  · iframe
  subst hr1
  cases hxm : x.isMapB
  · wp_auto
    iapply HΦ
    iexists GoInterface.nil
    iframe; iframe #
    rw [LawA5.removeAt_map_nonmap S t fs e rel R x Hfind hxm]
    isplitr
    · ipureintro; exact Hwf
    iapply (isIface_scalar_law_holds (GF := GF)).1
    ipureintro; trivial
  obtain ⟨kvs, rfl⟩ : ∃ kvs, x = .map kvs := by cases x <;> simp_all [UVal.isMapB]
  wp_auto
  wp_apply h_valueUnstructured_AsMapUsing_ptr p dq kvs (GoInterface.ok ia) $$ [Hv] as %mv ⟨Hv, Hmv⟩
  · iframe
  ihave %Hmc := isMapV_concrete_law_holds mv kvs $$ Hmv
  obtain ⟨gm, rfl⟩ := Hmc
  ihave ⟨HmvS, HfM⟩ := (freeable_view_law_holds).1 _ kvs $$ Hmv
  ihave #Hmv := isMapV_persistent_law_holds _ kvs $$ HmvS
  try iclear HmvS
  ihave %hsorted := isMapV_sorted_law_holds _ kvs $$ Hmv
  wp_auto
  sorry

end proof

end smd
end EtcdGrove
end Perennial
