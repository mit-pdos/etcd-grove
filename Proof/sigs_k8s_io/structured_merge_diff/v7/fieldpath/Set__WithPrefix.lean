/-
`fieldpath.Set.WithPrefix`: proved over its callees' specs (the hypotheses).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__WithPrefix
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.NewSet
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.SetNodeMap__Get
import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsSet
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Defs

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

theorem fieldpath.Set.WithPrefix.wp_proof
    (h_NewSet : fieldpath.NewSet.spec (GF := GF))
    (h_SetNodeMap_Get : fieldpath.SetNodeMap.Get.spec (GF := GF)) :
    fieldpath.Set.WithPrefix.spec (GF := GF) := fun p S e pe => by
  wp_start as ⟨#Hs, #He⟩
  icases (fpC.isSet_view p S).1 $$ Hs with ⟨%v, #Hp, #Hm, #Hc, %hne⟩
  iStructNamed Hp
  wp_auto
  wp_apply (h_SetNodeMap_Get (p.[fieldpath.Set', go!"Children"]) S.deep e pe) as %q %ok ⟨%hok, Hq⟩
  · iframe #
    unfold isNodes; iexists v.Children'; iframe #
  cases ok
  · have hnh : pe ∉ S.deep.heads := fun h => by simpa using hok.2 h
    iapply wp_fupd
    wp_auto
    ihave Hnil := ownSlice_nil (V := GoSlice) (GF := GF) DFrac.discard
    wp_apply (h_NewSet slice.nil DFrac.discard [] []) $$ [$Hnil] as %r ⟨-, Hr⟩
    · unfold isPaths; itrivial
    imod fpS.ownSet_persist r _ $$ Hr with #Hr
    imodintro
    iapply HΦ
    rw [← fpS.under_deep S pe, fpS.under_empty _ _ hnh]
    iexact Hr
  · simp only [↓reduceIte]
    wp_auto
    iapply HΦ
    rw [← fpS.under_deep S pe]
    iexact Hq

end proof

end smd
end EtcdGrove
end Perennial
