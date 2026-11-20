/-
`typed.removeItemsWithSchema`: a member of the recursion cluster `typed.removingWalkerRec` (`removingWalkerRec.lean`); its proof is the
projection of the cluster's (its body is `removeItemsWithSchemaBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.removeItemsWithSchemaBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.resolveSchema
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.NewFreelistAllocator
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.NewValueInterface
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.removingWalker__doScalar
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsA
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsAPure
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

theorem typed.removeItemsWithSchema.wp_proofBody
    (h_resolveSchema : typed.resolveSchema.spec (GF := GF))
    (h_NewFreelistAllocator : value.NewFreelistAllocator.spec (GF := GF))
    (h_NewValueInterface : value.NewValueInterface.spec (GF := GF))
    (h_removingWalker_doScalar : typed.removingWalker.doScalar.spec (GF := GF)) :
    typed.removeItemsWithSchema.specBody (GF := GF) := by
  unfold typed.removeItemsWithSchema.specBody typed.removingWalkerRec.specI
    typed.removeItemsWithSchema.specI typed.removingWalker.doList.specI
    typed.removingWalker.doMap.specI
  iintro #IH
  iintro %v %dq %x %rp %sc %R %S %tr %t
  wp_start as ⟨Hv, #HR, #Hsc, #Htr, %Hpre⟩
  obtain ⟨HWF, Hc⟩ := Hpre
  obtain ⟨A, hA⟩ := Option.isSome_iff_exists.1 (LawA.conforms_find S t x Hc)
  wp_auto
  wp_apply h_NewFreelistAllocator as %a Ha
  ihave Hown : rmOwn «$r0_ptr» sc S v rp R a interface.nil $$ [«$r0» Ha]
  · unfold rmOwn; iframe; iframe #; ipureintro; exact HWF
  icases IH with ⟨-, #HdL, #HdM⟩
  wp_apply h_resolveSchema sc S tr t A v dq (some x)
    (go.GoType.PointerType typed.removingWalker.ty) #«$r0_ptr» iprop(rmOwn «$r0_ptr» sc S v rp R a interface.nil)
    (fun errs => iprop(∃ out : GoInterface, rmOwn «$r0_ptr» sc S v rp R a out ∗
      isIface out (removeAt S t R x) ∗ isValO v dq (some x)))
    $$ [Hv Hown] as %errs ⟨%out, Hown, #Hout, Hv⟩
  · iframe #
    unfold isValO
    iframe Hv Hown
    isplitr
    · ipureintro; exact ⟨HWF, hA⟩
    iintro %atm #Hat
    cases A with
    | scalar s' =>
      simp only [atomHandlerOk]
      icases (isAtomOpt_scalar_law_holds atm s').1 $$ Hat with ⟨#Hs', -⟩
      imodintro
      iintro %Φ2 ⟨Hv, Hown⟩ HΦ2
      wp_apply h_removingWalker_doScalar «$r0_ptr» sc S v dq x rp R a t atm.Scalar' s' $$ [Hv Hown]
        as %errs ⟨%out, Hown, Hout, Hv⟩
      · iframe #; iframe; ipureintro; exact hA
      iapply HΦ2
      iexists out
      iframe
    | list e rel ks =>
      simp only [atomHandlerOk]
      icases (isAtomOpt_list_law_holds atm e rel ks).1 $$ Hat with ⟨-, #Hl⟩
      imodintro
      iintro %Φ2 ⟨Hv, Hown⟩ HΦ2
      wp_apply HdL $$ [Hv Hown] as %errs ⟨%out, Hown, Hout, Hv⟩
      · iframe #; iframe; ipureintro; exact ⟨hA, Hc⟩
      iapply HΦ2
      iexists out
      iframe
    | map fs e rel =>
      simp only [atomHandlerOk]
      icases (isAtomOpt_map_law_holds atm fs e rel).1 $$ Hat with ⟨-, #Hm⟩
      imodintro
      iintro %Φ2 ⟨Hv, Hown⟩ HΦ2
      wp_apply HdM $$ [Hv Hown] as %errs ⟨%out, Hown, Hout, Hv⟩
      · iframe #; iframe; ipureintro; exact ⟨hA, Hc⟩
      iapply HΦ2
      iexists out
      iframe
  unfold rmOwn
  icases Hown with ⟨Hw, -⟩
  wp_auto
  wp_apply h_NewValueInterface out (removeAt S t R x) $$ [] as %v' Hv'
  · iframe #
  iapply HΦ
  unfold isValO
  iframe

end proof

end smd
end EtcdGrove
end Perennial
