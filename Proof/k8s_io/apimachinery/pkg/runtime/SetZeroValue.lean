/-
Lean-first (no Rocq counterpart). The proof of `runtime.SetZeroValue`: `conversion.EnforcePtr`'s
`Value` of the pointee, its `Type()`, `reflect.Zero` of it, `Set` (the `reflect` trust boundary,
`Proof/reflect/Values.lean`).
-/
module

public import Spec.k8s_io.apimachinery.pkg.runtime.SetZeroValue
public import Spec.k8s_io.apimachinery.pkg.conversion.EnforcePtr
public import Spec.reflect.Value__Type
public import Spec.reflect.Zero
public import Spec.reflect.Value__Set

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode reflectM

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.runtime.Assumptions]
variable [reflect.Assumptions]

theorem runtime.SetZeroValue.wp_proof
    (wp_EnforcePtr : conversion.EnforcePtr.spec (GF := GF) (hG := hG))
    (wp_Type : reflect.Value.Type.spec (GF := GF) (hG := hG))
    (wp_Zero : reflect.Zero.spec (GF := GF) (hG := hG))
    (wp_Set : reflect.Value.Set.spec (GF := GF) (hG := hG)) :
    runtime.SetZeroValue.spec (GF := GF) (hG := hG) := by
  intro T p V _ _ _ x
  wp_start as ⟨%Hp, Hx⟩
  ihave #Pcv : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.conversion $$ []
  · iPkgInit
  ihave #Prf : isPkgInit (PROP := IProp GF) pkg_id.reflect $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_EnforcePtr T p $$ [] as %v %err %Hv
  · iframe #
    ipureintro; exact Hp
  obtain ⟨rfl, Hv⟩ := Hv
  (try wp_auto)
  wp_apply wp_Type v_ptr (DFrac.own 1) v T p $$ [$v] as %rt ⟨Hvp, %Hrt⟩
  · iframe #
    ipureintro; exact Hv
  (try wp_auto)
  wp_apply wp_Zero rt T $$ [] as %z %Hz
  · iframe #
    ipureintro; exact Hrt
  (try wp_auto)
  wp_apply wp_Set v_ptr (DFrac.own 1) v z T p V x $$ [$Hvp $Hx] as ⟨-, Hx⟩
  · iframe #
    ipureintro; exact ⟨Hv, Hz⟩
  (try wp_auto)
  iapply HΦ
  iexact Hx

end proof

end EtcdGrove
end Perennial
