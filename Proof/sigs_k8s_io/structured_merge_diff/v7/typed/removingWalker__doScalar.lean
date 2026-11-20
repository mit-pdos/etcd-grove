/-
`typed.removingWalker.doScalar`: proved (Prove phase, 2026-11-20): the output is the value's
`Unstructured()`, which at a scalar type is what removal leaves (`removeAt_scalar`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.removingWalker__doScalar
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.valueUnstructured__Unstructured_ptr
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.LawProofs
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsAPure
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsBPers

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

theorem typed.removingWalker.doScalar.wp_proof
    (h_valueUnstructured_Unstructured_ptr : value.valueUnstructured.Unstructured_ptr.spec (GF := GF)) :
    typed.removingWalker.doScalar.spec (GF := GF) :=
    fun w sc S v dq x rp R a t tp s => by
  wp_start as ⟨Hown, Hv, %Hfind⟩
  rw [removeAt_scalar_law_holds S t s R x Hfind]
  ihave %Hcv := isValF_concrete_law_holds v dq x $$ Hv
  obtain ⟨p, rfl⟩ := Hcv
  unfold rmOwn
  icases Hown with ⟨Hw, #Hsc, %HWF, #HR, Ha⟩
  wp_auto
  wp_apply h_valueUnstructured_Unstructured_ptr p dq x $$ [Hv] as %u ⟨Hv, #Hu⟩
  · iframe Hv
  iapply HΦ
  iexists u
  iframe
  iframe #
  ipureintro; exact HWF

end proof

end smd
end EtcdGrove
end Perennial
