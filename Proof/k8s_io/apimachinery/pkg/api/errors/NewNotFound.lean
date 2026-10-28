/-
Proof of `Spec/k8s_io/apimachinery/pkg/api/errors/NewNotFound.lean`: the details, the message (`fmt.Sprintf` of the resource's `String()` and the name), the status literal. Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.apimachinery.pkg.api.errors.NewNotFound
public import Spec.k8s_io.apimachinery.pkg.runtime.schema.GroupResource__String_ptr
public import Perennial.Proof.fmt.Link

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apierrors

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.api.errors.Assumptions]

theorem NewNotFound.wp_proof
    (wp_String : schema.GroupResource.String_ptr.spec (GF := GF) (hG := hG)) :
    NewNotFound.spec (GF := GF) (hG := hG) := by
  intro gr name
  wp_start
  ihave #Pf : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_String $$ [$qualifiedResource] as %str qualifiedResource
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %asl ⟨Hasl, -⟩
  wp_apply (_root_.Perennial.fmt.wp_Sprintf _ _ _ (DFrac.own 1) (by
    exact _root_.Perennial.fmt.ArgsWf.cons_string _ _ (_root_.Perennial.fmt.ArgsWf.cons_string _ _
      _root_.Perennial.fmt.ArgsWf.nil)))
    $$ [$Hasl] as %s -
  iapply HΦ
  iexists _
  iframe
  ipureintro
  exact ⟨rfl, rfl, rfl⟩

end proof

end apierrors
end EtcdGrove
end Perennial
