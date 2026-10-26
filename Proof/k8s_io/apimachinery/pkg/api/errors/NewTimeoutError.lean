/-
Proof of `Spec/k8s_io/apimachinery/pkg/api/errors/NewTimeoutError.lean`. Lean-first (no Rocq
counterpart).

The message (`fmt.Sprintf`), the new details, then the new error over the status literal.
-/
module

public import Spec.k8s_io.apimachinery.pkg.api.errors.NewTimeoutError
public import Perennial.Proof.fmt.Link

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.api.errors.Assumptions]

theorem apierrors.NewTimeoutError.wp_proof :
    apierrors.NewTimeoutError.spec (GF := GF) (hG := hG) := by
  intro message retry
  wp_start
  ihave #Pf : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %asl ⟨Hasl, -⟩
  wp_apply (_root_.Perennial.fmt.wp_Sprintf _ _ _ (DFrac.own 1) (by
    exact _root_.Perennial.fmt.ArgsWf.cons_string _ _ _root_.Perennial.fmt.ArgsWf.nil))
    $$ [$Hasl] as %s -
  (try wp_auto)
  wp_apply wp_alloc as %p Hp
  (try wp_auto)
  iapply HΦ
  iexists _, _
  iframe
  ipureintro
  exact ⟨rfl, rfl, rfl⟩

end proof

end EtcdGrove
end Perennial
