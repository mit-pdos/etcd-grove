/-
Proof of `Spec/k8s_io/apimachinery/pkg/api/errors/NewTimeoutError.lean`. Lean-first (no Rocq
counterpart).

The message (`fmt.Sprintf`), the new details, then the new error over the status literal.
-/
module

public import Spec.k8s_io.apimachinery.pkg.api.errors.NewTimeoutError
public import Perennial.Proof.fmt.Link
public import Proof.fmt.SprintfPure

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
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
  wp_apply (fmt.wp_Sprintf_pure _root_.Perennial.fmt.wp_Sprintf go!"Timeout: %s"
    [.lit go!"Timeout: ", .dir none _root_.Perennial.fmt.verb_s]
    _ _ _ _ (by fmt_encode) (by fmt_fits) (.str _ _ _ .nil))
    $$ [$Hasl] as %s -
  (try wp_auto)
  irename «$r0» => Hp
  generalize «$r0_ptr» = p at *
  (try wp_auto)
  iapply HΦ
  iexists _, _
  iframe
  isplitr
  · ipureintro; rfl
  isplitr
  · ipureintro
    exact ⟨rfl, rfl, rfl⟩
  ipureintro
  rfl

end proof

end EtcdGrove
end Perennial
