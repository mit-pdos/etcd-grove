/-
Proof of `apierrors.NewInternalError` (`Spec/k8s_io/apimachinery/pkg/api/errors/NewInternalError.lean`)
over its body (prove-k8s3, 2026-11-21; until then a trust-boundary axiom: its message `Sprintf`s an
error, `%v`, which Perennial's `Sprintf` model formats under `fmt.argsOk`). Lean-first.
-/
module

public import Spec.k8s_io.apimachinery.pkg.api.errors.NewInternalError
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

theorem NewInternalError.wp_proof : NewInternalError.spec (GF := GF) (hG := hG) := by
  intro err
  wp_start as ⟨%ei, %He, #Hstr, %Hms⟩
  subst He
  ihave #Pf : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  wp_auto
  wp_bind (App (Val #(methods ei.ty go!"Error" ei.v)) (Val #()))
  ihave #Hs := Hstr
  iunfold _root_.Perennial.fmt.stringMethodSpec at Hs
  iapply Hs
  inext
  iintro %msg
  wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %csl ⟨Hcsl, -⟩
  wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %asl ⟨Hasl, -⟩
  have hds : _root_.Perennial.fmt.fmtDirectives go!"Internal error occurred: %v" =
      some [⟨W8 118, false⟩] := by
    decide
  ihave Hargs : _root_.Perennial.fmt.argsOkAt (GF := GF) _root_.Perennial.fmt.methodVerbs
      [⟨W8 118, false⟩] [GoInterface.ok ei] $$ []
  · simp only [_root_.Perennial.fmt.argsOkAt]
    isplitl []
    · unfold _root_.Perennial.fmt.argOkAt
      iright; iright; ileft
      isplitr
      · ipureintro
        refine ⟨by decide, rfl, fun h => ?_⟩
        exact absurd h (by decide)
      · unfold _root_.Perennial.fmt.argOk
        iright; ileft
        iframe Hstr
        ipureintro; exact Hms
    · itrivial
  ihave Hok := _root_.Perennial.fmt.argsOk_intro (GF := GF) (mv := _root_.Perennial.fmt.methodVerbs) hds $$ Hargs
  iapply wp_fupd
  wp_apply (_root_.Perennial.fmt.wp_Sprintf go!"Internal error occurred: %v" _
      [GoInterface.ok ei] (DFrac.own 1))
    $$ [$Pf $Hasl $Hok] as %s -
  ipersist «$v3»
  ipersist Hcsl
  imodintro
  iapply HΦ
  iexists _, _
  iframe
  isplitr
  · unfold statusDetailsAt; iright; iexists _; iframe «$v3»
    iexact Hcsl
  ipureintro
  exact ⟨rfl, rfl, rfl, rfl⟩

end proof

end apierrors
end EtcdGrove
end Perennial
