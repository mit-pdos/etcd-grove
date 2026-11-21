/-
Proof of `apierrors.NewConflict` (`Spec/k8s_io/apimachinery/pkg/api/errors/NewConflict.lean`) over its
body (prove-k8s2, 2026-11-21; until then a trust-boundary axiom: its message `Sprintf`s an error,
`%v`, which Perennial's `Sprintf` model now formats under `fmt.argsOk`). Lean-first.
-/
module

public import Spec.k8s_io.apimachinery.pkg.api.errors.NewConflict
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

/-- A string argument is well formed. -/
theorem argWf_string (x : GoString) :
    _root_.Perennial.fmt.ArgWf ⟨go.string, #x⟩ :=
  (_root_.Perennial.fmt.ArgsWf.cons_string x _ _root_.Perennial.fmt.ArgsWf.nil) _
    (List.mem_singleton_self _)

theorem NewConflict.wp_proof
    (wp_String : schema.GroupResource.String_ptr.spec (GF := GF) (hG := hG)) :
    NewConflict.spec (GF := GF) (hG := hG) := by
  intro gr name err
  wp_start as #Herr
  ihave #Pf : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_String $$ [$qualifiedResource] as %str qualifiedResource
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %asl ⟨Hasl, -⟩
  have hds : _root_.Perennial.fmt.fmtDirectives
      go!"Operation cannot be fulfilled on %s %q: %v" =
      some [⟨W8 115, false⟩, ⟨W8 113, false⟩, ⟨W8 118, false⟩] := by
    decide
  ihave Hargs : _root_.Perennial.fmt.argsOkAt (GF := GF) _root_.Perennial.fmt.methodVerbs
      [⟨W8 115, false⟩, ⟨W8 113, false⟩, ⟨W8 118, false⟩]
      [interface.mkOk go.string #str, interface.mkOk go.string #name, err] $$ [Herr]
  · simp only [_root_.Perennial.fmt.argsOkAt]
    isplitl []
    · unfold _root_.Perennial.fmt.argOkAt; ileft; ipureintro; exact argWf_string str
    isplitl []
    · unfold _root_.Perennial.fmt.argOkAt; ileft; ipureintro; exact argWf_string name
    isplitl [Herr]
    · cases err with
      | nil => unfold _root_.Perennial.fmt.argOkAt; itrivial
      | ok ii =>
        unfold _root_.Perennial.fmt.argOkAt
        iright; iright; ileft
        isplitr
        · ipureintro
          refine ⟨by decide, rfl, fun h => ?_⟩
          exact absurd h (by decide)
        · iexact Herr
    · itrivial
  ihave Hok := _root_.Perennial.fmt.argsOk_intro (GF := GF) (mv := _root_.Perennial.fmt.methodVerbs) hds $$ Hargs
  iapply wp_fupd
  wp_apply (_root_.Perennial.fmt.wp_Sprintf go!"Operation cannot be fulfilled on %s %q: %v" _
      [interface.mkOk go.string #str, interface.mkOk go.string #name, err] (DFrac.own 1))
    $$ [$Pf $Hasl $Hok] as %s -
  ipersist «$v3»
  imodintro
  iapply HΦ
  iexists _
  iframe
  isplitr
  · unfold statusDetailsAt; iright; iexists _; iframe «$v3»
    iapply (ownSlice_nil (V := k8s_io.apimachinery.pkg.apis.«meta».v1.StatusCause) DFrac.discard)
  ipureintro
  exact ⟨rfl, rfl, rfl⟩

end proof

end apierrors
end EtcdGrove
end Perennial
