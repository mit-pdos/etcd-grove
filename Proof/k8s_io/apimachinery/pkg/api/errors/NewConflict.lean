/-
Proof of `apierrors.NewConflict` (`Spec/k8s_io/apimachinery/pkg/api/errors/NewConflict.lean`) over its
body (prove-k8s2, 2026-11-21; until then a trust-boundary axiom: its message `Sprintf`s an error,
`%v`, which Perennial's `Sprintf` model now formats under `fmt.argsOk`). Lean-first.
-/
module

public import Spec.k8s_io.apimachinery.pkg.api.errors.NewConflict
public import Spec.k8s_io.apimachinery.pkg.runtime.schema.GroupResource__String_ptr
public import Perennial.Proof.fmt.Link
public import Proof.fmt.SprintfPure

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
  have hset : ∀ a b c : GoInterface,
      ([a, GoInterface.nil, GoInterface.nil].set (sint.nat (W64 (0 + 1))) b).set
        (sint.nat (W64 (0 + 1 + 1))) c = [a, b, c] := by
    intro a b c
    have h1 : sint.nat (W64 (0 + 1)) = 1 := by word
    have h2 : sint.nat (W64 (0 + 1 + 1)) = 2 := by word
    rw [h1, h2]
    rfl
  rw [hset]
  iapply wp_fupd
  -- the message: two strings and `err` (nil, or by its `Error()`); `%q` of the name (`fmt-stage15`)
  cases err with
  | nil =>
    wp_apply (_root_.Perennial.fmt.wp_Sprintf go!"Operation cannot be fulfilled on %s %q: %v" [.lit go!"Operation cannot be fulfilled on ", .dir none _root_.Perennial.fmt.verb_s, .lit go!" ", .dir none _root_.Perennial.fmt.verb_q, .lit go!": ", .dir none _root_.Perennial.fmt.verb_v] _ _
        [.str _, .str _, .nil] (DFrac.own 1) (by fmt_encode) ?fits)
      $$ [$Pf $Hasl] as %s -
    case fits => fmt_fits
    · iapply (_root_.Perennial.fmt.PureArgs.isArgs (.str _ _ _ (.str _ _ _ (.nil_ _ _ .nil))))
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
  | ok ii =>
    unfold fmtErrorOkOrNil fmtErrorOk
    icases Herr with ⟨%hms, #Hs⟩
    wp_apply (_root_.Perennial.fmt.wp_Sprintf go!"Operation cannot be fulfilled on %s %q: %v" [.lit go!"Operation cannot be fulfilled on ", .dir none _root_.Perennial.fmt.verb_s, .lit go!" ", .dir none _root_.Perennial.fmt.verb_q, .lit go!": ", .dir none _root_.Perennial.fmt.verb_v] _ _
        [.str _, .str _, .method fun _ => True] (DFrac.own 1) (by fmt_encode) ?fits)
      $$ [$Pf $Hasl] as %s -
    case fits => fmt_fits
    · iapply BigSepL2.bigSepL2_cons.2
      isplitr; · simp only [_root_.Perennial.fmt.isArg]; ipureintro; rfl
      iapply BigSepL2.bigSepL2_cons.2
      isplitr; · simp only [_root_.Perennial.fmt.isArg]; ipureintro; rfl
      iapply BigSepL2.bigSepL2_cons.2
      isplitl
      · iapply (fmt.isArg_error ii hms.1 hms.2); iexact Hs
      · iapply BigSepL2.bigSepL2_nil.2; itrivial
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
