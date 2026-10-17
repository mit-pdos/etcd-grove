/-
Package initialization of `github_com.Masterminds.semver.v3`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact is `True`. Its initializer initializes its imports and runs the untranslated
initializers of its variables (`X.init`, axioms of the translation), which the
trust-boundary axiom `opaqueInitsOk` says run without panicking.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.lease.Base

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial

/-- `x ∈ [a, ..., x, ...]`, linear in the list (`simp` overflows on the long ones). -/
local macro "mem_tac" : tactic =>
  `(tactic| repeat (first | exact List.Mem.head _ | apply List.Mem.tail))

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section opaqueInits
namespace github_com.Masterminds.semver.v3
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `github_com.Masterminds.semver.v3`'s untranslated variable initializers run.**
Goose translates them names-only, so each `X.init` is an axiom of the translation; Go
runs them at program start, and etcd starts, so each returns without panicking.
Satisfiable whatever the semantics (the `X.init`s are uninterpreted constants). -/
axiom opaqueInitsOk :
    ∀ v ∈ ([ErrConstraintTooLong.init,
        ErrTooManyConstraintGroups.init,
        CoerceNewVersion.init,
        DetailedNewVersionErrors.init,
        ErrInvalidSemVer.init,
        ErrEmptyString.init,
        ErrInvalidCharacters.init,
        ErrSegmentStartsZero.init,
        ErrInvalidMetadata.init,
        ErrInvalidPrerelease.init,
        ErrVersionTooLong.init] : List val),
    {{ (True : IProp GF) }} (App (Val v) (Val #())) {{ RET #(); True }}

end github_com.Masterminds.semver.v3
end opaqueInits

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.github_com.Masterminds.semver.v3.Assumptions]

namespace github_com.Masterminds.semver.v3

theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.github_com.Masterminds.semver.v3 get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.Masterminds.semver.v3 }} := by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply (opaqueInitsOk ErrConstraintTooLong.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrTooManyConstraintGroups.init (by mem_tac))
  wp_apply (opaqueInitsOk CoerceNewVersion.init (by mem_tac))
  wp_apply (opaqueInitsOk DetailedNewVersionErrors.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrInvalidSemVer.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrEmptyString.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrInvalidCharacters.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrSegmentStartsZero.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrInvalidMetadata.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrInvalidPrerelease.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrVersionTooLong.init (by mem_tac))
  iframe Hown
  is_pkg_init_finish


end github_com.Masterminds.semver.v3

end init

end Perennial
