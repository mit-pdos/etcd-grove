/-
Package initialization of `k8s_io.apimachinery.pkg.util.validation`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact is `True`. Its initializer initializes its imports and runs the untranslated
initializers of its variables (`X.init`, axioms of the translation), which the
trust-boundary axiom `opaqueInitsOk` says run without panicking.
-/
module

public import Proof.k8s_io.kubernetes.Base
public import Proof.runtime.PkgInitExt

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
namespace k8s_io.apimachinery.pkg.util.validation
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `k8s_io.apimachinery.pkg.util.validation`'s untranslated variable initializers run.**
Goose translates them names-only, so each `X.init` is an axiom of the translation; Go
runs them at program start, and etcd starts, so each returns without panicking.
Satisfiable whatever the semantics (the `X.init`s are uninterpreted constants). -/
axiom opaqueInitsOk :
    ∀ v ∈ ([IsQualifiedName.init,
        httpPathRegexp.init,
        IsValidLabelValue.init,
        dns1123LabelRegexp.init,
        dns1123SubdomainRegexp.init,
        dns1123SubdomainRegexpWithUnderscore.init,
        dns1035LabelRegexp.init,
        IsCIdentifier.init,
        portNameCharsetRegex.init,
        portNameOneLetterRegexp.init,
        percentRegexp.init,
        httpHeaderNameRegexp.init,
        envVarNameRegexp.init,
        configMapKeyRegexp.init] : List val),
    {{ (True : IProp GF) }} (App (Val v) (Val #())) {{ RET #(); True }}

end k8s_io.apimachinery.pkg.util.validation
end opaqueInits

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.k8s_io.apimachinery.pkg.util.validation.Assumptions]

namespace k8s_io.apimachinery.pkg.util.validation

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.k8s_io.apimachinery.pkg.util.validation get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.validation }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply (opaqueInitsOk IsQualifiedName.init (by mem_tac))
  wp_apply (opaqueInitsOk httpPathRegexp.init (by mem_tac))
  wp_apply (opaqueInitsOk IsValidLabelValue.init (by mem_tac))
  wp_apply (opaqueInitsOk dns1123LabelRegexp.init (by mem_tac))
  wp_apply (opaqueInitsOk dns1123SubdomainRegexp.init (by mem_tac))
  wp_apply (opaqueInitsOk dns1123SubdomainRegexpWithUnderscore.init (by mem_tac))
  wp_apply (opaqueInitsOk dns1035LabelRegexp.init (by mem_tac))
  wp_apply (opaqueInitsOk IsCIdentifier.init (by mem_tac))
  wp_apply (opaqueInitsOk portNameCharsetRegex.init (by mem_tac))
  wp_apply (opaqueInitsOk portNameOneLetterRegexp.init (by mem_tac))
  wp_apply (opaqueInitsOk percentRegexp.init (by mem_tac))
  wp_apply (opaqueInitsOk httpHeaderNameRegexp.init (by mem_tac))
  wp_apply (opaqueInitsOk envVarNameRegexp.init (by mem_tac))
  wp_apply (opaqueInitsOk configMapKeyRegexp.init (by mem_tac))
  iframe Hown
  is_pkg_init_finish

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.k8s_io.apimachinery.pkg.util.validation get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.validation }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end k8s_io.apimachinery.pkg.util.validation

end init

end Perennial
