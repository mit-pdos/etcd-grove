/-
Package initialization of `k8s_io.component_base.metrics`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact is `True`. Its initializer initializes its imports, runs the untranslated
initializers of its variables (`X.init`, axioms of the translation), which the
trust-boundary axiom `opaqueInitsOk` says run without panicking, and its untranslated
`init` functions, which the trust-boundary axiom `initFuncsOk` says return.
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.cacher.Base
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
namespace k8s_io.component_base.metrics
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `k8s_io.component_base.metrics`'s untranslated variable initializers run.**
Goose translates them names-only, so each `X.init` is an axiom of the translation; Go
runs them at program start, and etcd starts, so each returns without panicking.
Satisfiable whatever the semantics (the `X.init`s are uninterpreted constants). -/
axiom opaqueInitsOk :
    ∀ v ∈ ([DefBuckets.init,
        «_».init,
        «_».init,
        «_».init,
        «_».init,
        «_».init,
        «_».init,
        «_».init,
        «_».init,
        «_».init,
        «_».init,
        noopCounterVec.init,
        noopHistogramVec.init,
        noopTimingHistogramVec.init,
        noopGaugeVec.init,
        noop.init,
        disabledMetrics.init,
        disabledMetricsTotal.init,
        hiddenMetricsTotal.init,
        cardinalityEnforcementUnexpectedCategorizationsTotal.init,
        labelValueAllowLists.init,
        defObjectives.init,
        processStartTime.init,
        registeredMetricsTotal.init,
        BuildVersion.init,
        «_».init,
        «_».init,
        «_».init,
        «_».init,
        «_».init,
        «_».init,
        buildInfo.init,
        versionRe.init,
        errNotRegistered.init] : List val),
    {{ (True : IProp GF) }} (App (Val v) (Val #())) {{ RET #(); True }}

/-- **The trust boundary: `k8s_io.component_base.metrics`'s untranslated `init` functions return.** Goose
names a package's `func init()`s `init.<k>`, as gc does, and translates them names-only
here, so the model does not unfold them (`@! init.<k>`: the semantics' `functions`, which
the package's `Assumptions` do not constrain for them). Go runs them at program start, and
etcd starts, so each returns without panicking. A fact about the Go code, as the axioms of
other names-only functions (`EtcdGrove.prometheus.MustRegister.wp_proof`). -/
axiom initFuncsOk :
    ∀ f ∈ ([init.«0»] : List GoString),
    {{ (True : IProp GF) }} (App (Val (@! f)) (Val #())) {{ RET #(); True }}

end k8s_io.component_base.metrics
end opaqueInits

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.k8s_io.component_base.metrics.Assumptions]

namespace k8s_io.component_base.metrics

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.k8s_io.component_base.metrics get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.k8s_io.component_base.metrics }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply (opaqueInitsOk DefBuckets.init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk noopCounterVec.init (by mem_tac))
  wp_apply (opaqueInitsOk noopHistogramVec.init (by mem_tac))
  wp_apply (opaqueInitsOk noopTimingHistogramVec.init (by mem_tac))
  wp_apply (opaqueInitsOk noopGaugeVec.init (by mem_tac))
  wp_apply (opaqueInitsOk noop.init (by mem_tac))
  wp_apply (opaqueInitsOk disabledMetrics.init (by mem_tac))
  wp_apply (opaqueInitsOk disabledMetricsTotal.init (by mem_tac))
  wp_apply (opaqueInitsOk hiddenMetricsTotal.init (by mem_tac))
  wp_apply (opaqueInitsOk cardinalityEnforcementUnexpectedCategorizationsTotal.init (by mem_tac))
  wp_apply (opaqueInitsOk labelValueAllowLists.init (by mem_tac))
  wp_apply (opaqueInitsOk defObjectives.init (by mem_tac))
  wp_apply (opaqueInitsOk processStartTime.init (by mem_tac))
  wp_apply (opaqueInitsOk registeredMetricsTotal.init (by mem_tac))
  wp_apply (opaqueInitsOk BuildVersion.init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk buildInfo.init (by mem_tac))
  wp_apply (opaqueInitsOk versionRe.init (by mem_tac))
  wp_apply (opaqueInitsOk errNotRegistered.init (by mem_tac))
  wp_apply (initFuncsOk init.«0» (by mem_tac))
  iframe Hown
  is_pkg_init_finish

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.k8s_io.component_base.metrics get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.k8s_io.component_base.metrics }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end k8s_io.component_base.metrics

end init

end Perennial
