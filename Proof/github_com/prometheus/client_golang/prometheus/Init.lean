/-
Package initialization of `github_com.prometheus.client_golang.prometheus`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact is `True`. Its initializer initializes its imports and runs the untranslated
initializers of its variables (`X.init`, axioms of the translation), which the
trust-boundary axiom `opaqueInitsOk` says run without panicking.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.Base

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
namespace github_com.prometheus.client_golang.prometheus
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `github_com.prometheus.client_golang.prometheus`'s untranslated variable initializers run.**
Goose translates them names-only, so each `X.init` is an axiom of the translation; Go
runs them at program start, and etcd starts, so each returns without panicking.
Satisfiable whatever the semantics (the `X.init`s are uninterpreted constants). -/
axiom opaqueInitsOk :
    ∀ v ∈ ([rmNamesForMemStatsMetrics.init,
        nativeHistogramBounds.init,
        DefBuckets.init,
        errBucketLabelNotAllowed.init,
        errInconsistentCardinality.init,
        separatorByteSlice.init,
        defaultRegistry.init,
        DefaultRegisterer.init,
        DefaultGatherer.init,
        «_».init,
        errQuantileLabelNotAllowed.init,
        CounterMetricTypePtr.init,
        GaugeMetricTypePtr.init,
        UntypedMetricTypePtr.init,
        labelsPool.init,
        V2.init] : List val),
    {{ (True : IProp GF) }} (App (Val v) (Val #())) {{ RET #(); True }}

end github_com.prometheus.client_golang.prometheus
end opaqueInits

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.github_com.prometheus.client_golang.prometheus.Assumptions]

namespace github_com.prometheus.client_golang.prometheus

theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.github_com.prometheus.client_golang.prometheus get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.prometheus.client_golang.prometheus }} := by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply (opaqueInitsOk rmNamesForMemStatsMetrics.init (by mem_tac))
  wp_apply (opaqueInitsOk nativeHistogramBounds.init (by mem_tac))
  wp_apply (opaqueInitsOk DefBuckets.init (by mem_tac))
  wp_apply (opaqueInitsOk errBucketLabelNotAllowed.init (by mem_tac))
  wp_apply (opaqueInitsOk errInconsistentCardinality.init (by mem_tac))
  wp_apply (opaqueInitsOk separatorByteSlice.init (by mem_tac))
  wp_apply (opaqueInitsOk defaultRegistry.init (by mem_tac))
  wp_apply (opaqueInitsOk DefaultRegisterer.init (by mem_tac))
  wp_apply (opaqueInitsOk DefaultGatherer.init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk errQuantileLabelNotAllowed.init (by mem_tac))
  wp_apply (opaqueInitsOk CounterMetricTypePtr.init (by mem_tac))
  wp_apply (opaqueInitsOk GaugeMetricTypePtr.init (by mem_tac))
  wp_apply (opaqueInitsOk UntypedMetricTypePtr.init (by mem_tac))
  wp_apply (opaqueInitsOk labelsPool.init (by mem_tac))
  wp_apply (opaqueInitsOk V2.init (by mem_tac))
  iframe Hown
  is_pkg_init_finish


end github_com.prometheus.client_golang.prometheus

end init

end Perennial
