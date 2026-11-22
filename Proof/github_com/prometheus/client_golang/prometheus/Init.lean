/-
Package initialization of `github_com.prometheus.client_golang.prometheus`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact is `True`. Its initializer initializes its imports, runs the untranslated
initializers of its variables (`X.init`, axioms of the translation), which the trust-boundary axiom
`opaqueInitsOk` says run without panicking, and its translated ones: `defaultRegistry = NewRegistry()`
(stepped into) and `DefaultRegisterer`/`DefaultGatherer`, `defaultRegistry` converted to an interface; then
its `init()`, whose trusted model (route (b), notes/prom-registry.md) inserts the built-in collectors'
descriptor IDs, names and collector IDs into the registry's maps (`EtcdGrove.prometheus.wp_seed_insertAll`).
(Until 2026-11-22 `defaultRegistry.init`, `DefaultRegisterer.init` and `DefaultGatherer.init` were among
`opaqueInitsOk`, and `init.«0»` was the trust-boundary axiom `initFuncsOk`.)
-/
module

public import Proof.github_com.prometheus.client_golang.prometheus.PkgInit
public import Perennial.Proof.fmt.Link
public import Perennial.Proof.sync.Link
public import Perennial.Proof.time.Link
public import Proof.github_com.prometheus.client_model.go.Init
public import Proof.github_com.prometheus.client_golang.prometheus.Seed
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
namespace github_com.prometheus.client_golang.prometheus
variable [GooseExts] [GooseSemantics] [GooseInterp]
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.github_com.prometheus.client_golang.prometheus.Assumptions]

namespace github_com.prometheus.client_golang.prometheus

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.github_com.prometheus.client_golang.prometheus get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.prometheus.client_golang.prometheus }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := GoInterface) DefaultGatherer _ as HDefaultGatherer
  wp_apply wp_GlobalAlloc (V := GoInterface) DefaultRegisterer _ as HDefaultRegisterer
  wp_apply wp_GlobalAlloc (V := Loc) defaultRegistry _ as HdefaultRegistry
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.sync _root_.Perennial.sync.initialize'
      EtcdGrove.ExternalInit.sync _root_.Perennial.sync.wp_initialize' _ Hinit.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd4⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.fmt _root_.Perennial.fmt.initialize'
      EtcdGrove.ExternalInit.fmt _root_.Perennial.fmt.wp_initialize' _ Hinit.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply (_root_.Perennial.github_com.prometheus.client_model.go.wp_initialize'_lb _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.time _root_.Perennial.time.initialize'
      EtcdGrove.ExternalInit.time _root_.Perennial.time.wp_initialize' _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  wp_apply (opaqueInitsOk rmNamesForMemStatsMetrics.init (by mem_tac))
  wp_apply (opaqueInitsOk nativeHistogramBounds.init (by mem_tac))
  wp_apply (opaqueInitsOk DefBuckets.init (by mem_tac))
  wp_apply (opaqueInitsOk errBucketLabelNotAllowed.init (by mem_tac))
  wp_apply (opaqueInitsOk errInconsistentCardinality.init (by mem_tac))
  wp_apply (opaqueInitsOk separatorByteSlice.init (by mem_tac))
  -- translated initializer of defaultRegistry))
  try wp_auto
  wp_func_call
  wp_call
  try wp_auto
  wp_apply (wp_map_make1 (K := w64) (V := GoInterface) go.uint64 github_com.prometheus.client_golang.prometheus.Collector.ty) as %mC HmC
  try wp_auto
  wp_apply (wp_map_make1 (K := w64) (V := Unit) go.uint64 (go.GoType.StructType [])) as %mD HmD
  try wp_auto
  wp_apply (wp_map_make1 (K := GoString) (V := w64) go.string go.uint64) as %mN HmN
  try wp_auto
  -- translated initializer of DefaultRegisterer))
  -- translated initializer of DefaultGatherer))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk errQuantileLabelNotAllowed.init (by mem_tac))
  wp_apply (opaqueInitsOk CounterMetricTypePtr.init (by mem_tac))
  wp_apply (opaqueInitsOk GaugeMetricTypePtr.init (by mem_tac))
  wp_apply (opaqueInitsOk UntypedMetricTypePtr.init (by mem_tac))
  wp_apply (opaqueInitsOk labelsPool.init (by mem_tac))
  wp_apply (opaqueInitsOk V2.init (by mem_tac))
  -- the translated init.«0»
  wp_func_call
  wp_call
  try wp_auto
  simp only [EtcdGrove.prometheus.seed_Registry_eq, EtcdGrove.prometheus.seed_Collector_eq, EtcdGrove.prometheus.seed_defaultRegistry_eq]
  try wp_auto
  wp_apply (EtcdGrove.prometheus.wp_seed_insertAll (K := w64) (V := Unit) go.uint64 (fun id => (id, ())) github_com.prometheus.client_golang.prometheus.seed.descIDs) $$ HmD as HmD
  try wp_auto
  wp_apply (EtcdGrove.prometheus.wp_seed_insertAll (K := GoString) (V := w64) go.string (fun nd => nd) github_com.prometheus.client_golang.prometheus.seed.dims) $$ HmN as HmN
  try wp_auto
  wp_apply (EtcdGrove.prometheus.wp_seed_insertAll (K := w64) (V := GoInterface) go.uint64 (fun id => (id, (interface.nil : GoInterface))) github_com.prometheus.client_golang.prometheus.seed.collectorIDs) $$ HmC as HmC
  try wp_auto
  -- translated initializer of defaultRegistry))
  -- translated initializer of defaultRegistry))
  iframe Hown
  is_pkg_init_finish

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.github_com.prometheus.client_golang.prometheus get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.prometheus.client_golang.prometheus }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end github_com.prometheus.client_golang.prometheus

end init

end Perennial
