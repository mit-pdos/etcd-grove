/-
Package initialization of `k8s_io.apiserver.pkg.storage.cacher.metrics`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`cacherMetricsInit`, `storage/cacher/Base.lean`): `WatchCacheReadWait` holds a
histogram vector of the labels `group` and `resource`. Its initializer runs its variables'
untranslated initializers (`metrics.go`); the trust-boundary axiom `WatchCacheReadWait_init` states
the one the fact reads (`compbasemetrics.NewHistogramVec(..., []string{"group", "resource"})`),
`opaqueInitsOk` the others.
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.cacher.Base
public import Proof.k8s_io.component_base.metrics.Init
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
namespace k8s_io.apiserver.pkg.storage.cacher.metrics
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `k8s_io.apiserver.pkg.storage.cacher.metrics`'s untranslated variable initializers run.**
Goose translates them names-only, so each `X.init` is an axiom of the translation; Go
runs them at program start, and etcd starts, so each returns without panicking.
Satisfiable whatever the semantics (the `X.init`s are uninterpreted constants). -/
axiom opaqueInitsOk :
    ∀ v ∈ ([dispatchStages.init,
        listCacheCount.init,
        listCacheNumFetched.init,
        listCacheNumReturned.init,
        InitCounter.init,
        EventsReceivedCounter.init,
        EventsCounter.init,
        TerminatedWatchersCounter.init,
        watchCacheResourceVersion.init,
        watchCacheCapacityIncreaseTotal.init,
        watchCacheCapacityDecreaseTotal.init,
        WatchCacheCapacity.init,
        WatchCacheInitializations.init,
        WatchCacheInitializationErrors.init,
        WatchCacheInitializationDuration.init,
        ConsistentReadTotal.init,
        StorageConsistencyCheckTotal.init,
        WatchShardsTotal.init,
        WatchFilteredEventsTotal.init,
        DispatchStageDuration.init] : List val),
    {{ (True : IProp GF) }} (App (Val v) (Val #())) {{ RET #(); True }}

/-- `WatchCacheReadWait = compbasemetrics.NewHistogramVec(..., []string{"group", "resource"})`
(`metrics.go`): a `*HistogramVec` with those labels (`kmetrics.vecLabels`). -/
axiom WatchCacheReadWait_init :
    {{ (True : IProp GF) }} (App (Val WatchCacheReadWait.init) (Val #()))
    {{ RET #(); ∃ v : Loc, globalAddr WatchCacheReadWait ↦ v ∗ ⌜EtcdGrove.kmetrics.vecLabels v [go!"group", go!"resource"]⌝ }}

end k8s_io.apiserver.pkg.storage.cacher.metrics
end opaqueInits

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.k8s_io.apiserver.pkg.storage.cacher.metrics.Assumptions]

namespace k8s_io.apiserver.pkg.storage.cacher.metrics

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.k8s_io.apiserver.pkg.storage.cacher.metrics get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.cacher.metrics }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iapply wp_fupd
  wp_apply (_root_.Perennial.k8s_io.component_base.metrics.wp_initialize'_lb _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  wp_apply (opaqueInitsOk dispatchStages.init (by mem_tac))
  wp_apply (opaqueInitsOk listCacheCount.init (by mem_tac))
  wp_apply (opaqueInitsOk listCacheNumFetched.init (by mem_tac))
  wp_apply (opaqueInitsOk listCacheNumReturned.init (by mem_tac))
  wp_apply (opaqueInitsOk InitCounter.init (by mem_tac))
  wp_apply (opaqueInitsOk EventsReceivedCounter.init (by mem_tac))
  wp_apply (opaqueInitsOk EventsCounter.init (by mem_tac))
  wp_apply (opaqueInitsOk TerminatedWatchersCounter.init (by mem_tac))
  wp_apply (opaqueInitsOk watchCacheResourceVersion.init (by mem_tac))
  wp_apply (opaqueInitsOk watchCacheCapacityIncreaseTotal.init (by mem_tac))
  wp_apply (opaqueInitsOk watchCacheCapacityDecreaseTotal.init (by mem_tac))
  wp_apply (opaqueInitsOk WatchCacheCapacity.init (by mem_tac))
  wp_apply (opaqueInitsOk WatchCacheInitializations.init (by mem_tac))
  wp_apply (opaqueInitsOk WatchCacheInitializationErrors.init (by mem_tac))
  wp_apply (opaqueInitsOk WatchCacheInitializationDuration.init (by mem_tac))
  wp_apply WatchCacheReadWait_init as ⟨%vWatchCacheReadWait, HWatchCacheReadWait, %LWatchCacheReadWait⟩
  wp_apply (opaqueInitsOk ConsistentReadTotal.init (by mem_tac))
  wp_apply (opaqueInitsOk StorageConsistencyCheckTotal.init (by mem_tac))
  wp_apply (opaqueInitsOk WatchShardsTotal.init (by mem_tac))
  wp_apply (opaqueInitsOk WatchFilteredEventsTotal.init (by mem_tac))
  wp_apply (opaqueInitsOk DispatchStageDuration.init (by mem_tac))
  ipersist HWatchCacheReadWait
  iframe Hown
  imodintro
  isplitr
  · ipureintro
    exact isPanic_intoVal _
  is_pkg_init_finish
  try (isplitl []; · (imodintro; itrivial))
  imodintro
  iexists _
  iframe HWatchCacheReadWait
  ipureintro
  exact LWatchCacheReadWait

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.k8s_io.apiserver.pkg.storage.cacher.metrics get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.cacher.metrics }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end k8s_io.apiserver.pkg.storage.cacher.metrics

end init

end Perennial
