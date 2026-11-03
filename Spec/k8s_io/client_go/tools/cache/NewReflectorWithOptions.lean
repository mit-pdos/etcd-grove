/-
`cache.NewReflectorWithOptions(lw, expectedType, store, options)` (`reflector.go`): a reflector
over the list-watch (`ToListerWatcherWithContext(lw)`: `lwOk` carries over), the expected type
`reflect.TypeOf(expectedType)` (`typeOfOk`), the store (the FIFO), resync `0`, a real clock, the
default backoff (its `DelayWithReset`: `delayOk`), watch-list off (`WatchListClient` reads
`false`, `Main`'s gates), no version yet. Lean-first; the DaemonSet run's track A.
-/
module

public import Spec.k8s_io.client_go.tools.cache.Reflector__watch

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI apimodel cache informer k8s_io.client_go.tools.cache

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]
variable [ctx_sem : _root_.Perennial.context.Assumptions]
/-- **The reflector's fields its maker may still set** (owned; `controller.RunWithContext` sets
`ShouldResync`, `WatchListPageSize`, the error handler, then they are read-only, `reflFixed2`). -/
def reflRest (r : Loc) (dh : GoFunc) : IProp GF :=
  iprop(∃ (name td : GoString) (ps : w64) (md : time.Duration) (sr weh : GoFunc),
    r.[Reflector, go!"delayHandler"] ↦□ dh ∗
    r.[Reflector, go!"name"] ↦ name ∗
    r.[Reflector, go!"typeDescription"] ↦ td ∗
    r.[Reflector, go!"WatchListPageSize"] ↦ ps ∗
    r.[Reflector, go!"MaxInternalErrorRetryDuration"] ↦ md ∗
    r.[Reflector, go!"ShouldResync"] ↦ sr ∗
    r.[Reflector, go!"watchErrorHandler"] ↦ weh)

/-- **`NewReflectorWithOptions(lw, obj, fifo, options)`**: see the file header. -/
abbrev NewReflectorWithOptions.spec : Prop :=
  ∀ (lw : GoInterfaceOk) (q f : Loc) (o : ReflectorOptions) (γa : ApiNames)
    (cfg : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Config) (res : Res),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ lwOk lw γa cfg res ∗
      ⌜o.ResyncPeriod' = W64 0 ∧ o.Backoff' = null⌝ ∗
      (⌜o.Logger' = null⌝ ∨ ∃ lg : github_com.go_logr.logr.Logger, o.Logger' ↦□ lg) }}
    (App (App (App (App (Val (@! NewReflectorWithOptions)) (Val #(GoInterface.ok lw)))
      (Val #(interface.mkOk (go.GoType.PointerType (resObjTy res)) #q : GoInterface)))
      (Val #(interface.mkOk (go.GoType.PointerType RealFIFO.ty) #f : ReflectorStore))) (Val #o))
  {{ (r : Loc), RET #r; ∃ (lw' : GoInterfaceOk) (et : reflect.Type') (dh : GoFunc),
      reflFixed1 r f lw' et ∗ lwOk lw' γa cfg res ∗ typeOfOk et res ∗ delayOk dh ∗
      reflRest r dh ∗ reflOwn r go!"" false ∗ reflMisc r }}

end spec

end cache
end EtcdGrove
end Perennial
