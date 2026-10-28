/-
`handleAnyWatch(ctx, start, w, store, expectedType, expectedGVK, name, expectedTypeName,
setLastSyncResourceVersion, exitOnWatchListBookmarkReceived, clock, errCh)` (`reflector.go:972`): the
reflector's watch loop. **A named hypothesis, gap D4** (`notes/k8s-daemonset-goose.md`: a labeled
`break` out of the `select` inside the `for`, which the pinned Goose rejects; names only): `?` in
`etc/link-lean-first-k8scache.txt`, a hypothesis of every result that reaches it. Phase 4 of
`notes/k8s-daemonset-plan.md`, fifth round.

**What the code does** (read 2026-10-27 at the pin), for the case the reflector's `watch` calls it
in (`handleWatch`: `exitOnWatchListBookmarkReceived` false; the store the informer's `*RealFIFO`;
`expectedGVK` nil, as `getExpectedGVKFromObject` gives for a typed object; the watch the model
API server's, all namespaces): it loops on a `select` over `ctx.Done()` (returns
`errorStopRequested`), `errCh` (returns the error received), `w.ResultChan()` and the warning
ticker's `C()` (a nil channel: the no-op ticker of `exitOnWatchListBookmarkReceived = false`). For
each event received:
* an `ERROR` event returns `apierrors.FromObject`; an event whose object's `reflect.TypeOf` is not
  `expectedType`, or that is an unstructured `Table`, or that `meta.Accessor` rejects, is skipped
  with a logged error. Neither happens here: the model sends `ADDED`/`MODIFIED`/`DELETED`/
  `BOOKMARK` events whose object is a `*T` of the watched resource (`evOk`), whose `TypeOf` is
  `expectedType` (`typeOfOk`). So each event's step (`evStepOk`, the caller's) gives the type
  facts first, which the hypothesis uses to know the event is not skipped.
* `ADDED`/`MODIFIED`/`DELETED` call the store's `Add`/`Update`/`Delete(event.Object)`,
  `BOOKMARK` the store's `Bookmark(rv)` (a `ReflectorBookmarkStore`; `rv` the object's
  `GetResourceVersion()`); each through the FIFO's logically atomic update (`evAct`), its error
  only logged; then `setLastSyncResourceVersion(rv, eventReceivedBesidesAdded)` (`cbOk`).
* when the result channel closes, it returns (`nil`, or a `VeryShortWatchError` after a watch
  shorter than a second with no event); a deferred `w.Stop()` (`stopWatcher` stays true).
So the caller's state `L` follows the watch's consumer side (`watchCons`) event by event, and
comes back at whatever event the loop stopped at; the returned error is any.
-/
module

public import Proof.k8s_io.client_go.tools.cache.RefWatchDefs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI k8s_io.client_go.tools.cache apimodel

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- **`handleAnyWatch(...)`** on the model's watch `w` (consumer side after `n` events at `p`) into
the FIFO `f`, with the caller's per-event step (`evStepOk`) and callback (`cbOk`): back to the
caller's state `L` at the watch's consumer side where it stopped. -/
abbrev handleAnyWatch.spec : Prop :=
  ∀ (ctx : GoInterfaceOk) (dch : GoChan) (γd : ChanNames) (start : time.Time) (w : GoInterface)
    (γa : ApiNames) (γw : WatchNames) (r : Res) (bm : Bool) (inits : List Obj)
    (f : Loc) (γ : FifoNames) (OK : GoInterface → IProp GF) (et : reflect.Type')
    (name tname : GoString) (cb : GoFunc) (clk : k8s_io.utils.clock.RealClock) (errCh : GoChan)
    (n : Nat) (p : Pos') (L : Nat → Pos' → IProp GF) (C : Nat → Pos' → GoString → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ stableCtx ctx dch γd ∗
      watchAt w γa γw r go!"" bm inits ∗ watchCons γw n p ∗ L n p ∗ isFIFO f γ OK ∗
      typeOfOk et r ∗ errChOk errCh ∗ evStepOk γa γw r bm inits γ OK L C ∗ cbOk cb C L }}
    (App (App (App (App (App (App (App (App (App (App (App (App
      (Val (@! k8s_io.client_go.tools.cache.handleAnyWatch))
      (Val #(GoInterface.ok ctx))) (Val #start)) (Val #w))
      (Val #(interface.mkOk (go.GoType.PointerType RealFIFO.ty) #f : ReflectorStore)))
      (Val #et)) (Val #(null : Loc))) (Val #name)) (Val #tname)) (Val #cb)) (Val #false))
      (Val #(interface.mkOk k8s_io.utils.clock.RealClock.ty #clk : k8s_io.utils.clock.Clock)))
      (Val #errCh))
  {{ (b : Bool) (err : GoInterface), RET (PairV #b #err);
      ∃ (n' : Nat) (p' : Pos'), watchCons γw n' p' ∗ L n' p' }}

end spec

end cache
end EtcdGrove
end Perennial
