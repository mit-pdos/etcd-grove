/-
Lean-first (no Rocq counterpart).

# k8s 7f-5a-D: the Draft of the etcd3 watcher's serial branch (UNLINKED; hard stop S3)

Statements only, no proofs; `notes/k8s-7f5a-draft.md` explains each in plain words. Nothing imports
this file. After etcd-grove-81's review, its definitions move to `WatchDefs.lean` (the vocabulary)
and `Spec/k8s_io/apiserver/pkg/storage/etcd3/store__Watch.lean` (the triple), and this file goes.

1. **The ideal stream** (pure, generic in the store's object type, over etcd's history read as a
   `KVState`): `KWEv` (a watch event as the consumer sees it), `kEvOfL` (an etcd event's watch event,
   as `transform` computes it from the event and the key's record at the revision before),
   `kInitialL` (a watch-list's initial events), `KTail` (the events of a watch from a cursor, with
   progress bookmarks), `kModeOf` (what the request asks: initial events, the initial-events-end
   bookmark, the requested revision), **`kStreamOk`** (the events received, Error events removed,
   are a prefix of the ideal stream from a start point), **`kStreamSub`** (a subsequence of it) and
   **`kStartOk`** (the start point is the revision of a state the caller's read update fired at,
   or the requested one).
2. **The consumer's view**, `k8sWatch`: `ResultChan()` returns an SPSC channel (`isSpsc`, the
   consumer's half) whose `i`-th element is a `watch.Event` (`wevAt`) and carries the persistent
   fact that the first `i + 1` events' models are `kStreamSub`, and `kStreamOk` unless the watch is
   no longer live (`kCancelled`: stopped by the consumer, or its context done); `Stop()` takes
   `kLive` (or `kStopped`) and gives `kStopped`.
3. **`store.Watch.spec`** (`Draft.store.Watch.spec`).
4. **The protocol** (the proof's ghost state, internal): `KRaw` (an `*event` the producer queues),
   `kRawStreamOk`/`kRawStreamSub`, `kInElem` (the `incomingEventChan` SPSC's element), `kResInv`
   (the `resultChan`'s two producers: the producer token in an invariant), `kCancelPD` (`wc.cancel`'s
   Done proposition).
5. **Trusted texts T5-f** as statements (`def … .spec : Prop`, no axiom; the axioms land in 7f-5a-P):
   `klog.Warningf.spec` (`klog.Errorf.spec`'s restricted form), `mvccpb.Event_EventType.String.spec`.
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.WatchDefs
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.CompactorDefs
public import Proof.k8s_io.apiserver.pkg.storage.SelDefs
public import Proof.k8s_io.apiserver.pkg.audit.CtxKeys
public import Proof.go_etcd_io.etcd.client.v3.WatchStateDefs
public import Spec.k8s_io.klog.v2.Args

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s
namespace Draft

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver


/-! ## 3. The triple -/

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

/-- **`(*store).Watch(ctx, key, opts)`** (`store.go:1142-1152`; see `notes/k8s-7f5a-draft.md` §3):
a watch of the prepared key's scope from the parsed resource version `n`, with `WatchList` on,
`EtcdRangeStream` off and (temporarily, Q6) `ConcurrentWatchObjectDecode` off, under the caller's
context (an `isContext` with grpc's outgoing metadata, client errors and the Kubernetes keys), with
the caller's read updates `Q lb` (`Q lb σ`: a state of one history at revision at least `lb`;
`Q σ.rev` handed out after a firing at `σ`), returns an error (only `getCurrentStorageRV`'s, for RV 0 with `SendInitialEvents = false`), or `nil`
and the consumer's view
(`k8sWatch`, live while the caller has not stopped it and its context `cd` is not done). No thread
token: the watch's three goroutines get theirs at their `go` statements. -/
abbrev store.Watch.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (Obj : Type) [DecidableEq Obj] [Pos.Countable Obj] (sp : Loc) (c : StoreCfg GF Obj)
    (W : WatchSpec Obj) (γk : KVNames) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (key : GoString) (opts : k8s_io.apiserver.pkg.storage.ListOptions) (k : GoString) (n : w64)
    (sie : Option Bool) (sel : Obj → Bool) (emp : Bool) (Q : Nat → KVState → IProp GF),
  (∀ lb σ, Q lb σ ⊢ ⌜lb ≤ σ.rev ∧ kvWf c σ ∧ kvWfHist c σ ∧ kvKeysShort σ⌝) →
  (∀ lb lb' σ σ', Q lb σ ∗ Q lb' σ' ⊢ ⌜kvSameHist σ σ'⌝) →
  (∀ x ∈ c.ms, noRefusalAt x.addr) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗ isStore sp c ∗
      storeWatchOk sp c W γk ∗
      ⌜prepareKeyM c.resourcePrefix key opts.Recursive' = some k ∧
        (c.pathPrefix ++ k).length ≤ opKeyMax ∧ c.S.parseRV opts.ResourceVersion' = some n ∧
        uint.Z n < 2 ^ 63 - 1 ∧ opts.ProgressNotify' = false ∧ opts.RecordTimestamps' = false⌝ ∗
      sendInitIs opts.SendInitialEvents' sie ∗ selPredOk c.S opts.Predicate' sel emp ∗
      watchListOn ∗ rangeStreamOff ∗ concurrentDecodeOff ∗
      context.isContext ci cd ∗ metadata.outgoingCtxOkC ci ∗ ctxErrClient ci cd ∗
      k8sctx.k8sCtxOk ci ∗
      ⌜threadBound GF ≤ 2 ^ 30 - 1⌝ ∗
      (|==> readAus c γk (Q 0)) ∗
      (□ ∀ lb σ, □ Q lb σ -∗ |==> readAus c γk (Q σ.rev)) }}
    (App (App (App (Val (sp @!! go.GoType.PointerType
      k8s_io.apiserver.pkg.storage.etcd3.store.ty @!! go!"Watch")) (Val #(GoInterface.ok ci)))
      (Val #key)) (Val #opts))
  {{ (wi err : GoInterface), RET (PairV #wi #err);
      ⌜err ≠ GoInterface.nil ∧ sie = some false ∧ uint.nat n = 0⌝ ∨
      (⌜err = GoInterface.nil⌝ ∗ ∃ γ : KWatchNames,
        k8sWatch c W wi γ cd sel emp (kScopeOf c k opts.Recursive')
          (kModeOf sie opts.Predicate'.AllowWatchBookmarks' n) Q) }}

end spec

end Draft
end k8s
end EtcdGrove
end Perennial
