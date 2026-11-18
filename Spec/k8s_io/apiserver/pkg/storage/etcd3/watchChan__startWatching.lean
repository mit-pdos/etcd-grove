/-
`(*watchChan).startWatching(watchClosedCh, bm, force)` (`k8s.io/apiserver/pkg/storage/etcd3/watcher.go:455-544`),
the watch's producer goroutine (k8s 7f-5a-P step 5): for a watch with initial events at a positive
requested revision, checks it against `getCurrentStorageRV` (an error, or a revision above the current
one, is sent as an Error event: `kErrOk`, E4 and E6); with initial events, `sync()` (an error sent);
queues the initial-events-end bookmark if asked; then watches the scope from `initialRev + 1`
(`WithPrevKV`, `WithPrefix` when recursive) and queues each response's events (`parseEvent`) and
progress notifications, until the client's channel closes (then sets `kProdExited` and closes
`watchClosedCh`, a broadcast of it) or a response is an error (sent; E2). Every queued raw event
extends the producer's state (`kProdSt`): what it queued is a subsequence of the ideal raw stream from
the start point, and a prefix unless the watch is no longer live or the processing goroutine has exited
(each element `kInElem`). Before each `sendError` it sets `kProdExited` (`kCancelPD`'s producer arm, for
`wc.cancel()`). Its premises are what `run` (step 6) has: the watch channel's fields (`kWcProd`),
`initialRev` (`kStartPre`), the caller's read updates, the producer's ghost state, a running producer of
`resultChan` (`kResAlive`, given back for `resultChanWG.Done()`) and the broadcast channel; the
goroutine's thread token (`getResourceSizeEstimator` borrows a reader slot with it); a bookmark asked
only with initial events (`kModeOf`'s), and the resource prefix's key short enough
(`GetCurrentResourceVersion`'s premise). Lean-first (no Rocq counterpart).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.WatchProd
public import Perennial.Golang.Theory.Chan.Idioms.Broadcast

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

/-- See the file header. -/
abbrev watchChan.startWatching.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
    (Obj : Type) [DecidableEq Obj] [Pos.Countable Obj] (wc sp : Loc) (c : StoreCfg GF Obj)
    (W : WatchSpec GF Obj) (γk : KVNames) (γ : KWatchNames) (cd : context.ContextDesc (IProp GF))
    (sel : Obj → Bool) (emp : Bool) (inS : GoString → Bool) (m : KWatchMode)
    (Q : Nat → KVState → IProp GF) (procd alive : GName) (ctx : GoInterfaceOk) (kp : GoString)
    (recur : Bool) (r0 : w64) (q : Qp) (wcc : Loc) (γb : ChanNames),
  (∀ lb σ, Q lb σ ⊢ ⌜lb ≤ σ.rev ∧ kvWf c σ ∧ kvWfHist c σ ∧ kvKeysShort σ⌝) →
  (∀ lb lb' σ σ', Q lb σ ∗ Q lb' σ' ⊢ ⌜kvSameHist σ σ'⌝) →
  (∀ x ∈ c.ms, noRefusalAt x.addr) →
  (m.bmReq = true → m.forceInit = true) →
  (c.pathPrefix ++ c.resourcePrefix).length ≤ opKeyMax →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 ∗ rangeStreamOff ∗
      isStore sp c ∗ storeWatchOk sp c W γk ∗
      kWcProd wc sp c W γ cd sel emp inS m Q procd alive ctx kp recur ∗
      structFieldRef k8s_io.apiserver.pkg.storage.etcd3.watchChan go!"initialRev" wc ↦ r0 ∗
      kStartPre m Q r0 ∗ readAus c γk (Q 0) ∗
      (□ ∀ lb σ, □ Q lb σ -∗ |==> readAus c γk (Q σ.rev)) ∗
      kProdSt γ cd [] ∗ dghostVar γ.prodEx (DFrac.own 1) false ∗ kResAlive alive q ∗
      ownBroadcastChan wcc γb (kProdExited γ) Broadcast.Pending ∗ threadTok }}
    (App (App (App (Val (wc @!! go.GoType.PointerType k8s_io.apiserver.pkg.storage.etcd3.watchChan.ty @!!
      go!"startWatching")) (Val #wcc)) (Val #m.bmReq)) (Val #m.forceInit))
  {{ RET #(); kResAlive alive q ∗ threadTok }}

end spec

end k8s
end EtcdGrove
end Perennial
