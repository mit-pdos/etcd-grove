/-
`Cache.watchEvents` (`cache/*.go`), an internal helper.
Users: `Cache.watch`.
Proof sketch: the client's `Watch` of the prefix from `rev` with `WithProgressNotify`, `WithCreatedNotify` (`isClient_fields`' `watcherAt`, 1b's `watcherAt_methods`: `Watcher.WatchTriple` on the cache's internal context at the cache's principal, `ctxPrin who ctx who`: `ctxPrin_background`, `ctxPrin_child`; a `rev > 0` start, so the position is `WatchPos.init rev _`, complete up to `rev - 1`, or `closed`), a loop `select`ing on the cache's context, the watch channel (1b's `watchChAt_recvAu`: a response `watchRespAt v m` with `etcdLb γ σ`, `etcdLb γ σa` and `watchStep who w σ σa p m p'`) and `applyErr`: `readyOnce.Do(ready.Set)`; an error response (`WatchResponse.Err.spec`, `m.isErr`) resets readiness (`ready.Reset.spec`); else the response made read-only (`watchRespAt_persist`, `watchRespRO`; the events are `EtcdWire.eventOwn` at `DFrac.discard`, the cache's `eventOwn` with `prevKv = none` by `WatchReq.prevOk` without `prevKV`), converted to the cache's `WatchRespM` (each `EventM` the history's event by `EventM.isOf`), and its `respFact` from `watchStep`: an events response gives `deliv` (the gate `exactFrom σ.kv 0` implies 1b's `exactFrom σ.kv (done + 1)`), a progress (`IsProgressNotify`) `quiet` (the same gate), a `Created` the third arm; then `storeCeil_raise` to the response's revisions, `demux.Broadcast.spec`.
Changes: restated over the opaque vocabulary of `Internal.lean` (the old internal handles, ghost names and certificate parameters replaced by predicates over W0's model); the spec mirrors the code.
Margin: none known.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.cache.v3.Internal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Cache

open Iris Iris.BI EtcdModel EtcdWire ClientV3
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `c.watchEvents(rev, applyErr, readyOnce)` while the upstream watch from `rev` runs: returns with the run's role back. -/
def Cache.watchEvents.spec : Prop :=
  ∀ (c : Loc) (γ : Cluster) (who : Principal) (pfx : GoString) (rev : w64) (aec ro : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ isCache c γ who pfx ∗ cacheLoopRun c (sint.Z rev) ∗ applyErrChan aec ∗ readyOnceAt c ro }}
    (App (App (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.cache.v3.Cache.ty @!! go!"watchEvents")) (Val #rev)) (Val #aec)) (Val #ro))
  {{ (err : GoInterface), RET #err; cacheLoopRun c (sint.Z rev) }}

end spec

end Cache
end EtcdGrove
end Perennial
