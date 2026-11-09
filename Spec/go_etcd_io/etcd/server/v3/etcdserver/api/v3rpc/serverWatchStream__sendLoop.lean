/-
`(*serverWatchStream).sendLoop()` (`watch.go`): the handler's send loop, with its closure
`sendWatch`.

**Users.** `watchServer.Watch`'s send goroutine (`watch.go:192`).

**Proof sketch.** `GetProgressReportInterval()` (its spec, the thread token lent and back: a
positive interval), `time.NewTicker` (Perennial's `time`, positive). Local `ids` (the ids whose
`Created` was sent and whose cancel response was not) and `pending` (mvcc responses of ids whose
`Created` was not sent, in order). Loop invariant (`swsAt`'s send state): `srvWatchSend st γ who g
sst` with the client's state `sst` agreeing with `ids`, the registrations and the mvcc consumer's
positions (each id of `sst.regs` is registered, at the position its responses sent so far made;
`sst.frag = none` between iterations), `pending[id]`'s responses steps of `id`'s registration from
its start.
* **An mvcc response** (`<-sws.watchStream.Chan()`, 3f: a response with its facts, its events
  owned (the event structs in full, their `Kv`s read-only, `PrevKv` `nil`); a closed channel ends
  the loop). `sendWatch`: under `mu` (`RLock`, the thread token as the reader slot) the id's
  `prevKV`; for each event, `IsCreateEvent` (its spec) and, with `prevKV`, mvcc's `Range(ctx, key,
  nil, {Rev: ModRevision - 1})` (3f/3e, thread token: the key's record at that revision of a
  reached state's history, or an error only below the member's compaction, at most the cluster's),
  its first record written to `PrevKv`: `WatchReq.prevOk`. The response `wr` (a header by
  `newResponseHeader(wresp.Revision)`, `Canceled` iff a compaction). Its id not `-1` and not in
  `ids`: buffered in `pending` (facts kept), `true`. Else, under `mu`, `fragment[id]`; sent whole
  (`Send`, `srvWatchSend_send`) or by `sendFragments` (its spec, `S ms :=` the half after the
  fragments `ms`, each fragment's `srvWireStep` from the pending-fragment state; the whole
  response's from mvcc's facts). The facts of a response of a registered id: mvcc's step of its
  registration (whole revisions of the range's filtered events after its position, the header at
  least the last event's; a progress at a synced watcher's revision, not below its start; a
  compaction above its position, at most the cluster's compaction) with `prevOk`, and the
  permission at the registration's `σa`: `watchStep`'s cases. Of an id not in `sst.regs` (its
  cancel or compaction response sent): `wireStep`'s "nothing". Of id `-1` (`RequestProgressAll`'s
  answer, never buffered): a progress at `P` of every registration live when it was produced; a
  registration of `sst.regs` not live then was canceled, and its cancel request was received
  before (`rs`): `srvWireStep`'s exemption. After a successful send with events, `progress[id]`
  cleared under `mu`. A failed send (`isClientCtxErr`, the log or the metric) ends the loop.
* **A control response** (`<-sws.ctrlStream`, closed: the loop ends): a `Created` one first drains
  mvcc's channel (`select` with `default`: every response produced before the creation is sent
  first, so a progress of id `-1` computed before the registration cannot follow its `Created`:
  the fork's fix of `issues/etcd-watch-progress-before-created.md`); then `Send` with the control
  protocol's facts (the `k`-th create's answer when `sst.answered = k`; a registration with a fresh
  id and its `σa`; a cancel's id); `verify.Assert` holds (a `Created` and `Canceled` answer has id
  `-1`); a cancel's id leaves `ids`; a `Created` one enters it and its `pending` responses are
  sent in order (`Send` each: steps of the new registration from `WatchPos.init s H`, `H` the
  `Created` header's revision, at least the registration's revision) and deleted.
* **The ticker**: under `mu`, `RequestProgress(id)` (3f, thread token: a progress of `id` at the
  store's revision if its watcher is synced and the revision not below its start) for each id whose
  flag is set, every flag set.
* **`closec`**: the loop ends.
On every exit the deferred function stops the ticker and drains mvcc's channel (until mvcc's
`Close` closes it: `swsAt`'s close protocol) and `pending`, with metrics (`ReportEventReceived`,
3f).

**Changes** from `specs-ref`'s file: the old run record, the down position's `watchDn`, mvcc's
consumer and received-list authority, the `threadBound` premise and the store's reader token
replaced by the run's shares (`swsAt`, `swsSender`) and the thread token; the facts are 1b's wire
protocol (`srvWireStep`); `prevKV`, fragments and filters in scope.

**Margin.** Mirrors the code: what is sent is `srvWatchSend`'s business.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.WatchInternal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace V3rpc

open Iris Iris.BI EtcdModel EtcdWire ClientV3
open go_etcd_io.etcd.server.v3.etcdserver.api

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`sws.sendLoop()`**: sends the run's responses down the stream, each with its `srvWireStep`
facts, until a send fails, a channel closes or the run closes. -/
def serverWatchStream.sendLoop.spec : Prop :=
  ∀ (sws : Loc) (γ : EtcdModel.Cluster) (who : Principal) (st : GoInterface) (g : WatchStreamNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      swsAt sws γ who st g ∗ srvWatchSend st γ who g WireSt.init ∗ swsSender sws ∗ threadTok }}
    (App (Val (sws @!! go.GoType.PointerType v3rpc.serverWatchStream.ty @!! go!"sendLoop")) (Val #()))
  {{ RET #(); threadTok }}

end spec

end V3rpc
end EtcdGrove
end Perennial
