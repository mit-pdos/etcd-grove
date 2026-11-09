/-
`(*watchServer).Watch(stream)` (`watch.go`): the handler of one watch stream.

**Users.** gRPC's server, through the service registered by `v3rpc.Server` (`grpc.go:81`, batch 2a:
`_Watch_Watch_Handler` calls `srv.(WatchServer).Watch(&grpc.GenericServerStream{...})` for each
stream a client opens; 2a's registration takes `watchServiceAt`, whose meaning
`WatchServer.WatchTriple` is this spec, `watchServerAt_service`). Its clients are the Go client's
watch streams (1b: `watchGRPCStream.run`, `serveWatchClient`, through grpc's
`wireWatchRecv_recv`). Snippets: `examples/specreq/v3rpcwatch/protocol.go` (every one).

**Proof sketch.** Builds the run `sws`: the fields from `watchServerAt p γ`; `ws.watchable.
NewWatchStream()` (the member's watchable store, `watchMemberAt`'s triple, 3f: a fresh mvcc watch
stream with no watcher, its control side, its channel's consumer, its close; no thread token);
`ctrlStream` a channel of 16; the three maps; `closec`. Allocates the run's ghost state and
invariant (`swsAt sws γ who stream g`, `WatchInternal.lean`: no registration, the control channel
empty, the send state at `WireSt.init`, the mvcc consumer at nothing received) and splits it into
`swsRecver sws []` (with `srvWatchRecv stream g []`), `swsSender sws` (with `srvWatchSend stream γ
who g WireSt.init`) and `swsCloser sws`.
`sws.wg.Add(1)`; `go` the send goroutine (`Fork` gives it a thread token): `sendLoop.spec`, then
`wg.Done()` (the wait group's adder share, taken with the goroutine), exit with the token. `errc`
a channel of one, whose one message carries `∃ rs, swsRecver sws rs` (the control channel's
producer); `go` the receive goroutine: `recvLoop.spec` → `rerr`; if `rerr ≠ nil`: `stream.Context()`
(`srvWatchStreamAt_context`), `ctx.Err()` (W0's `Context.Err.spec`), `isClientCtxErr` (2a's
`util.go`, names only: its trusted spec, any errors, no panic), the log (zap) or the metric
(`streamFailures`, the ambient metrics boundary), `errc <- rerr` with the receive loop's share (never
blocks: the only send on a channel of one); exit with the token. The `select`: from `errc`, the
receive loop has returned and its share came with the message, so `close(sws.ctrlStream)` is the
producer's (no send can follow); `errors.Is(err, context.Canceled)` (Perennial's `errors`, an error
of any kind) and `rpctypes.ErrGRPCWatchCanceled` (2a's rpctypes variable, `isPkgInit`). From
`stream.Context().Done()` (`Context.Done.spec`, `doneRecv`): `Err()`, the same conversion; the
control channel stays open (the receive loop may still send; its sends `select` on `closec`). Then
`sws.close()` (`swsCloser`: the mvcc stream closed, `closec` closed, the send loop joined) and return.
The receive goroutine may outlive the call (blocked in `Recv` until grpc ends the stream when the
handler returns); its token goes back at its exit.

**Changes** from `specs-ref`'s `watchServer__Watch.lean`: stated over the client's wire protocol
(`srvWatchSend`'s `wireStep`, 1b's wire protocol, which took 2b's corrections in its round 2) instead of the old server-side stream
specification (`srvStreamIs ... Up Dn`, `watchStreamSpec γs R W tok Dn`, `upOk`, the auxiliary
name, the auth mode's tag); the principal `who` of the stream in place of the context's token
(`auth.ctxTokenOf`); no reader resources (`R.E.RD`, `mvccReaders W.γm 2`, the `threadBound`
premise): the loops take their goroutines' thread tokens (the bounds plan); the old restrictions of
the client's requests (`watchReqOk`: no `prevKV`, no fragments, no filters, no explicit id, no
`other`) reduced to the last two (the wire model: `ApiWatch.lean`'s header): `prevKV`, fragments
and filters are in scope.

**Margin.** The returned error (the receive loop's error, `ErrGRPCWatchCanceled`, the context's) is
not modelled: grpc turns it into the client's stream error, classified by 2a (`callErr`); the
handler returns only once the stream's context is done or the receive loop failed (liveness).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.ApiWatch

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

/-- **`ws.Watch(stream)`** on the server end of a watch stream of a client of `γ` as `who`: serves
the watch protocol on it (every response it sends a `wireStep`, through `srvWatchSend_send`). -/
def watchServer.Watch.spec : Prop :=
  ∀ (p : Loc) (γ : EtcdModel.Cluster) (st : GoInterface) (who : Principal) (g : WatchStreamNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      watchServerAt p γ ∗ srvWatchStreamAt st γ who g ∗ srvWatchRecv st g [] ∗
      srvWatchSend st γ who g WireSt.init }}
    (App (Val (p @!! go.GoType.PointerType v3rpc.watchServer.ty @!! go!"Watch")) (Val #st))
  {{ (err : GoInterface), RET #err; True }}

end spec

end V3rpc
end EtcdGrove
end Perennial
