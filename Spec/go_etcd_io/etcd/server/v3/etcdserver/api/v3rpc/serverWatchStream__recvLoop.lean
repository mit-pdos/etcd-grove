/-
`(*serverWatchStream).recvLoop()` (`watch.go`): the handler's receive loop.

**Users.** `watchServer.Watch`'s receive goroutine (`watch.go:202`).

**Proof sketch.** Loop invariant: `srvWatchRecv st g rs ∗ swsRecver sws rs ∗ threadTok`
(`swsRecver`: the control channel's producer, the mvcc stream's control side, the count of creates
answered). `Recv()` (`srvWatchRecv_recv`): an error ends the loop (`errors.Is(err, io.EOF)`:
Perennial's `errors`, any error; `nil` for `io.EOF`, else the error), the share given back. Else a
fresh request `watchReqOwn p (own 1) r` (`srvWatchRecv_lb` records it received); its fields by
`watchReqOwn_unfold` (the type switch takes the case of `r`'s wrapper, its inner request non-`nil`;
the `default:` branch, stuck in the translation, is unreachable):
* `create wq s`: an empty `Key` is set to `"\x00"` (the field owned in full), so the key is
  `wq.range.key` (`createRange`). The answer goes on the control channel (`select` with `closec`:
  `closec` closed ends the loop, `nil`), and is, by the channel's protocol, the answer of this, the
  `k`-th, create: when the send loop sends it the client's state has answered `k` creates. Its
  header is `newResponseHeader(sws.watchStream.Rev())` (mvcc's `Rev`, 3f, with the thread token:
  a revision the member applied, so reached). `s < 0`: refused (`-1`, `Created`, `Canceled`,
  `rpctypes.ErrCompacted.Error()`, a non-empty string: 2a's rpctypes). Else
  `isWatchPermitted(creq)` (its spec): an error refuses (its reason by `errors.Is` against auth's
  errors, each `rpctypes.ErrGRPC*.Error()` non-empty; the `Error` log, zap); a pass gives `σa`
  with `σa.permits who [(.read, wq.range)] []`. The range end normalized (`nil` for an empty one,
  `[]byte{}` for `"\x00"`: mvcc's single key and from-key), `FiltersFromRequest` (its spec:
  `filterFuncs`, whose functions meet mvcc's filter contract by `filterNoPut.spec`,
  `filterNoDelete.spec`), the tracer's span (`traceutil.Tracer.Start`, otel: a context, no panic),
  then mvcc's `Watch(ctx, 0, key, end, s, filters...)` (3f, `req/..._storage_mvcc.md`, with the
  thread token: an auto id, fresh on the stream and not `-1`, registered at `s` over the range and
  filters, its responses on the stream's channel as the run's invariant states; or an error with a
  non-empty message: refused, `-1`). A registration is recorded in the run's ghost map (id ↦ `wq`,
  `s`, `σa`) and its options under `mu` (`progress`, `prevKV`, `fragment`: from mvcc's `Watch` to
  here the send loop may already have built responses of the id without `PrevKv`, the
  registration's loose window, `issues/etcd-watch-prevkv-before-created.md`); the answer `Created`
  with the id, carrying the registration.
* `cancel id`: mvcc's `Cancel(id)` (3f): `nil` only for a live registration, which is now canceled
  (no response of it is produced after; the ones queued stay in the channel): the run's canceled
  set gains `id`, its cancel request received (`rs`). The answer (`Canceled`, the id, a header) on
  the control channel; then the options deleted under `mu`. An error: no answer.
* `progress`: under `mu`, mvcc's `RequestProgressAll()` (3f, thread token: a progress of id `-1`
  at the store's revision for every live registration, on the stream's channel after their queued
  responses, if all are synced; else nothing).

**Changes** from `specs-ref`'s file: the old run record (`swsIs sws r Up Dn st ci cd`), the
answer pool (`ansPool`), the control channel's producer token and the store's reader tokens
(`mvccReaders`) and auth reader resource replaced by the run's shares (`swsAt`, `swsRecver`) and
the thread token (the bounds plan); the post's control producer kept (`swsRecver`), which the
handler needs to close the control channel.

**Margin.** The error is the `Recv`'s (or `nil`), not modelled.
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

/-- **`sws.recvLoop()`**: answers each request it receives (through the control channel and the
mvcc stream), until the stream fails or the run closes; gives back its share. -/
def serverWatchStream.recvLoop.spec : Prop :=
  ∀ (sws : Loc) (γ : EtcdModel.Cluster) (who : Principal) (st : GoInterface) (g : WatchStreamNames)
    (rs : List WireWatchReq),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      swsAt sws γ who st g ∗ srvWatchRecv st g rs ∗ swsRecver sws rs ∗ threadTok }}
    (App (Val (sws @!! go.GoType.PointerType v3rpc.serverWatchStream.ty @!! go!"recvLoop")) (Val #()))
  {{ (err : GoInterface), RET #err; threadTok ∗ ∃ rs' : List WireWatchReq, swsRecver sws rs' }}

end spec

end V3rpc
end EtcdGrove
end Perennial
