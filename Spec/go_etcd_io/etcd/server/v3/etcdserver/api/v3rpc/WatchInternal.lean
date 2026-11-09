/-
# The watch handler's run: internal vocabulary (batch 2b)

What the specs of `serverWatchStream`'s methods (`recvLoop`, `sendLoop`, `isWatchPermitted`,
`close`, `newResponseHeader`) are stated over: one run of `watchServer.Watch` on one gRPC stream.
Internal to v3rpc's watch: no client sees these names (`watchServer.Watch.spec` and the
`WatchServer` contract are over `ApiWatch.lean`'s).

* `swsAt sws γ who st g` (persistent): **the run `sws`** of the handler on the stream end `st`
  (stream `g`, a client of `γ` as `who`). Intended realization, the run's invariant:
  - the read-only fields: the logger, the member's ids (for `newResponseHeader`), the request
    budget, `sg`/`ag` (`watchMemberAt s γ`), `watchable` (the member's `mvcc.WatchableKV`),
    `gRPCStream = st` (`srvWatchStreamAt st γ who g`), `watchStream` (the mvcc stream, 3f's
    predicates), `ctrlStream` (a buffered channel), `closec` (a channel closed once), the maps;
  - **the registrations** (a ghost map, persistent entries): each mvcc id the receive loop got from
    `Watch` maps to its wire create `(w, s)` and the state `σa` (`etcdLb γ σa`, the permission at
    `σa`) that admitted it; ids are fresh on the stream and never `-1` (3f's auto ids);
  - **the control channel's protocol**: the `k`-th element sent is the answer of the `k`-th create
    or the cancel it follows, carrying the facts its send will need (a refusal; or the registration
    of a fresh id, with its `σa`; a cancel's id, whose mvcc watcher is canceled);
  - **mvcc's stream** (3f, `req/go_etcd_io_etcd_server_v3_storage_mvcc.md`): its consumer side
    (the send loop's) at per-id positions, each response of a registered id a step of that
    registration against a reached state, a response of id `-1` a progress of every id live
    (registered, not canceled) when it was produced; the canceled ids, each with its cancel
    request among the requests received;
  - **the send state**: the client's `WireSt` as the responses sent made it (`srvWatchSend`'s
    index) agrees with the send loop's `ids` (the ids whose `Created` was sent and whose cancel
    response was not) and with the mvcc consumer's positions of those ids; a buffered response
    (`pending`) is of an id whose `Created` was not sent, at the positions from its start;
  - the lock `mu` over `progress` (any), `prevKV`, `fragment` (`prevKV[id]` and `fragment[id]` the
    registration's `w.prevKV`, `w.fragment`).
* `swsRecver sws rs` (exclusive): **the receive loop's share** after the requests `rs`: the
  control channel's producer, the mvcc stream's control side (`Watch`, `Cancel`,
  `RequestProgressAll`), the count of creates answered.
* `swsSender sws` (exclusive): **the send loop's share** at its start: the control channel's and
  mvcc channel's consumers (positions at nothing received), the empty `ids`/`pending` it allocates,
  the wait group's `Done` (its thread token's deposit).
* `swsCloser sws` (exclusive): **the handler's share**: the mvcc stream's close, `closec`'s close,
  the wait group's waiter.

`swsAt_alloc` is how the handler gets them (its spec's sketch); no law is exported (internal).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.ApiWatch

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace V3rpc

open Iris Iris.BI EtcdModel EtcdWire ClientV3

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]

/-- **The run `sws`** of the watch handler on the stream end `st` (persistent). -/
opaque swsAt (sws : Loc) (γ : Cluster) (who : Principal) (st : GoInterface) (g : WatchStreamNames) :
  IProp GF := iprop(True)

/-- **The receive loop's share** of the run, after the requests `rs` (exclusive). -/
opaque swsRecver (sws : Loc) (rs : List WireWatchReq) : IProp GF := iprop(True)

/-- **The send loop's share** of the run, at its start (exclusive). -/
opaque swsSender (sws : Loc) : IProp GF := iprop(True)

/-- **The handler's share** of the run: the right to close it (exclusive). -/
opaque swsCloser (sws : Loc) : IProp GF := iprop(True)

def swsAt_persistent.spec : Prop := ∀ sws γ who st g, Persistent (swsAt (GF := GF) sws γ who st g)

end res

end V3rpc
end EtcdGrove
end Perennial
