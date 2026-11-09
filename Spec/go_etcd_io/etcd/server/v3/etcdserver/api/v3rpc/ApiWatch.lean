/-
# etcd's gRPC watch service: the vocabulary (batch 2b)

`server/etcdserver/api/v3rpc/watch.go`: the `Watch` service a member registers with its gRPC
server (`grpc.go`: `pb.RegisterWatchServer(grpcServer, NewWatchServer(s))`). One handler run per
gRPC stream (`watchServer.Watch`): a receive loop reads the client's requests (create, cancel,
progress) and drives the member's mvcc watch stream; a send loop forwards mvcc's responses and the
receive loop's control responses down the gRPC stream.

## The contract: the client's wire protocol

The meaning of the service is **what a client observes on the stream**: 1b's `wireStep`
(`Spec/go_etcd_io/etcd/client/v3/ApiWatch.lean`, the wire protocol of one watch stream, "the
contract with 2a and 2b"). A response the handler sends is a `wireStep` from the stream's state as
the responses before it made it (`WireSt`), after the requests the handler had received (`ss`),
read against reached states of the cluster (`etcdLb γ σ`: the history the events and revisions are
read against; `etcdLb γ σa`: the auth state that admitted the registration whose response it is).
In words (1b's round 2 took 2b's corrections and strengthenings into `wireStep` itself):

* every response has a header;
* the `k`-th `Created` answers the `k`-th create received: refused (`WatchId = -1`, `Canceled`, a
  reason: a negative start revision, always refused; the permission check; mvcc's refusal), or
  registered (a non-negative start) under an id **never announced before on the stream**, **the
  principal permitted to read the range** at `σa`, at `WatchPos.init start H`;
* a response of a registered id is a `watchStep` of its registration: its events are exactly the
  range's (filtered) events of the revisions after its position up to the last event's, whole
  revisions, `PrevKv` as the history says (`WatchReq.prevOk`, loose in the registration's window:
  `issues/etcd-watch-prevkv-before-created.md`), the header revision at least the last event's; a
  progress (no events) at `P` says nothing of the range changed since the position up to `P`, `P`
  not below it; a compaction (`Canceled`, `CompactRevision = cr`) says `cr` is at most the
  cluster's compaction and above the position;
* the id `-1`: a progress notification for every registration **whose cancel the member has not
  read** (a client that cancels an unsynced watch and then requests progress can receive the
  progress before the cancel response; the Go client never delivers it to the canceled watch);
* `Canceled` without compaction ends the id's registration (a cancel's answer), and **nothing more
  of that id** is sent (`WireSt.retired`); no response of an id never announced;
* a fragment (`Fragment` set) has events, is of a registered watch created with `Fragment`, and its
  response's fragments are sent contiguously, the last without `Fragment`.

**The scope of the contract: the requests are wire requests.** The handler reads each request
through 1b's `watchReqOwn p dq r` (the one wire model of both ends): a `WireWatchReq`, so a create
asks for no watch id of its own (`WatchId = 0`), and no request is an empty or `nil` oneof (the
unfold law the message's realization owes, `watchReqOwn_unfold`; the non-`nil` *inner* request is
the model's choice, the Go code `break`s on one). A restriction on the stream's clients, met by
etcd's Go client (`watchRequest.toPB`, `progressRequest.toPB`, `run`'s cancel requests), hence by
grpc-proxy (a clientv3 user towards the member) and the in-process client; **not** by the
grpc-gateway (`/v3/watch` forwards any JSON, `watch_id` included) nor by foreign clients. Two
reasons: a create with an explicit id may reuse a canceled watch's id and receive its queued events
(`issues/etcd-watch-id-reuse-stale-events.md`), and the translation of `recvLoop`'s `default:`
branch reads the type switch's variable `uv`, which Goose leaves unbound there (stuck in the model,
harmless in Go). 2a cannot check the restriction of a network peer: `srvWatchRecvdLb_sent` assumes
every stream is opened by a modelled client. A decision for the user (`notes/specs-only/batch-2b.md`).

**The in-process client is out of scope** (`v3client.New`, `embed/serve.go:148-150`, which v3lock
and v3election use): it runs this handler on the adapter's pipe stream
(`proxy/grpcproxy/adapter/chan_stream.go`), which passes the message pointers themselves, so the
slot laws below (fresh messages at both ends) do not hold of it: the handler writes a received
create's `Key`/`RangeEnd` (1b's client `Send` gives the request back), reads a sent control
response's `WatchId`/`Canceled`/`Created` after `Send`, while 1b's client writes the fields of the
first fragment of a received response (`cur.Events`, `cur.Fragment`). A realization needs `Send` at
both ends to transfer the message (the sender keeping a read-only share of only the fields it reads
afterwards, which the receiver never writes). An open question (`batch-2b.md`).

## Vocabulary

Pure (transparent):
* `progressIntervalOk d` (the progress interval's lock invariant: `GetProgressReportInterval`'s
  jitter needs `d ≥ 10` ns, the ticker a positive sum), `watchIntervalCfgOk d` (the configured
  `--watch-progress-notify-interval`, raised to 100ms: a scope premise of the configuration,
  `nonissues/etcd-watch-progress-interval-overflow.md`), `minWatchProgressIntervalNs`.
* `filterFuncs fl`: the filter functions `FiltersFromRequest` builds of a request's filter types.
* `fragmentsOf m ms`, `fragPrefix`: `ms` is how `sendFragments` cuts `m`.

Resources:
* `watchServerAt p γ` (persistent): **a `*watchServer` of a member of the cluster `γ`**
  (`NewWatchServer`'s). Intended realization: its read-only fields (the logger, the member's
  cluster and member ids, the request budget, `sg`/`ag` the `*EtcdServer` as `RaftStatusGetter` and
  `AuthGetter`, `watchable` the member's mvcc store), with `watchMemberAt s γ` and `isPkgInit v3rpc`
  (persistent: `WatchServer.WatchTriple` does not take it, `watchServer.Watch.spec` does).
* `watchServiceAt v γ` (persistent): **the `pb.WatchServer` value `v` serves the watch protocol of
  `γ`**: its `Watch` method meets `WatchServer.WatchTriple` (`watchServiceAt_methods`). The slot 2a's
  registration (`grpc.go`'s `Server`, the service's spec at `/etcdserverpb.Watch/Watch`) consumes;
  `watchServerAt_service` gives it for a `*watchServer`.
* `watchMemberAt s γ` (persistent): **slot of the server batches (2c/2d/2e)**: the `*EtcdServer`
  `s` is a member of `γ` whose watch path is ready. What `NewWatchServer` and the handler read of it:
  its configuration's logger, request budget and progress interval (read-only fields,
  `watchMemberAt_cfg`), and the triples of `s.Cluster().ID()`, `s.MemberID()`, `s.Watchable()`
  (the member's `mvcc.WatchableKV`: its watch streams deliver the history of `γ` as the member
  applies it), `Term()`/`Leader()` (any values), `AuthInfoFromCtx(ctx)` and
  `AuthStore().IsRangePermitted(info, key, end)` (a pass means a reached state permits the
  stream's principal to read the range), stated in plain terms in
  `req/go_etcd_io_etcd_server_v3_etcdserver.md` (`## from 2b`) and `req/..._storage_mvcc.md`,
  `req/..._auth.md`; the integration round states them as laws here.
* **Slots of the gRPC boundary (2a), the server's end of a watch stream** (1b's
  `WatchStreamNames` name the stream at both ends):
  - `srvWatchStreamAt st γ who g` (persistent): `st` is the server end of the watch stream `g`,
    opened by a client of `γ` as the principal `who`; its `Context()` is a context whose incoming
    metadata names `who` (`srvCtxPrin`, `srvWatchStreamAt_context`);
  - `srvWatchRecv st g rs` (exclusive): the receiving half, the requests `rs` received so far
    (`srvWatchRecv_recv`); `srvWatchRecvdLb g rs` (persistent): at least `rs` were received
    (`srvWatchRecv_lb`), hence sent by the client (`srvWatchRecvdLb_sent`, with 1b's
    `wireWatchSentLb`);
  - `srvWatchSend st γ who g sst` (exclusive): the sending half, the responses sent so far having
    made the client's state `sst` (`WireSt`); `Send` takes a read-only response with its `wireStep`
    facts (`srvWatchSend_send`): the facts travel with the message, as the old `GrpcSpec`'s did;
  - `srvCtxPrin ctx who` (persistent): the server context's incoming metadata names `who` (its
    token issued to `who`, or no token; a token issued to no one fails `AuthInfoFromCtx`), and,
    with client-certificate authentication on, a token-less context's TLS peer's CN names `who`
    (`EtcdServer.AuthInfoFromCtx` falls back to `AuthInfoFromTLS`: `req/..._auth.md`,
    `req/google_golang_org_grpc.md`, `## from 2b`). Consumed by `AuthInfoFromCtx` (2c/3d). If 2a
    states a server-context principal of its own for the unary handlers (W0's item 6), this one
    becomes it.
* Laws on 1b's message slots that the handler's proof needs, offered to their realizer (3h, with
  W0's `Wire.lean`): `watchReqOwn_unfold` (the request's Go fields; the server writes the create's
  `Key` and `RangeEnd`), `wireWatchRespOwn_unfold` (the response's Go fields: the server builds
  them), `wireWatchRespOwn_persist`.

## Requirement snippets

`examples/specreq/v3rpcwatch/`: `protocol.go` (over a raw `pb.WatchClient` stream, what the Go
client's `run` and `serveWatchClient` rely on: creates answered in order, a refused create,
events from the start revision in order with whole revisions, the permission check, progress
meaning "nothing missed", progress of id `-1`, a cancel ends the id, compaction, fragments
reassembled) and `serve.go` (the registration: `NewWatchServer` on a started member, the
progress interval's setter).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.ApiWatch
public import GeneratedProof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc
public import Spec.PkgInit.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc
public import Spec.go_uber_org.zap.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace V3rpc

open Iris Iris.BI EtcdModel EtcdWire ClientV3
open go_etcd_io.etcd.api.v3
open Classical

/-! ## Pure -/

/-- `minWatchProgressInterval` (100ms), in nanoseconds. -/
def minWatchProgressIntervalNs : Int := 100000000

/-- **The progress interval's lock invariant** (`progressReportInterval`): at least `10` ns
(`GetProgressReportInterval`'s `rand.Int63n(interval / 10)` needs a positive argument), and the
interval plus its jitter (below a tenth of it) fits an `int64` (`time.NewTicker` panics on a
non-positive duration). -/
def progressIntervalOk (d : Int) : Prop := 10 ≤ d ∧ d + d / 10 ≤ 2 ^ 63

/-- **The configured progress interval** (`--watch-progress-notify-interval`): not used if not
positive, else raised to 100ms by `NewWatchServer`, and then within `progressIntervalOk` (at most
about 265 years: `nonissues/etcd-watch-progress-interval-overflow.md`). A scope premise of the
configuration, taken where the server is configured (2e). -/
def watchIntervalCfgOk (d : Int) : Prop :=
  d ≤ 0 ∨ progressIntervalOk (max d minWatchProgressIntervalNs)

/-- `NOPUT`, `NODELETE` (`pb.WatchCreateRequest_FilterType`). -/
def filterNoPutTy : w32 := W32 0
def filterNoDeleteTy : w32 := W32 1

section funcs
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

/-- **The filters `FiltersFromRequest` builds**: for each filter type of the request, in order,
`filterNoPut` for `NOPUT`, `filterNoDelete` for `NODELETE`, nothing for any other value. -/
def filterFuncs (fl : List w32) : List GoFunc :=
  fl.filterMap fun ft =>
    if ft = filterNoPutTy then
      some (functions go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.filterNoPut [])
    else if ft = filterNoDeleteTy then
      some (functions go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.filterNoDelete [])
    else none

end funcs

/-- **`ms` is how `sendFragments` sends `m`**: `m` whole, or fragments carrying its events in
order, each non-empty, each with `m`'s other fields, all but the last with `Fragment` set. -/
def fragmentsOf (m : WireWatchRespM) (ms : List WireWatchRespM) : Prop :=
  ms = [m] ∨
  (ms ≠ [] ∧ (ms.map (·.events)).flatten = m.events ∧
    ∀ (i : Nat) (f : WireWatchRespM), ms[i]? = some f →
      f.events ≠ [] ∧ f = { m with events := f.events, fragment := decide (i + 1 < ms.length) })

/-- `ms` is a prefix of a way `sendFragments` sends `m`. -/
def fragPrefix (m : WireWatchRespM) (ms : List WireWatchRespM) : Prop :=
  ∃ rest, fragmentsOf m (ms ++ rest)

/-! ## Resources -/

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- **A `*watchServer` of a member of `γ`** (persistent). -/
opaque watchServerAt (p : Loc) (γ : Cluster) : IProp GF := iprop(True)

/-- **The `pb.WatchServer` value `v` serves the watch protocol of `γ`** (persistent). -/
opaque watchServiceAt (v : GoInterface) (γ : Cluster) : IProp GF := iprop(True)

/-- **Slot (2c/2d/2e)**: the `*EtcdServer` `s` is a member of `γ` whose watch path is ready. -/
opaque watchMemberAt (s : Loc) (γ : Cluster) : IProp GF := iprop(True)

/-- **Slot (2a)**: `st` is the server end of the watch stream `g`, opened by a client of `γ` as
`who` (persistent). -/
opaque srvWatchStreamAt (st : GoInterface) (γ : Cluster) (who : Principal) (g : WatchStreamNames) :
  IProp GF := iprop(True)

/-- **Slot (2a)**: the receiving half of the server end `st` (exclusive), the requests `rs`
received. -/
opaque srvWatchRecv (st : GoInterface) (g : WatchStreamNames) (rs : List WireWatchReq) :
  IProp GF := iprop(True)

/-- **Slot (2a)**: at least the requests `rs` were received on the stream `g` (persistent). -/
opaque srvWatchRecvdLb (g : WatchStreamNames) (rs : List WireWatchReq) : IProp GF := iprop(True)

/-- **Slot (2a)**: the sending half of the server end `st` (exclusive), the responses sent having
made the client's state `sst`. -/
opaque srvWatchSend (st : GoInterface) (γ : Cluster) (who : Principal) (g : WatchStreamNames)
  (sst : WireSt) : IProp GF := iprop(True)

/-- **Slot (2a, consumed by 2c/3d)**: the server-side context `ctx`'s incoming metadata names the
principal `who` (persistent). -/
opaque srvCtxPrin (ctx : GoInterface) (who : Principal) : IProp GF := iprop(True)

/-- The type of a watch stream's server end. -/
def watchSrvStreamTy : go.GoType :=
  google_golang_org.grpc.BidiStreamingServer.ty etcdserverpb.WatchRequest.ty
    etcdserverpb.WatchResponse.ty

/-! ## The handler contract, filling `watchServiceAt` -/

/-- **`Watch(stream)`**, the handler of one watch stream: given the server end of a stream of a
client of `γ` as `who`, both halves at the start, it serves the protocol (every response it sends
carries its `wireStep` facts: `srvWatchSend_send`) and returns some error when the stream ends
(the receive loop's error, `ErrGRPCWatchCanceled` for a canceled context, or the context's error:
not modelled). -/
def WatchServer.WatchTriple (f : val) (P : IProp GF) (γ : Cluster) : Prop :=
  ∀ (st : GoInterface) (who : Principal) (g : WatchStreamNames),
  {{ P ∗ srvWatchStreamAt st γ who g ∗ srvWatchRecv st g [] ∗ srvWatchSend st γ who g WireSt.init }}
    (App (Val f) (Val #st))
  {{ (err : GoInterface), RET #err; True }}

/-! ## Laws -/

def watch_srv_persistent.spec : Prop :=
  (∀ p γ, Persistent (watchServerAt (GF := GF) p γ)) ∧
  (∀ v γ, Persistent (watchServiceAt (GF := GF) v γ)) ∧
  (∀ s γ, Persistent (watchMemberAt (GF := GF) s γ)) ∧
  (∀ st γ who g, Persistent (srvWatchStreamAt (GF := GF) st γ who g)) ∧
  (∀ g rs, Persistent (srvWatchRecvdLb (GF := GF) g rs)) ∧
  (∀ ctx who, Persistent (srvCtxPrin (GF := GF) ctx who))

/-- **`watchServiceAt`'s meaning**: the `Watch` method's handler contract. -/
def watchServiceAt_methods.spec : Prop := ∀ (v : GoInterface) (γ : Cluster),
  WatchServer.WatchTriple (v @!! etcdserverpb.WatchServer.ty @!! go!"Watch")
    (watchServiceAt (GF := GF) v γ) γ

/-- A `*watchServer` serves the protocol (its `Watch`'s spec, `watchServer__Watch.lean`). -/
def watchServerAt_service.spec : Prop := ∀ (p : Loc) (γ : Cluster),
  watchServerAt (GF := GF) p γ ⊢
    watchServiceAt (interface.mkOk (go.GoType.PointerType
      go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.watchServer.ty) #p) γ

/-- **What `NewWatchServer` reads of a member's configuration** (slot law, 2e): the logger (`nil`
or a logger), the request budget and the progress interval, read-only, the interval within the
configuration's scope (`watchIntervalCfgOk`). -/
def watchMemberAt_cfg.spec : Prop := ∀ (s : Loc) (γ : Cluster),
  watchMemberAt (GF := GF) s γ ⊢
    ∃ (lg : Loc) (mrb : w64) (d : w64),
      (structFieldRef go_etcd_io.etcd.server.v3.config.ServerConfig go!"Logger"
        (structFieldRef go_etcd_io.etcd.server.v3.etcdserver.EtcdServer go!"Cfg" s)) ↦□ lg ∗
      (⌜lg = null⌝ ∨ Zap.isLogger lg) ∗
      (structFieldRef go_etcd_io.etcd.server.v3.config.ServerConfig go!"MaxRequestBytes"
        (structFieldRef go_etcd_io.etcd.server.v3.etcdserver.EtcdServer go!"Cfg" s)) ↦□ mrb ∗
      (structFieldRef go_etcd_io.etcd.server.v3.config.ServerConfig go!"WatchProgressNotifyInterval"
        (structFieldRef go_etcd_io.etcd.server.v3.etcdserver.EtcdServer go!"Cfg" s)) ↦□ d ∗
      ⌜watchIntervalCfgOk (sint.Z d)⌝

/-- **The stream's context** (`st.Context()`): a context (`Context.ctxOk`) whose incoming metadata
names `who`. -/
def srvWatchStreamAt_context.spec : Prop := ∀ (st : GoInterface) (γ : Cluster) (who : Principal)
    (g : WatchStreamNames),
  {{ srvWatchStreamAt (GF := GF) st γ who g }}
    (App (Val (st @!! watchSrvStreamTy @!! go!"Context")) (Val #()))
  {{ (ctx : GoInterface), RET #ctx; Context.ctxOk ctx ∗ srvCtxPrin ctx who }}

/-- **Receiving a request** (`st.Recv()`): the client's next request, in order, a fresh message
owned in full; or an error (`io.EOF` once the client closed its sending side, else the stream's
or its context's), the half kept (later receives fail too). -/
def srvWatchRecv_recv.spec : Prop := ∀ (st : GoInterface) (γ : Cluster) (who : Principal)
    (g : WatchStreamNames) (rs : List WireWatchReq),
  {{ srvWatchStreamAt (GF := GF) st γ who g ∗ srvWatchRecv st g rs }}
    (App (Val (st @!! watchSrvStreamTy @!! go!"Recv")) (Val #()))
  {{ (p : Loc) (err : GoInterface), RET (PairV #p #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ r : WireWatchReq,
         watchReqOwn p (DFrac.own 1) r ∗ srvWatchRecv st g (rs ++ [r])) ∨
      (⌜err ≠ GoInterface.nil⌝ ∗ srvWatchRecv st g rs) }}

/-- A lower bound of what was received. -/
def srvWatchRecv_lb.spec : Prop := ∀ st g rs,
  srvWatchRecv (GF := GF) st g rs ⊢ srvWatchRecv st g rs ∗ srvWatchRecvdLb g rs

/-- What the server received the client sent (1b's `wireWatchSentLb`). -/
def srvWatchRecvdLb_sent.spec : Prop := ∀ g rs,
  srvWatchRecvdLb (GF := GF) g rs ⊢ wireWatchSentLb g rs

/-- **Sending a response** (`st.Send(p)`): the message, read-only (the handler never writes a
response after sending it; grpc-go may read it after `SendMsg` returns, grpc-go#5857), with its facts
(a `wireStep` from the state the responses sent so far made, after requests received, at reached
states); on success the half at the new state; on an error the half is gone (the handler sends
nothing more; the message may or may not have been delivered). -/
def srvWatchSend_send.spec : Prop := ∀ (st : GoInterface) (γ : EtcdModel.Cluster) (who : Principal)
    (g : WatchStreamNames) (sst sst' : WireSt) (p : Loc) (m : WireWatchRespM)
    (σ σa : State) (rs : List WireWatchReq),
  {{ srvWatchStreamAt (GF := GF) st γ who g ∗ srvWatchSend st γ who g sst ∗
      wireWatchRespOwn p DFrac.discard m ∗ etcdLb γ σ ∗ etcdLb γ σa ∗ srvWatchRecvdLb g rs ∗
      ⌜wireStep who σ σa rs sst m sst'⌝ }}
    (App (Val (st @!! watchSrvStreamTy @!! go!"Send")) (Val #p))
  {{ (err : GoInterface), RET #err;
      (⌜err = GoInterface.nil⌝ ∗ srvWatchSend st γ who g sst') ∨ ⌜err ≠ GoInterface.nil⌝ }}

/-! ### Laws on 1b's message slots (offered to their realizer, 3h) -/

/-- The `KeyRange` a create request's raw key and range end name, as the member checks it: an
empty key is `"\x00"` (`recvLoop`); the range end as sent (`nil`, or `"\x00"` for a from-key). -/
def createRange (k e : GoString) : KeyRange :=
  { key := if k = [] then [W8 0] else k, rangeEnd := e }

/-- **A watch request's Go fields** (`pb.WatchRequest`): its `RequestUnion` a non-`nil` wrapper of
a non-`nil` inner request. A create's fields model the wire create `create w s`: the key and range
end raw (`createRange`), `StartRevision = s`, `ProgressNotify`, `PrevKv`, `Fragment` as `w`'s, the
filter types containing `NOPUT` iff `w.filterPut` and `NODELETE` iff `w.filterDelete`, and
`WatchId = 0` (no id of its own; `w.createdNotify` is the client's alone). A cancel's `WatchId`
its id. -/
def watchReqOwn_unfold.spec : Prop := ∀ (p : Loc) (dq : DFrac) (r : WireWatchReq),
  watchReqOwn (GF := GF) p dq r ⊣⊢
    ∃ (iv : GoInterface) (w : Loc), protoRest etcdserverpb.WatchRequest p dq ∗
    p.[etcdserverpb.WatchRequest, go!"RequestUnion"] ↦{dq} iv ∗
    match r with
    | .create wq s => ∃ (c : Loc) (ks es fs : GoSlice) (k e : GoString) (fl : List w32),
        ⌜iv = interface.mkOk (go.GoType.PointerType etcdserverpb.WatchRequest_CreateRequest.ty) #w ∧
          c ≠ null ∧ createRange k e = wq.range ∧ -2 ^ 63 ≤ s ∧ s < 2 ^ 63 ∧
          (filterNoPutTy ∈ fl ↔ wq.filterPut = true) ∧
          (filterNoDeleteTy ∈ fl ↔ wq.filterDelete = true)⌝ ∗
        w.[etcdserverpb.WatchRequest_CreateRequest, go!"CreateRequest"] ↦{dq} c ∗
        protoRest etcdserverpb.WatchCreateRequest c dq ∗
        c.[etcdserverpb.WatchCreateRequest, go!"Key"] ↦{dq} ks ∗ ks ↦*□ k ∗
        c.[etcdserverpb.WatchCreateRequest, go!"RangeEnd"] ↦{dq} es ∗ es ↦*□ e ∗
        c.[etcdserverpb.WatchCreateRequest, go!"StartRevision"] ↦{dq} (W64 s) ∗
        c.[etcdserverpb.WatchCreateRequest, go!"ProgressNotify"] ↦{dq} wq.progressNotify ∗
        c.[etcdserverpb.WatchCreateRequest, go!"Filters"] ↦{dq} fs ∗ fs ↦*□ fl ∗
        c.[etcdserverpb.WatchCreateRequest, go!"PrevKv"] ↦{dq} wq.prevKV ∗
        c.[etcdserverpb.WatchCreateRequest, go!"WatchId"] ↦{dq} (W64 0) ∗
        c.[etcdserverpb.WatchCreateRequest, go!"Fragment"] ↦{dq} wq.fragment
    | .cancel id => ∃ c : Loc,
        ⌜iv = interface.mkOk (go.GoType.PointerType etcdserverpb.WatchRequest_CancelRequest.ty) #w ∧
          c ≠ null ∧ -2 ^ 63 ≤ id ∧ id < 2 ^ 63⌝ ∗
        w.[etcdserverpb.WatchRequest_CancelRequest, go!"CancelRequest"] ↦{dq} c ∗
        protoRest etcdserverpb.WatchCancelRequest c dq ∗
        c.[etcdserverpb.WatchCancelRequest, go!"WatchId"] ↦{dq} (W64 id)
    | .progress => ∃ c : Loc,
        ⌜iv = interface.mkOk (go.GoType.PointerType etcdserverpb.WatchRequest_ProgressRequest.ty) #w ∧
          c ≠ null⌝ ∗
        w.[etcdserverpb.WatchRequest_ProgressRequest, go!"ProgressRequest"] ↦{dq} c ∗
        protoRest etcdserverpb.WatchProgressRequest c dq

/-- **A watch response's Go fields** (`pb.WatchResponse`): the header (`nil` for `none`), the
events (each an `eventOwn`), the flags; `WatchId`'s `int64` the model's id. -/
def wireWatchRespOwn_unfold.spec : Prop := ∀ (p : Loc) (dq : DFrac) (m : WireWatchRespM),
  wireWatchRespOwn (GF := GF) p dq m ⊣⊢
    ∃ (h : Loc) (evs : GoSlice), protoRest etcdserverpb.WatchResponse p dq ∗
    p.[etcdserverpb.WatchResponse, go!"Header"] ↦{dq} h ∗ optOwn respHeaderOwn h dq m.hdr ∗
    p.[etcdserverpb.WatchResponse, go!"WatchId"] ↦{dq} (W64 m.watchId) ∗
    p.[etcdserverpb.WatchResponse, go!"Created"] ↦{dq} m.created ∗
    p.[etcdserverpb.WatchResponse, go!"Canceled"] ↦{dq} m.canceled ∗
    p.[etcdserverpb.WatchResponse, go!"CompactRevision"] ↦{dq} m.compactRev ∗
    p.[etcdserverpb.WatchResponse, go!"CancelReason"] ↦{dq} m.cancelReason ∗
    p.[etcdserverpb.WatchResponse, go!"Fragment"] ↦{dq} m.fragment ∗
    p.[etcdserverpb.WatchResponse, go!"Events"] ↦{dq} evs ∗ msgsOwn eventOwn evs dq m.events ∗
    ⌜-2 ^ 63 ≤ m.watchId ∧ m.watchId < 2 ^ 63⌝

/-- A response persisted (read-only), as the send loop shares its header and events among
fragments and sends read-only messages; a read-only one is persistent. -/
def wireWatchRespOwn_persist.spec : Prop :=
  (∀ (p : Loc) (m : WireWatchRespM),
    wireWatchRespOwn (GF := GF) p (DFrac.own 1) m ⊢ |==> wireWatchRespOwn p DFrac.discard m) ∧
  (∀ (p : Loc) (m : WireWatchRespM), Persistent (wireWatchRespOwn (GF := GF) p DFrac.discard m))

end res

end V3rpc
end EtcdGrove
end Perennial
