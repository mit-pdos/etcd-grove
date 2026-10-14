# gRPC bidirectional streams: a specification proposal, for the generic gRPC specification's author

For: the author of `Proof/google_golang_org/grpc/InvGrpc.lean` (the generic gRPC specification,
units C1/P3a/P3b).
From: the vertical slice's watch unit (`notes/STATUS.md`, "The vertical slice"; the request
path's session).
Status: proposal. Nothing of it is built. The watch slice's server hop (unit W-S, `server/v3/
etcdserver/api/v3rpc/watch.go`) is being proved against a local server-end interface of exactly
this shape (`v3rpc/InvWatchStream.lean`, `srvStreamIs`), so that your axiom instantiates it when
you add streams; the client hop (`client/v3/watch.go`) will use the client end. Names are
proposals; rename them to your conventions.

## 1. What is needed

etcd's `Watch` is a bidirectional stream (`rpc Watch(stream WatchRequest) returns (stream
WatchResponse)`): the client sends create/cancel/progress requests on one stream and receives
responses, each carrying a watch id, a header revision, flags (`Created`, `Canceled`,
`CompactRevision`, fragments) and events. The unary specification (`GrpcSpec Req Rep := Req.M →
(Rep.M → IProp) → IProp`, `grpcHandlerOk`, `isGrpcRpc`, `grpc.serve`) does not cover it: there is
no single request and reply, the server pushes responses on its own (the send loop over mvcc's
watch stream), and the client reads them in order.

## 2. The model: two reliable FIFO queues per stream

A stream, once established, is two reliable, ordered, lossless message queues: up (client →
server, `Req.M` messages, ended by the client's `CloseSend` or the stream's end) and down (server
→ client, `Rep.M` messages, ended by the handler's return). The runtime transports each message
intact (the same `ProtoMsg` round-trip as the unary case). Ghost state: two mono-lists, `upQ γ L`
and `downQ γ L` (the authority with the sender, lower bounds with the receiver), as the repository's
SPSC channel idiom (`Perennial/Golang/Theory/Chan/Idioms/Spsc.lean`: `spscProducer`/
`spscConsumer`, `monoListIdxOwn`) does for an in-process channel.

- **The server end** (`grpc.ServerStream` as the generated `Watch_WatchServer` wraps it):
  `srvStreamIs (st : GoInterface) (γ : StreamNames) (Req Rep : ProtoMsg GF) (Dn : Nat → Rep.M →
  IProp GF)` (persistent), with `Dn i m` the handler's own content for the `i`th message sent
  down (what the client may learn of it: the handler chooses `Dn` when it registers; for `Watch`
  it is "the `i`th response's events are the mvcc watch guarantee's", see §4):
  - `Recv()`: `{{ srvRecvTok γ L }} st.Recv() {{ (req, err); (⌜err = nil⌝ ∗ ∃ l m, Req.recv l m ∗
    srvRecvTok γ (L ++ [m])) ∨ (⌜err = io.EOF⌝ ∗ srvRecvTok γ L ∗ upClosed γ L) ∨ (⌜err ≠ nil⌝ ∗
    clientErr err ∗ srvRecvTok γ L) }}` (the receiver's token `srvRecvTok γ L`: `L` the requests
    received so far; the up queue's `i`th message is the `i`th the client sent, `upQ_agree`);
  - `Send(resp)`: `{{ srvSendTok γ L ∗ Rep.send l m ∗ Dn L.length m }} st.Send(l) {{ err;
    (⌜err = nil⌝ ∗ srvSendTok γ (L ++ [m])) ∨ (⌜err ≠ nil⌝ ∗ srvSendTok γ L) }}` (on an error
    the message may or may not have been delivered: the client's view below allows a prefix);
  - `Context()`: `{{ True }} {{ ctx; isContext ctx cd ∗ grpcRunCtx ctx }}` for the run's context
    (cancelled when the client goes away: its `Done` is the stream's end, as `Watch` uses it).
- **The client end** (`grpc.ClientStream` as `Watch_WatchClient` wraps it): `cliStreamIs (cs :
  GoInterface) (γ : StreamNames) Req Rep Dn` (persistent):
  - `Send(req)`: `{{ cliSendTok γ L ∗ Req.send l m }} cs.Send(l) {{ err; (⌜err = nil⌝ ∗ cliSendTok γ
    (L ++ [m])) ∨ (⌜err ≠ nil⌝ ∗ clientErr err ∗ cliSendTok γ L) }}`;
  - `Recv()`: `{{ cliRecvTok γ L }} cs.Recv() {{ (resp, err); (⌜err = nil⌝ ∗ ∃ l m, Rep.recv l m ∗
    □ Dn L.length m ∗ cliRecvTok γ (L ++ [m])) ∨ (⌜err = io.EOF⌝ ∗ cliRecvTok γ L ∗ downClosed γ L)
    ∨ (⌜err ≠ nil⌝ ∗ clientErr err ∗ cliRecvTok γ L) }}` (the `i`th message received is the `i`th
    the server sent, with its content `Dn i m`: the client learns it once per message; `Dn` may be
    exclusive, delivered with the message);
  - `CloseSend()`: `{{ cliSendTok γ L }} {{ err; upClosed γ L }}`.
- **Establishing a stream**: the generated stub `watchClient.Watch(ctx, opts...)` calls
  `conn.NewStream(ctx, &StreamDesc, "/etcdserverpb.Watch/Watch", opts...)`: the axiom (the
  streaming analogue of `ClientConn.Invoke`): `{{ grpcConn conn addr … ∗ isGrpcStream addr name
  Spec ∗ isContext ctx cd ∗ callOptsOk vs }} conn.NewStream(ctx, desc, name, opts) {{ (cs, err);
  (⌜err = nil⌝ ∗ ∃ γ Dn, cliStreamIs cs γ Req Rep Dn ∗ cliSendTok γ [] ∗ cliRecvTok γ [] ∗ Spec γ
  Dn) ∨ (⌜err ≠ nil⌝ ∗ clientErr err) }}` where `Spec : StreamNames → (Nat → Rep.M → IProp) →
  IProp` is the registered method's stream specification: what the handler promises about the
  down queue's contents relative to the up queue's (for `Watch`: `Dn` is determined by the
  requests the client sent, §4; the client reads `Spec γ Dn` to know `Dn`).
- **Serving**: `grpc.serve`'s registrations gain stream methods (`StreamDesc.Handler`: the
  generated `_Watch_Watch_Handler(srv, stream)` calling `srv.Watch(&watchWatchServer{stream})`):
  `grpcStreamMethodOk mh srv ics S Spec := ∀ γ Dn ci cd, {{ S ∗ isContext ci cd ∗ grpcRunCtx ci ∗
  srvStreamIs st γ Req Rep Dn ∗ srvRecvTok γ [] ∗ srvSendTok γ [] ∗ (the chain) }} mh srv st {{
  err; S ∗ Spec γ Dn }}`: a run of the handler with a fresh stream's server end and both tokens,
  returning the run slot and the stream specification; `isGrpcStream addr name Spec := ∃ …,
  grpcServes addr name … ∗ grpcStreamMethodOk …` (persistent), obtained from `grpc.serve` as
  `isGrpcRpc` is. One run slot per open stream (gRPC's `MaxConcurrentStreams`: the pool bound,
  as for unary runs).
- **The transport's claims** (the trust boundary, as the unary axiom's): intact, ordered,
  lossless delivery per direction while the stream lives; `Recv` returns `io.EOF` exactly when
  the other side closed its direction and everything sent before was received; after an error,
  nothing (a prefix may have been delivered); the server's run starts when the client's
  `NewStream` returns (the handler may be entered later, but no message is lost in between).

## 3. Why ghost queues and not a predicate transformer

A unary call has one request and one reply, so `Spec m Φ` says it all. A stream's handler makes
an unbounded number of sends whose contents depend on the whole history of requests and on the
server's own state (the mvcc watch stream's deliveries); the client consumes them one at a time
and must relate the `i`th response to the `i`th request it sent (the create request's watch id
appears in later responses). Indexed queues give exactly that, and the SPSC idiom gives the
lemmas (`monoListIdxOwn` agreement by position). `Dn i m` is the per-message content the client
learns, indexed by position so that the handler can promise "the response at position `i` for
watch id `w` carries the mvcc guarantee's events for the `k`th delivery of `w`".

## 4. What `Watch`'s stream specification will say (the watch slice's unit W-S)

`watchStreamSpec γ Dn := ∀ i m, Dn i m ⊣⊢ (the response m at position i is: a control response
(Created, Canceled with reason, or the compaction response) for a create/cancel request at some
earlier up position, with the watch id the server assigned; or an events/progress response for a
watch id created earlier, whose events are the next delivery of that watcher's mvcc watch
guarantee (`mvcc.watchRecvOk`/`watchGuarantee_unfiltered`: the certified log's events in the
watcher's range from its start revision, in order, no gap), with the header revision at or above
the events' revisions)`. Stated in `v3rpc/InvWatchStream.lean` against `srvStreamIs` as above; the
client slice derives from it the cache's `rangeWatchElem` chain (`EtcdStep` facts of the server's
model instance between consecutive responses).

## 5. Open points

- Fragments (`WithFragment`: a response split across several sends with `Fragment = true`) and
  filters: the recipes use neither; W-S states the unfragmented, unfiltered case and leaves the
  others as premises (a filter function's contract exists in mvcc: `WatchParams.F`).
- The client's reconnection (`client/v3/watch.go`'s `openWatchClient`/resume): a new stream per
  reconnect; `Spec` is per stream, and the client proves the resumed substreams' continuity from
  the start revisions it sends. Nothing in §2 needs to know about it.
- Progress requests (`RequestProgress`): an up message with a down response for watch id `-1`;
  `Dn` covers it (a progress response's revision is the store's current one).
- `grpc.serve`'s pool: one slot per stream for its whole life (the handler returns when the
  stream ends), so a server with `N` slots serves at most `N` watch streams at a time plus the
  unary runs: say whether the pool is shared or separate.
