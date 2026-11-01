# G2 (b) + (b′): `grpc.serveStream`'s md-indexed contract and the stream interceptors' (2026-10-30)

**Reviewed** (branch `g2-stmts`, `7ec9f1f715`; the change is the diff against `8527537fba`, the design
`notes/g2-watch-auth.md`):

- (b) `grpc.serveStream` (`Proof/google_golang_org/grpc/InvGrpcStream.lean`) with the contract it is
  given, `grpcStreamMethodOk`/`grpcStreamMethodOkR` and `grpcStreamHandlerOk`, now
  metadata-indexed: a run is given `Spec (metadata.incomingOf ci) γ Dn`, `ci` the run's context, and
  `□ ∀ md, streamSpecOk (Spec md)`. The other half of that claim is the client's,
  `grpc.ClientConn.NewStream` (`Spec a md γ Dn` at an `md` with `clientAttemptMd conn ctx md`, so
  `grpcAttemptMd`, `InvGrpc.lean:901`): the transport hands both ends one `Dn`, which is sound only if
  the handler's `incomingOf ci` is an `md` the client's attempt delivers. Both are reviewed here as
  one claim.
- (b′) `srvStreamInterceptorOk` (the handler's continuation now takes a server end at the run's own
  `ci`; `srvStreamChainWP_of_ok` proved over it) and the axiom
  `grpc_prometheus.ServerMetrics.StreamServerInterceptor` (`Spec/github_com/grpc_ecosystem/
  go_grpc_middleware/providers/prometheus/ServerMetrics__StreamServerInterceptor.lean`); etcd's
  `newStreamInterceptor` is proved against the contract (under `runsNoRequireLeader`).

Go at the pins: grpc-go v1.84.0, go-grpc-middleware v2.3.4 and providers/prometheus v1.1.0, x/net
v0.59.0 (etcd's `server/go.mod`), etcd fork `249d76bea7`, toolchain go1.27.3.

## Verdict

- (b′) **survives**: no interceptor the contract admits, and none of the real chain, hands the handler
  a context whose incoming metadata differs from `incomingOf ci`.
- (b) **refuted on the Go side; the Lean proof was not built**. The claim that the handler sees, at
  every key `grpcReservedKey` leaves out, the values the client's attempt sent is false at the key
  **`host`**. grpc-go's server transport deletes `host` whenever `:authority` is present, and grpc-go's
  client always sends `:authority`. A Go program that panics is below. The Lean triple was not proved:
  a client program has no spec that gives it an etcd client's raw connection (`ActiveConnection`), and
  a custom stream service would need its own server start (see "The Lean proof"). The consequence is
  narrow. No spec in the repository reads `host`: etcd's specs read `token`, `authorization`,
  `client-api-version` and `hasleader`, so no exported result is false. The fix is one word in a
  definition (below).

## (b′) The interceptors

**The contract.** `srvStreamInterceptorOk ic R`: the handler's continuation is
`∀ st' cd', srvRawStreamIs st' γ … ci cd' -∗ WP (handler srv st')`, with the same `ci` the interceptor
was called with. `srvRawStreamIs st' … ci cd'` contains `{{True}} st'.Context() {{RET ci}}`. So the
handler's `Context()` returns exactly the value whose `incomingOf` the run's spec was taken at.
`cd'` may differ, but `incomingOf` is a function of the interface value only, and `isContext`'s
descriptor is not read by it. The chain lemma `srvStreamChainWP_of_ok` threads `ci` through every
level (proved). The continuation is a wand under `∧`, so it is used at most once.

**Attacks.**

1. *An interceptor that substitutes a context.* It would have to produce `srvRawStreamIs st' … ci cd'`
   for a stream whose `Context()` returns something else. The triple pins the return value, so this
   cannot be proved.
2. *grpc-prometheus* (`interceptors/server.go:31-39`): `reporter, newCtx :=
   reportable.ServerReporter(ss.Context(), …)`, and the handler gets `&monitoredServerStream{ServerStream:
   ss, newCtx: newCtx, …}`, whose `Context()` returns `newCtx` (`:49-51`). `ServerReporter` is
   `rep.reporter(ctx, …)`, which returns `r, ctx` unchanged on every path (`reporter.go:84-86,
   92-131`). With no options there is no `exemplarFn` and no `labelsFn`, and with those options the
   context is still not touched. So `Context()` returns the same interface value. The axiom's
   `srvStreamInterceptorOk ic True` is true. The counters it bumps (`WithLabelValues` with three
   labels, `.(ExemplarAdder)` on a `*counter`) cannot panic.
3. *etcd's `newStreamInterceptor`* (`server/etcdserver/api/v3rpc/interceptor.go:216-263`): it passes
   `ss` unchanged except in the require-leader branch (`:239-258`), where `ss =
   serverStreamWithCtx{ctx: newCancellableContext(ss.Context()), …}`. That branch is excluded by the
   proof's premise `runsNoRequireLeader`, and it is harmless to the metadata even in Go:
   `cancellableContext` embeds the parent `context.Context`, so `Value(mdIncomingKey{})` is the
   parent's. The contract (the same `ci`) is stronger than Go needs here. The proof does not reach
   the branch.
4. *grpc's own wrapping* (`server.go`, `processStreamingRPC`): the `serverStream` grpc builds carries the
   transport stream's context. The values grpc adds to it, and otelgrpc's `TagRPC` when
   `EnableDistributedTracing` is on (`grpc.go:67`), are `WithValue` children, and propagation
   extraction only reads the incoming metadata. `metadata.NewIncomingContext` is called once, in
   `http2_server.go:544` (and `handler_server.go:413`, the `ServeHTTP` path, which etcd uses only
   behind TLS on a shared port; the model's `grpc.start` is `Serve(lis)`).
5. *The chain order* (`grpc.go:62-65`: prometheus outermost, then etcd's): `newStreamInterceptor` sees
   the `monitoredServerStream`, whose `Context()` is the run's context (attack 2).

**Not tried:** the require-leader branch with a proof (excluded by the premise); interceptors
configured through `gopts` by `embed` (none are stream interceptors at the pin).

## (b) Does the handler's incoming metadata equal what the attempt sent?

**The client** (`internal/transport/http2_client.go`, `createHeaderFields`, `:542-671`) sends
`:method`, `:scheme`, `:path`, `:authority` (always, `:595`, with `callHdr.Host`), `content-type`,
`user-agent`, `te`, optional `grpc-*`. It then sends the per-RPC credentials' data (`:628-633`; keys
lower-cased and validated in `getTrAuthData`/`getCallAuthData`, `:707-713`, `:743-746`), then the
outgoing metadata's `md` and `added`, skipping `isReservedHeader` keys (`:635-658`). Last come
`t.md`'s pairs, which are empty for etcd. Binary `-bin` values are base64-encoded.
`grpcAttemptMd`'s order, credentials then outgoing, `md` then `added`, matches this.

**The server** (`internal/transport/http2_server.go`, `operateHeaders`, `:425-544`) appends each field
to `mdata[name]` in order, decoding `-bin` (the round trip is exact). It drops
`isReservedHeader && !isWhitelistedHeader` fields (`:467`), and every such name is a
`grpcReservedKey` (a `:` prefix, a `grpc-` prefix, `content-type`, `user-agent`, `te`). There are two
special names that `grpcReservedKey` does not cover:

- `connection` (`:461-465`): the stream is reset with `PROTOCOL_ERROR` and no handler runs. That is
  harmless, because the client's stream then fails (a `streamErr` branch). It is not a mismatch.
- **`host`** (`:485-523`): two or more values abort the stream, which is again harmless. If
  `:authority` is present, which grpc-go's client always ensures, `delete(mdata, "host")` (`:522`)
  removes one `host` value. If `:authority` is missing, `host` is renamed to `:authority` (`:518`).
  Either way **the handler never sees a `host` key**. `grpcAttemptMd` says that
  `mdVals md "host" = mdVals cm "host" ++ mdVals (outgoingOf ctx) "host"`, which is `[…, "x"]` after
  `AppendToOutgoingContext(ctx, "host", "x")` (its spec allows `host`: `lowerKey`).

The other points the task asked about hold:

- *Lower-case keys*: `AppendToOutgoingContext` lower-cases (its spec requires `lowerKey`),
  `withVersion` copies `FromOutgoingContext`'s lower-cased map (`client/v3/ctx.go:41-51`), and the
  credentials' keys are lower-cased. The server keys are the header names as sent.
- *Empty keys*: a key with no values sends no field (`mdNorm`, `mdGet md k ≠ some []`). An empty
  value `""` arrives as `[""]`.
- *Invalid values* are rejected at `newClientStream` (`imetadata.Validate`), so the client gets an
  error.
- *Header-list truncation* resets the stream.
- *Cookie crumbs* would be joined only on the `ServeHTTP` path, which is not the model's.

**The counterexample program**, `examples/axiomcx/g2servestream/g2servestream.go`: a Watch service
whose handler answers one `WatchResponse` with `WatchId = len(md[k])`, where `md` is
`FromIncomingContext(st.Context())`. It is served by `grpc.NewServer()`/`Serve(lis)` on a loopback
listener. The client is an etcd client (`clientv3.New`, so etcd's stream interceptor and
`withVersion`, as `dialOk` asks) that opens `pb.NewWatchClient(cli.ActiveConnection()).Watch(ctx)`,
with `ctx = AppendToOutgoingContext(Background(), k, "x")`, and receives. `Main` panics if
`seen("host") == 0`. Error paths return without panicking, as the proof's error branches would.
The test (`GOTOOLCHAIN=go1.27.3 go test -count=20 ./axiomcx/g2servestream/`, in `examples/`):

```
=== RUN   TestMainPanics
    g2servestream_test.go:18: Main panicked: the handler did not see the client's host metadata
--- PASS: TestMainPanics (0.00s)
=== RUN   TestControl
--- PASS: TestControl (0.00s)
ok  	github.com/mit-pdos/etcd-grove/examples/axiomcx/g2servestream	0.094s
```

It panics every run, with no interleaving involved. The control shows that `hostx`, `token` and
`authorization` reach the handler, one value each, while `host` arrives with none.

**The Lean proof (not built).** The derivation from the axioms is short:

1. The handler meets `grpcStreamMethodOk` at `Spec md γ Dn := ∀ j m, Dn j m ⊣⊢ ⌜m.WatchId =
   len (mdVals md "host")⌝`, which is satisfiable at every `md` (`streamSpecOk`: the transport picks
   that `Dn`). `FromIncomingContext.spec` gives `md0 = incomingOf ci`, with `m !! "host" = none ↔
   md0 "host" = none`, so the handler sends `len (mdVals (incomingOf ci) "host")` and meets `Dn`.
2. The client's `NewStream` gives `Spec a md γ Dn` with `clientAttemptMd conn ctx md`, so
   `mdVals md "host" = mdVals cm "host" ++ mdVals (mdAdd _ "host" "x") "host"`, of length at least 1.
   This holds whatever the credentials yield and whatever `Background()`'s outgoing metadata is.
3. The `Recv`ed response has `Dn 0 m`, so `WatchId ≥ 1` and the `== 0` branch is unreachable.

It was not carried to a closed proof. The client needs the raw `grpcConn` of an etcd client, and no
spec gives `Client.ActiveConnection` (`isNewClient` keeps the connection inside the client's
predicates). The alternative is `grpc.NewClient` with etcd's interceptor (`dialOk`'s
`etcdStreamInterceptor`), assembled as `clientv3.New` does. The server side needs
`grpc.NewServer`/`RegisterWatchServer`/`grpc.start`/`Serve` for a service other than etcd's, as
`v3rpc/Results.lean`'s `etcd_watch_served*` do for etcd's: that is a few hundred lines of setup over
specs that exist. No `sorry`, new axiom or extra hypothesis would be needed: the gap is cost, not a
missing fact. Building it is the next step if the user wants the definitive form. No Goose project
was added, so the Go package does not enter `etc/goose.py --check`.

**Which axioms are wrong.** The false claim lives in the definition `grpcAttemptMd` (its
`grpcReservedKey`), which is shared by:

- this stream contract, through `grpc.ClientConn.NewStream` (`clientAttemptMd`) and `grpc.serveStream`
  (the run's `Spec (incomingOf ci)`);
- the unary attempt contract `grpcInvokerOk` (`grpc.ClientConn.Invoke`, the auth plan's E3zb/C1). Its
  server side is the same `operateHeaders`, so the gap is the same there.

**What rests on it.** The collections listing `grpc.serveStream` (`v3rpc`, `watch`, `watchkv`,
`cachekv`, `cache-client`, `linkv3p`) and `grpc.ClientConn.NewStream`/`Invoke` (also `client`,
`lease`, `lease-served`, `authkv`, `putget`, `putget3`, `linkvtxn`, `k8s`, `k8setcd3`, `recipes`,
`m2`, `slice`). None of their results is false. Every metadata-indexed spec in the repository reads
`grpcAttemptMd` only at `token` and `authorization` (`InvClientAuth.lean:349-416`, through
`grpcReservedKey_token`/`_authorization`) and the server's at `client-api-version`/`hasleader`/the
token. All of these are delivered intact. The statements are unsound in general and sound for the
specs actually instantiated.

**Proposed restatement (not applied; a trusted definition, the user's call).** Add `host` to
`grpcReservedKey` (`InvGrpc.lean:885`):

```lean
def grpcReservedKey (k : GoString) : Prop :=
  go!":" <+: k ∨ go!"grpc-" <+: k ∨ k = go!"content-type" ∨ k = go!"user-agent" ∨ k = go!"te" ∨
    k = go!"host"
```

The docstring would say why: "the server drops `host` when `:authority` is present, which grpc's
client always sends, http2_server.go:518-522". `connection` could be added too for symmetry, but it
is not needed, because a stream carrying it never reaches a handler. `grpcReservedKey_token` and
`grpcReservedKey_authorization` are proved by `decide`, which still works. No other proof unfolds the
definition. `NewStream`'s docstring ("reserved keys skipped") and `grpcAttemptMd`'s ("True of grpc-go
v1.84 … to check in C1's phase 2") should cite the server side as well.

This is not an `issues/` finding. grpc-go's handling of `host` is gRFC A41's documented behaviour,
and the bug is in this repository's model.

## Not tried

- *Transparent retry with changing credentials*: grpc may retry a stream's creation (`REFUSED_STREAM`,
  for example when etcd's `MaxConcurrentStreams` is exceeded) after `NewStream` returned. The retry
  recomputes the headers, so `credsYield` may give another token. The client's `md` is existential
  and `clientAttemptMd` holds of every attempt, so the client cannot tell the attempts apart. Within
  etcd's client the token is always the configured user's. Whether a stale token at one attempt and
  a fresh one at the next could be told apart by a token-indexed spec (the watch's `watchSpec R
  (mdTokenOf md)`) was not attempted.
- `incomingOf` as a fixed function of `(type, loc)` under nondeterministic allocation: the caveat of
  `withtimeout-md.md` applies unchanged.
- `runsNoRequireLeader` (a deployment premise, not changed by G2). It could now be stated over the
  client's `clientAttemptMd`.
