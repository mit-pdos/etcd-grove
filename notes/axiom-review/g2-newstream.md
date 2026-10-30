# Axiom review: G2's `ClientConn.NewStream` and `dialOk` (2026-10-30)

**Reviewed** (branch `g2-stmts`, `7ec9f1f715`; the change against `8527537fba`; grpc-go v1.84.0,
etcd's fork at `249d76bea7`, go1.27.3, amd64), as G2 strengthened them in place
(`notes/g2-watch-auth.md`, "Trusted statements changed", (a) and (a′)):

- (a) `grpc.ClientConn.NewStream.wp_proof` (`Proof/google_golang_org/grpc/ClientConn__NewStream.lean`;
  the triple `Spec/google_golang_org/grpc/ClientConn__NewStream.lean`): the registration is
  metadata-indexed (`isGrpcStreamsMd`) and the stream's specification is the registration's at
  some `md` with `clientAttemptMd conn ctx md`, i.e. `clientAttemptMdOf conn (outgoingOf ctx) md`
  (`Proof/go_etcd_io/etcd/client/v3/InvKVConn.lean`): `md` is what `grpcAttemptMd conn c md`
  (`Proof/google_golang_org/grpc/InvGrpc.lean`) says an attempt on `withVersion(ctx)`'s context `c`
  delivers: at every key `k` with `¬ grpcReservedKey k`, the per-RPC credentials' values for the
  attempt (`credsYield conn cm`) then `c`'s outgoing metadata; no key with no values.
- (a′) `grpc.NewClient.wp_proof` through `dialOk` (`Proof/google_golang_org/grpc/InvDial.lean`,
  `Spec/google_golang_org/grpc/NewClient.lean`): a dial's stream interceptors are all etcd's
  (`etcdStreamInterceptor`) and there is one.

Read with them: `grpc.serveStream` and `grpcStreamMethodOkR` ((b): the server's run is given
`Spec (incomingOf ci)`), `etcdStreamInterceptor`'s producer
(`Client.streamClientInterceptor.spec`), `getToken`, `withVersion`, `cliStreamIs`, `cliStreamErr`.
Method: `.claude/skills/axiom`.

## Verdict: (a) refuted (counterexample proved); (a′) survives

### (a) The handler does not see `"host"`: counterexample proved

**The claim.** For an attempt's metadata `md`, `mdVals md k = mdVals cm k ++ mdVals (outgoingOf c) k`
for every `k` that is not a `grpcReservedKey` (`:`-prefixed, `grpc-`-prefixed, `content-type`,
`user-agent`, `te`). `"host"` is none of these, so a stream opened on a context whose outgoing
metadata has `"host": ["x"]` gets the registration's specification at an `md` with a value at
`"host"`.

**Why it is false.** grpc-go's client writes the outgoing metadata's `"host"` as a header field
(`isReservedHeader` does not skip it: `internal/transport/http_util.go:96-116`;
`http2_client.go:635-658`) and always sends `:authority` (`http2_client.go:595`). The server
reads the header block into `mdata` (`http2_server.go:466-476`: `"host"` is not reserved there
either) and then, per gRFC A41, `"If :authority is present, Host must be discarded"`:
`delete(mdata, "host")` (`http2_server.go:513-523`; with no `:authority`, `host` is renamed to it).
So the handler's incoming metadata never has `"host"`. (Two `"host"` values abort the stream at
`:485`; one is deleted.) The axiom hands the client `Spec a md γ Dn` at an `md` the server's run
never sees: the server's run is given `Spec (incomingOf ci) γ Dn` for the same `Dn` (b), with
`incomingOf ci` without `"host"`, and a `Spec` that reads `"host"` lets the two ends disagree.

**The counterexample**:

- Go: `examples/axiomcx/g2newstream/g2newstream.go`. `Handler` (a `StreamDesc.Handler`) answers one
  `*pb.LeaseKeepAliveResponse` with `ID` = `hasHost(stream.Context())`: `1` if
  `metadata.FromIncomingContext` has a value at `"host"`, else `0`. `Check(parent, conn)` opens a
  client stream of `/axiomcx.Echo/Echo` on `conn` with
  `metadata.AppendToOutgoingContext(parent, "host", "x")`, receives one response, and panics unless
  its `ID` is `1`.
- Test (`g2newstream_test.go`; `cd examples && GOTOOLCHAIN=go1.27.3 go test -v
  ./axiomcx/g2newstream/`): an in-process grpc server (`grpc.NewServer()`, no interceptor, the
  method registered with `Handler`), an etcd client to it (`clientv3.New`, so `dialOk`'s dial with
  etcd's stream interceptor), `Check(ctx, cli.ActiveConnection())`:
  `Check panicked: NewStream: the handler saw no "host" metadata` (deterministic). The control
  test opens a stream with `"host"` and `"x-host"`: the handler sees `x-host: ["x"]`,
  `client-api-version: ["3.8"]` (etcd's interceptor's `withVersion`), `:authority:
  ["127.0.0.1:…"]`, and no `host`.
- Translation: project `axiomcx-g2newstream` of `etc/goose.py` (`Code/`,
  `GeneratedProof/.../examples/axiomcx/g2newstream.lean`).
- Proof: `Proof/github_com/mit_pdos/etcd_grove/examples/axiomcx/g2newstream/Main.lean`, no `sorry`:
  - `echoSpec md γ Dn := ⌜Dn = echoDn md⌝`, `echoDn md _ r := ⌜r.1 = hostFlag md⌝` (`hostFlag md` is
    `1` iff `mdVals md "host" ≠ []`), at the trusted wire model `pbLeaseKeepAliveResponse`
    (`InvLessor.lean`) for the messages;
  - `hasHost.wp_proof`, `Handler.wp_proof` (from `FromIncomingContext.spec`), `echoMethodOk`
    (`grpcStreamMethodOk`), `echo_served` (`grpc_serveStream_rpcs` from `grpcStreamServerAt addr []
    sregs`, the server's construction, a premise as in `etcd_watch_served`);
  - `hostFlag_attempt`: `clientAttemptMd conn ctx md` and `outgoingOf ctx = mdAdd M "host" "x"` give
    `hostFlag md = 1` (from `grpcAttemptMd` at `"host"`, `¬ grpcReservedKey "host"` by `decide`);
  - `Check.wp_proof`: `{{ isPkgInit g2newstream ∗ isContext parent cd ∗ grpcConn conn [addr] ics []
    ∗ isGrpcStreamMd addr method echoUp echoSpec }} Check parent conn {{ RET #(); True }}`, from the
    specs of `AppendToOutgoingContext` and `NewStream`: the response's `ID` is `hostFlag md = 1`, so
    the `panic` branch is unreachable;
  - `Check_served.wp_proof` (the registration from `echo_served`), and `Check_served_axioms`, the
    same from the axioms.
- `#print axioms Check_served_axioms`, against `#print axioms hasHost.wp_proof` (both in the
  file): the same 486 (Lean's three, and the axiomatized types and package facts every proof that
  imports grpc's and etcd's names-only translations prints), plus exactly: the axiom under review
  `grpc.ClientConn.NewStream.wp_proof`; `grpc.serveStream` ((b), the server side); the two metadata
  specs `metadata.AppendToOutgoingContext.wp_proof` and `metadata.FromIncomingContext.wp_proof`;
  the opaque predicates `grpcConn`, `grpcServesStream`, `grpcStreamServerAt` and their persistence.
  None of the extra ones is what fails: `AppendToOutgoingContext` and `FromIncomingContext` are
  true of the run (the test shows `x-host` delivered; `FromIncomingContext` returns the handler's
  real metadata, without `host`); `serveStream` gives the run `Spec (incomingOf ci)` at the real
  metadata, which is what (b) claims and what the handler reads. The triple's premises hold in the
  test: `conn` is `clientv3.New`'s connection (`grpcConn`, from `NewClient` with `dialOk`'s
  options), the server is built with no interceptor and the method registered with `Handler`
  (`grpcStreamServerAt addr [] sregs`).

**What rests on it.** The collections listed in `notes/g2-watch-auth.md` for (a): cachekv, watch,
cache-client, watchkv, lease-served, linkv3p, client, lease (taken from that table; not re-run
with `etc/tcb-report.py --roots`, which needs a full up-to-date build). No proof reads an attempt's
metadata at `"host"`: they read the token (`auth.mdTokenOf`, key `token`) and the client's own
outgoing metadata (`streamKeyOf`), so no exported result is shown false; the statement they rest
on is.

**The same flaw in the unary path.** `grpcAttemptMd` is also the attempt contract's
(`grpcInvokerOk`, which restates the `grpc.ClientConn.Invoke` axiom's promise since C1,
2026-10-28): grpc's server takes the same `operateHeaders` path for unary calls, so a unary
handler does not see `"host"` either. Not attacked separately (the counterexample would be the
unary twin of this one); the fix below covers both.

**Proposed restatement (not applied: a trusted change, the user's).** Add `"host"` to
`grpcReservedKey` (`InvGrpc.lean`):
`go!":" <+: k ∨ go!"grpc-" <+: k ∨ k = go!"content-type" ∨ k = go!"user-agent" ∨ k = go!"te" ∨
k = go!"host"`, with the docstring's reason (`http2_server.go:513-523`, gRFC A41: the server
discards `host` when `:authority` is present, and grpc's client always sends `:authority`).
`grpcAttemptMd` then says nothing at `"host"`. Every consumer reads `token`, which stays covered;
`hostFlag_attempt` would no longer be provable (its `host_not_reserved` fails). `connection`
(`http2_server.go:461`: the stream is reset, no handler runs) needs nothing: a stream whose
handler never runs gives the client no response to contradict.

### (a′) `dialOk`: survives

Every dial `dialOk` admits makes NewStream's metadata claim hold up to the flaw above:

- **The interceptor runs.** grpc's `chainStreamClientInterceptors` (`clientconn.go:549-568`) runs
  `dopts.streamInt`, the last `WithStreamInterceptor`'s, then grpc's `defaultStreamInterceptor`
  (`stream.go:232`, which only wraps the returned stream); no descriptor sets `chainStreamInts`.
  `dialOk` makes every `.streamInterceptor` etcd's and requires one, so the connection's is
  etcd's `streamClientInterceptor` (`retry_interceptor.go:117-161`), whose first step is
  `ctx = withVersion(ctx)` (`ctx.go:41-51`: `FromOutgoingContext`, copy, `Set` the version key,
  `NewOutgoingContext`): `outgoingOf c = mdSet (outgoingOf ctx) "client-api-version" [v]`. The
  earlier round's gap (a dial with no stream interceptor, where nothing sets the version key) is
  closed.
- **Another client's interceptor.** `etcdStreamInterceptor si` is not tied to the dialing client:
  a dial may carry client A's interceptor on client B's connection. A's `getToken` then updates
  A's credentials, not the connection's; the claim speaks only of the connection's
  (`credsYield conn cm`, existential per attempt), so it still holds.
- **`getToken`'s token.** With a user name the interceptor calls `getToken` before grpc's streamer
  (`retry_interceptor.go:123-127`); the token reaches the headers only through the connection's
  per-RPC credentials (`http2_client.go:689-716`, `authData`, lower-cased keys, one value each),
  which is `cm`. An error of `getToken` returns `nil, err`: NewStream's error branch.
- **Address metadata.** `t.md` (headers from a resolver address's metadata,
  `http2_client.go:384-388,660-669`) would add values the claim does not list; etcd's
  `EtcdManualResolver` builds addresses with `Addr` and `ServerName` only
  (`client/v3/internal/resolver/resolver.go:66-75`), and `dialOk` fixes the resolver to `rb`.

### Other attacks tried on (a), and why each failed

- **Reserved keys.** grpc's client skips exactly `isReservedHeader`'s keys (`:`-prefixed,
  `content-type`, `user-agent`, `grpc-message-type`, `grpc-encoding`, `grpc-message`, `grpc-status`,
  `grpc-timeout`, `te`), all within `grpcReservedKey`; `grpc-previous-rpc-attempts` and other
  `grpc-` keys are sent but the claim says nothing at them. Server side, `content-type`,
  `grpc-accept-encoding` and `user-agent` are kept, all reserved in the claim. Only `host` slips
  through (above).
- **Keys and values grpc rejects.** Upper-case keys or invalid values in the outgoing metadata:
  `newClientStream` validates it (`stream.go:322-334`) and fails the call (the error branch); the
  model's `outgoingOf` excludes keys colliding up to case. `-bin` values round-trip through
  base64.
- **Empty value lists.** A key with no values is not sent; the claim's `mdGet md k ≠ some []`
  matches.
- **Order and duplicates.** Credentials' values first (`authData`), then the metadata's, then
  `added` (`http2_client.go:628-658`); the server appends in header order: `cm ++ outgoing`.
- **Transparent retry** of the stream's creation rebuilds the headers (credentials called again)
  but only when the first attempt's handler never ran: `md` is existential, one per stream.
- **Call options adding metadata.** `grpc.PerRPCCredentials(...)` as a call option would add
  `callAuthData`; it is not among `streamCallOptsOk`'s options (`grpcScalarOptTys`, retry options).
- **`getToken`'s `EtcdError`.** After `New`, a changed password makes the interceptor's
  `getToken` return `rpctypes.ErrAuthFailed` (an `EtcdError`) from NewStream. `cliStreamErr`'s and
  `grpcInvokerOk`'s docstrings call `clientErr` "not an `EtcdError`", but `clientErr`
  (`ClientErr.lean`) admits one (a leaf whose `As` is well-typed), and `statusErrOk`/`streamErr`
  hold of it: no gap in the statement. The two docstrings are wrong (this repository's, to fix
  with the restatement).
- **A context whose `Value` changes** (a user type under `ctxQuiet`): `outgoingOf` is a function of
  the context value; NewStream reads the context once (`withVersion`'s snapshot), so one call
  cannot disagree with itself; two calls would need another axiom to pin `outgoingOf` of that
  type (the convention recorded in `withtimeout-outgoing.md`, "Remarks").

Not tried: the stream's later messages and `Recv`/`Send` claims (unchanged by G2), and the
server-side axioms (b), (b′) on their own beyond what the counterexample uses.

## Where things are

- Go: `examples/axiomcx/g2newstream/` (package and test).
- Translation: project `axiomcx-g2newstream` in `etc/goose.py` (on this branch only, as
  `axiomcx-bboltnan`).
- Proof: `Proof/github_com/mit_pdos/etcd_grove/examples/axiomcx/g2newstream/Main.lean` (`lake build
  Proof.github_com.mit_pdos.etcd_grove.examples.axiomcx.g2newstream.Main`).
