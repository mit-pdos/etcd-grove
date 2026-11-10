# The network as trusted operational models: grpc and net/http at their APIs (design for review)

Design note, 2026-11-10 (specs-only at `157a6903c5`), **for the user's review: nothing here is
built**. It implements the decision recorded in `open-questions.md` (2026-11-10, "The new test"):
grpc-go and net/http are **trusted operational models at their APIs**, a GooseLang extension over
the network between the nodes of Perennial's distributed language (`DistLang.lean`,
`goose_dist_crash_adequacy`), **no TCP model beneath**, justified by grpc's and net/http's documented
behavior. The program: several etcd members, each a node that crashes alone and reruns its boot
program, and a client node that never crashes (clientv3 over grpc); members talk over rafthttp
(net/http). The goal is that every `Spec/google_golang_org/grpc/**` and `Spec/net/http/**` statement
(E1, E7 of `trust-boundaries.md`) becomes a **theorem** proved from the model, so the adequacy
theorem has no Iris axiom for the network.

A draft of the extension's semantics, which **typechecks** against the pinned Perennial (`lake env
lean`), is at `/home/ubuntu/.claude-E/jobs/b4c3a1d2/tmp/netext-draft/Impl.lean` (575 lines, 39
operations; not in the repository, not in Perennial). Section 3 summarizes it, and the file is the
precise statement.

Contents: 1. the API surface the program reaches; 2. the cut; 3. state and crash; 4. operations;
5. messages as values; 6. at-most-once, retries, deadlines, endpoints, errors; 7. justification and
known gaps; 8. size, and what it lets us prove; 9. open choices.

## 1. The API surface the program reaches

Enumerated from the pinned code: clientv3 (`client/v3`, `client/v3/internal/resolver`), the
server (`server/v3/embed`, `etcdserver/api/v3rpc`, `etcdserver/api/rafthttp`, `etcdserver/
{cluster_util,corrupt}.go`, `lease/leasehttp`), `client/pkg/v3/transport`, cmux v0.1.5, grpc-go
v1.84.0 (`examples/go.mod`), Go 1.27.3 (`etc/goose.py`'s `GO_TOOLCHAIN`).

**grpc, client side** (clientv3, `client.go`, `options.go`, `internal/resolver/resolver.go`):
`grpc.NewClient(target, opts...)` (`client.go:328`) with `WithTransportCredentials(insecure)`,
`WithResolvers` (a `resolver/manual` builder: `NewBuilderWithScheme`, `UpdateState`, `CC`, `Build`,
`Close`; `cc.ParseServiceConfig({"loadBalancingPolicy": "round_robin"})`, `resolver.go:38-75`),
`WithUnaryInterceptor`/`WithStreamInterceptor` (the retry interceptors, `retry_interceptor.go`),
`WithPerRPCCredentials` (the token bundle), `WithKeepaliveParams`, `WithDefaultCallOptions`
(`WaitForReady(true)`, `MaxCallSendMsgSize`, `MaxCallRecvMsgSize`, `options.go:26-63`);
`ClientConn.Invoke` (generated unary stubs), `ClientConn.NewStream` (Watch, LeaseKeepAlive, the
generated `GenericClientStream`), `ClientStream.{SendMsg,RecvMsg,CloseSend,Context,Header,
Trailer}`, `ClientConn.Close`, `Target`; `grpc.Peer`; `status.{FromError,Convert,Code}`, `codes`,
`metadata.{NewOutgoingContext,AppendToOutgoingContext,FromOutgoingContext,Pairs}`.

**grpc, server side** (`v3rpc/grpc.go:40-80`, `embed/serve.go:120-290`, `embed/etcd.go:470-520`):
`grpc.NewServer` with `CustomCodec(&codec{})` (`v3rpc/codec.go`: `proto.Marshal`/`Unmarshal`),
`MaxRecvMsgSize`, `MaxSendMsgSize`, `MaxConcurrentStreams`, `KeepaliveParams`,
`KeepaliveEnforcementPolicy`, `ChainUnaryInterceptor`, `ChainStreamInterceptor` (`Creds` and
`StatsHandler` only with TLS / tracing: off); `RegisterService` (the generated `Register*Server`,
`healthpb.RegisterHealthServer`); `Serve(lis)` (`serve.go:200`, `:213`, `:274`); `GracefulStop`,
`Stop` (`etcd.go:495-520`); handlers through `MethodDesc.Handler`/`StreamDesc.Handler` with the
chained interceptor; `ServerStream.{SendMsg,RecvMsg,Context}`; `metadata.FromIncomingContext`,
`peer.FromContext`. `ServeHTTP` only on the TLS path (`serve.go:317`).

**net/http, client side** (rafthttp's pipeline, stream and snapshot senders; `cluster_util.go`,
`corrupt.go`, `leasehttp/http.go`): `http.NewRequest`, `Request.WithContext`, `Header.{Set,Get}`;
`RoundTripper.RoundTrip` on the `*http.Transport` built by `transport.NewTimeoutTransport`/
`NewTransport` (`client/pkg/transport/timeout_transport.go`: `Dial` is `rwTimeoutDialer.Dial`,
which wraps `net.Dialer.Dial`'s connection in `timeoutConn`, `timeout_dialer.go`), and
`(*http.Client).{Do,Get}` over such a transport; `Response.{StatusCode,Header,Body}`, `Body.
{Read,Close}`, `io.ReadAll`; `Transport.CloseIdleConnections`.

**net/http, server side**: `http.Server{Handler, ReadTimeout, ...}.Serve(l)` (`etcd.go:604`,
`serve.go:207`), `Shutdown(ctx)` (`etcd.go:617`), `http.Serve` (metrics, off in the test),
`NewServeMux`, `ServeMux.Handle` (`etcdhttp.NewPeerHandler`, rafthttp's `/raft`, `/raft/stream/`,
`/raft/snapshot`, `/raft/probing`; `/members`, `/version`, `/leases`, ...), handlers'
`ResponseWriter.{Header,WriteHeader,Write}`, `w.(http.Flusher).Flush()` (`rafthttp/http.go:160`,
`:451`, `stream.go:187`, `:214`), `Request.{Method,URL.Path,Header,Body,RemoteAddr,Context}`,
`http.Error`, `http.StatusText`. No `Hijack`; no `CloseNotify` on a `ResponseWriter` (the only
`CloseNotify` is `snap.Message`'s own).

**net** (under all of the above): `net.Listen`/`ListenConfig.Listen` (`transport/listener.go:102-115`),
`TCPListener.{Accept,Close,Addr}`, `net.Dialer.{Dial,DialContext}`, `TCPConn.{Read,Write,Close,
SetDeadline,SetReadDeadline,SetWriteDeadline,SetKeepAlive,SetKeepAlivePeriod,LocalAddr,RemoteAddr}`.

**etcd's own code between net and the libraries** (translated, so it must *run* in the model):
every listener is wrapped. Peer listeners: `keepaliveListener` (whose `Accept` type-asserts
`*net.TCPConn`, `keepalive_listener.go:65-75`) under `rwTimeoutListener` (`timeoutConn`'s `Read`/
`Write` set a deadline and delegate, `timeout_conn.go`) under cmux with `cmux.Any()` (`etcd.go:598`;
`Any` reads nothing, `matchers.go:30`). Client listeners: `keepaliveListener` under
`LimitListener` (`etcd.go:703-720`; a slot released by the connection's `Close`), and, unless the
client HTTP URLs are split off, cmux with `HTTP1()`/`HTTP2()` matchers that *read* the first bytes
(`serve.go:141-213`, `matchers.go:91-124`). rafthttp's client connections are `timeoutConn`s from
its dialer. This is what forces the one piece of byte-level machinery in the design (section 3,
"Prefaces"; open choice C1).

## 2. The cut

* **The extension** (`GooseLang/Ext/GoNet/{Impl,Specs,Adequacy}.lean` in this repository, named
  `"net"`): the network's state and ~39 primitive steps: listeners, connections, HTTP exchanges,
  gRPC streams (section 4). Its semantics is the trusted part, stated relationally like OsFs.
* **TrustedCode models** (GooseLang, `TrustedCode/net.lean`, `TrustedCode/net/http.lean`,
  `TrustedCode/google_golang_org/grpc.lean` and `grpc/resolver/manual.lean`): the Go functions of
  section 1, written as GooseLang over the extension's operations, as grpc-go and net/http's code
  would behave: the accept loops, per-connection and per-stream goroutines, the method registry,
  interceptor chaining, transparent retry, the endpoint pick, size checks, status mapping, the
  `ServeMux`'s routing. They call the **program's own code where the libraries do**: dialers and
  listeners and their wrappers, `ResponseWriter` users, request-body readers, codecs, interceptors,
  per-RPC credentials, resolver builders, handlers. Also trusted (each model's docstring says why
  it is faithful, as `TrustedCode/os.lean`'s do).
* **Translated, hence verified**: etcd's wrappers (`client/pkg/transport`), cmux, clientv3's
  resolver and interceptors, grpc's small pure packages (`metadata`, `peer`, `codes`, `health`,
  the generic stream wrappers of `stream_interfaces.go`), `net/http`'s pure helpers (`Header`,
  `StatusText`, `Error`) where Goose takes them.
* **Not the network's**: protobuf (`proto.Marshal`/`Unmarshal`, E2) is called by the codecs as
  program code; its trust is E2's alone (section 5).

## 3. State and crash

**Local state** (per node; the extension's `LocalState`): `Owner = {node, epoch}`, the node and its
incarnation. **Crash** (`ExtSemantics.crash`): `node' = node`, `epoch' = epoch + 1`.

**Global state** (`GlobalState`, the network):

* `plan : address → node`, **the deployment**: the address strings the program may listen at or
  dial, each the node that may listen at it. Fixed: an execution starts with it, no step changes
  it (as OsFs's fixed domain of files). `Listen` of an address not the node's, and `Dial` of an
  address outside the plan, are **stuck**: the proof must show the program uses only plan strings.
  This replaces today's environment premise "one reserved string per socket" (`Http.addrFree`,
  `Spec/net/http/Api.lean` header): aliases (`localhost:p` vs `127.0.0.1:p`) and port `0` are simply
  outside the model.
* `bound : address → listener`; `lis : id → {addr, owner, isOpen, backlog}`: the listeners, each
  with the connections dialed to it and not yet accepted.
* `conns : id → {listener, addr, dialer : Owner, acceptor : Option Owner, up/dn byte pipes, claimed
  flags, broken, draining, its HTTP exchanges in order and how many the server took, its gRPC
  streams}`.
* `hxs : id → {conn, request line and headers, body (bytes, read position, end: open / complete /
  aborted), started, taken, committed status and headers, response body, canceled}`.
* `gss : id → {conn, method, metadata, timeout, state ∈ draft | pending | refused | dispatched,
  up and down message queues (each a list of byte strings, a read position, closed), header and
  trailer metadata, fin : status (code, message), reset}`.
* `next`: fresh identities.

Every end (a listener, either end of a connection, and through it either end of an exchange or a
stream) is **owned by one incarnation**: the one that made it (`Listen`, `Dial`) or accepted it.
Every operation checks that the caller owns the end it acts on (else stuck).

**What a crash of node `n` does.** DistLang's crash keeps the global state as it is ("a crash
changes neither the other nodes nor the global state", `DistLang.lean`), so the effects are what
the ownership rule and nondeterminism make of the unchanged records:

* Its threads are gone (DistLang) and so is its heap; its old incarnation's ends have no owner able
  to act on them (the new incarnation is `epoch + 1`, and owns none of them). So nothing it had
  accepted is ever taken, read or answered again: an HTTP request or gRPC stream sent to the dead
  incarnation is never dispatched by the new one.
* Its servers vanish: their accept loops are dead. Until the node reboots and listens again, a
  peer's `Dial` may still land in the dead listener's backlog (a connection never accepted), or
  fail. The next incarnation's `Listen` of one of its plan addresses **takes it over** (`Bindable`:
  the bound listener's owner is the same node at a smaller epoch): the dead listener closes and its
  unaccepted connections break.
* Peers' operations on the other ends may fail at any time (they always may: section 6), and may
  also still succeed where reality allows it: a response the dead server finished before the crash
  may still be read; a request the dead client sent may still be served by a live server.
* Nothing of other nodes changes; the client node never crashes.

**Prefaces: how a model finds its connection behind etcd's wrappers.** A model of `Serve` gets a
`net.Conn` from `l.Accept()` that is etcd's or cmux's wrapper around the base connection, and the
model of `RoundTrip` gets one from rafthttp's dialer. With no byte-level HTTP, the model needs the
base connection's identity. Design (C1, recommended): connections carry **byte pipes, used only for
prefaces**. A client model takes a fresh preface (`Nonce`: a protocol-looking magic, HTTP/2's client
preface for gRPC or a request line for HTTP/1, then 8 bytes of a fresh id), writes it **through the
connection the program's dialer returned** (so the wrapper's `Write` runs), and claims the base
connection whose pipe holds exactly those bytes (`ClaimD`). A server model reads the preface
**through the connection the program's listener accepted** (wrappers' and cmux's `Read`s run) and
claims the accepted base connection from which exactly those bytes were read (`ClaimA`). If a
wrapper altered the bytes, there is no such connection and the model is stuck: sound. After the
claim, all traffic is records (HTTP exchanges, gRPC streams), not bytes. The magic makes cmux's
matchers classify the connection as the real protocol would (`HTTP2()` reads exactly HTTP/2's
24-byte preface, `HTTP1()` a request line), and its sniffed bytes are replayed to the matched
listener's model, which then reads the preface.

## 4. Operations

### 4.1 The extension's steps (`Impl.lean`'s `IsStep`; every waiting operation may also stutter)

| group | operation | step (successes; then failures) |
|---|---|---|
| net | `Listen(a)` | `a` must be the node's in the plan (else stuck). A new open listener bound at `a`, if `a` is unbound or bound by a dead incarnation of this node (taken over); or a failure (`EADDRINUSE`, ...). |
| | `Accept(l)` | the oldest connection of the backlog, now accepted by the caller; `rClosed` once closed; a temporary error (`EMFILE`, ...) at any time. Waits. |
| | `LisClose(l)` | closed, unbound, its backlog broken. |
| | `Dial(a)` | `a` in the plan (else stuck); a new connection appended to the backlog of the open listener bound at `a`, or a failure (refused, unreachable, timed out). |
| | `Write`/`Read`/`Close`/`Addr` (raw) | a reliable byte pipe per direction: `Write` appends all (or fails having appended a prefix); `Read` returns 1..n available bytes, `rEOF` after the writer's close, waits, fails at any time; `Close` closes the end's direction and breaks the connection's exchanges and streams; `Addr` is the plan address on the listening side, any string on the dialing side. Deadline setters are no-ops of the TrustedCode (a deadline is a failure, which is always possible). |
| | `Nonce`, `ClaimD`, `ClaimA` | the prefaces above. |
| kv | `PutKV`, `GetKV` | headers, metadata, trailers one entry at a time: the client's request headers or stream metadata before sending; a server's response headers before the commit, a stream's header and trailer before its end; each side reads the other's (the client the trailer only after the end). |
| HTTP/1.1 | `HOpen`, `HStart(x, hasBody)` | a request on a claimed connection: sent (appended to the connection's exchanges), or **`rNotSent`** (nothing reached the server). |
| | `HBodyPut`, `HBodyEnd(ok)` | the client's body copier: bytes, then complete or aborted. |
| | `HTake(c)` | the server's connection loop: the next request of the connection, **taken once** (`taken`), its line returned; `rEOF` after the client closed; a failure. Waits. |
| | `HBodyRead` | the request body: available bytes (re-chunked), `rEOF` only after a complete body, failure at any time. Waits. |
| | `HCommit(st)`, `HWrite`, `HFinish(ok)` | the response: status and headers committed once; bytes appended (or a failure having appended a prefix); the end (the handler returned: complete, `200` committed if nothing was; or panicked: aborted). |
| | `HHead`, `HRespRead`, `HCancel` | the client: the committed status (headers through `GetKV`), the body (prefixes; `rEOF` only after a complete end), cancellation. Wait. |
| | `HGone` | returns at any time: the server model cancels the request's context then (client gone, timeout). |
| gRPC (HTTP/2 streams) | `GOpen(c, method, timeout)`, `GStart` | a stream on a claimed connection: `pending` (headers sent), or **`rNotSent`** (transport not ready, closing or draining: nothing reached the server). |
| | `GSend`, `GCloseSend`, `GCancel` | the client's next message (intact, in order), its half closed, `RST_STREAM`. `GSend` after the server's end returns `rEOF` (grpc's `io.EOF` from `SendMsg`). |
| | `GRecv` | the server's next message; after all of them its end (code, message; trailer through `GetKV`); **`rNotSent` for a refused stream**; failure. Waits. |
| | `GTake(c)` | the server's connection loop: a pending stream **dispatched (once; never refused afterwards)**, with method and timeout; or a pending stream **refused** (`REFUSED_STREAM`; never dispatched afterwards) and the loop goes on; `rEOF`; failure. Waits. |
| | `GDrain(c)` | `GOAWAY`: nothing dispatched on the connection any more; its pending streams refused. |
| | `GSrvRecv`, `GSrvSend`, `GFinish(code, msg)` | the server's side: the client's messages in order, `rEOF` after `CloseSend`; its messages; its end, the message as it arrives (`msgArrives`: an ASCII message unchanged). |
| | `GGone` | returns at any time: the handler's context may be canceled then. |
| | `GOwnErr` | a status grpc-go makes itself: any code `1..16` with one of grpc-go's own messages (`grpcOwnMsg`, C5). |

The heap and the incarnation never change in a step. Result convention: `(result, code)`, code
`rOk | rFail | rEOF | rNotSent | rClosed | rTemp`. Handles are extension values in the draft; the
Impl may use plain ids instead (C11).

### 4.2 The Go functions over them (TrustedCode, GooseLang)

* **net**: `Listen` → `Listen`, a `*TCPListener` holding the id; `Accept` → `Accept`, a
  `*TCPConn` (the type `keepaliveListener` asserts); `Dialer.Dial(Context)` → `Dial` (a context
  done: an error); `TCPConn.Read/Write/Close/LocalAddr/RemoteAddr` → the raw operations; deadline
  and keepalive setters return `nil`; errors are `*net.OpError`s (`Temporary()` true for `rTemp`).
* **net/http client**: `Transport.RoundTrip(req)`: dial through the transport's `Dial`/`DialContext`
  field (the program's dialer; else `net.Dialer`), write an HTTP/1 preface through the returned
  connection, `ClaimD`, `HOpen`, `PutKV` each header, `HStart`; a goroutine copies the request body
  by calling the body reader's `Read` (program code: `bytes.Buffer`, rafthttp's readers) into
  `HBodyPut`, then `HBodyEnd`; `HHead`; a `*Response` whose `Body` reads with `HRespRead` and
  closes with `HCancel` + `Close`. **Resends** (net/http's `shouldRetryRequest`, `transport.go:844-
  890`, as if the connection were reused): after `rNotSent`, when the body is absent or rewindable
  (`GetBody`); after a failure of a sent request, only when `isReplayable` (`request.go:1561`:
  `GET`/`HEAD`/`OPTIONS`/`TRACE` or an idempotency key, body absent or rewindable). Always a fresh
  connection (C9). Context cancellation (`WithContext`): `HCancel` and an error.
  `CloseIdleConnections`: no-op. `Client.Do/Get`: `RoundTrip` through the client's `Transport`
  (dynamic); a `3xx` with `Location` is stuck (etcd's handlers never redirect; net/http would follow
  it); `Timeout`: an error.
* **net/http server**: `Server.Serve(l)`: loop `l.Accept()` (the program's listener chain), with
  net/http's backoff on temporary errors (`server.go:3529-3600`), `ErrServerClosed` after
  `Shutdown`/`Close`; per connection a goroutine: read the preface through the connection (wrapper
  `Read`s), `ClaimA` (an HTTP/2 preface: close, as net/http without h2c does), then loop `HTake`;
  per request build a `*Request` (fields read-only, `Body` reading with `HBodyRead`, `Context()`
  canceled by a `HGone` watcher), a `ResponseWriter` (`Header()` a map, `WriteHeader` →
  `PutKV`s + `HCommit`, `Write` → `HWrite`, `Flush` commits `200`), call `Handler.ServeHTTP`
  (dynamic) **with no `recover`** (coordinator's decision, 2026-11-10: net/http recovers handler
  panics but `ErrAbortHandler`, `server.go:1956`, yet the model lets a handler panic be the
  program's panic, so the proof must show no handler panics; stronger than Go, and true of the
  program once `issues/etcd-rafthttp-pipeline-process-error-panic.md` is fixed on the fork):
  `HFinish(true)` on return; then call the
  connection's `Close` (the program's wrapper: `LimitListener`'s slot). `Shutdown(ctx)`: close the
  listeners, wait until no handler runs or `ctx` is done. `ServeMux`: plain path patterns, the
  longest wins, a subtree pattern redirects its bare path (`301`), no match `404`; methods,
  wildcards and host patterns stuck (C10).
* **grpc client**: `NewClient(target, opts)`: a `ClientConn` holding the options (interceptors,
  credentials, default call options, the resolver builder for the target's scheme), idle: the
  builder's `Build` (the program's: clientv3 wraps `resolver/manual`) runs at the first RPC and
  again after any idle period (grpc's idleness manager; nondeterministic in the model, which is
  what `issues/etcd-client-resolver-build-race.md` is about); `manual.Resolver.CC()` panics before
  `Build` (`resolver/manual/manual.go:123-127`), as grpc's does. `ParseServiceConfig` of exactly
  `{"loadBalancingPolicy": "round_robin"}` (else stuck). `Invoke` = grpc's `invoke` (`call.go:69-
  94`): the chained unary interceptor (program code) around the attempt: pick an endpoint among the
  addresses the resolver has reported (any of them: round-robin over ready subchannels, removals
  asynchronous), reuse a claimed connection to it or dial one (grpc's own `net.Dialer`) and write
  the gRPC preface, `GOpen` with the deadline, `PutKV` the outgoing metadata and the credentials'
  `GetRequestMetadata` (program code), `GStart`, marshal the request with the codec (program code:
  grpc's default proto codec over `proto.Marshal`), `MaxCallSendMsgSize` check, `GSend`,
  `GCloseSend`, `GRecv` twice (`cardinality violation` if a second message comes), unmarshal into
  the reply (codec), `MaxCallRecvMsgSize` check. Transparent retry and errors: section 6.
  `NewStream` the same with a `clientStream` whose methods map one to one. `Close`: every stream
  `GCancel`, every connection `Close`; later calls `Canceled` "grpc: the client connection is
  closing" (`clientconn.go:70`).
* **grpc server**: `NewServer(opts)`: a `Server` struct (options applied: codec, limits,
  interceptor chains); `RegisterService(sd, ss)`: recorded (the reflection check and the
  duplicate check, `server.go:778-797`, end in `logger.Fatalf`: section 7, G8); `Serve(lis)`: loop
  `lis.Accept()` with backoff on temporary errors (`server.go:906-960`), per connection a goroutine:
  preface through the connection, `ClaimA`, loop `GTake`; per dispatched stream a goroutine **without
  `recover`** (grpc does not recover handler panics, `server.go:1091-1107`: a panic is the program's),
  method lookup (`Unimplemented` "unknown service"/"unknown method", `server.go:1599-1608`, through
  `GFinish`); a unary method: `GSrvRecv` one message (`MaxRecvMsgSize`: `ResourceExhausted`, handler
  not run), the handler with a decoder closure (codec `Unmarshal`) and the chained interceptor, its
  reply marshaled (`MaxSendMsgSize`), `GSrvSend`, `GFinish(OK)`; its error through `status.
  FromError`, else `status.FromContextError` (`server.go:1465`: `Unknown` with `err.Error()`, or the
  context's code); a streaming method: the handler with a `serverStream` over `GSrvRecv`/`GSrvSend`.
  The handler's context: incoming metadata (`GetKV`), the peer, the timeout as a deadline, canceled
  by a `GGone` watcher. `GracefulStop`: close the listeners, `GDrain` every connection, wait for
  the handlers (`server.go:1721-1722`), close the connections. `Stop`: close listeners and
  connections without waiting for handlers. `ServeHTTP` (TLS path): stuck (C8).

Roughly 95 Go functions and methods: net ~16, net/http ~35, grpc (with `resolver/manual`, call and
dial options, server options, status if not translated) ~45.

## 5. Messages as values

**Proposal: the extension moves byte strings; the codecs are program code; protobuf is E2's.**
A gRPC message in the extension is the codec's output bytes (`List w8`); headers, metadata and
trailers are `(key, value)` string pairs; HTTP bodies are bytes. The TrustedCode passes Go strings
in and out (`string(b)`, as OsFs's models do) and calls the codec the library would: the server's
`CustomCodec` (etcd's `v3rpc/codec.go`, which calls `proto.Marshal`/`Unmarshal`) and the client's
default `encoding/proto` codec (modeled as `proto.Marshal`/`Unmarshal` of the message, with its
"not a `proto.Message`" error).

Consequences:

* The grpc model knows nothing of protobuf; the content-level statements of today's boundary
  (`norm c`, `msgAt`, "the server decodes `norm c`") become **lemmas** combining the byte-level
  specs with E2's `Unmarshal ∘ Marshal = norm` law.
* `msgsFit` (`issues/grpc-codec-alloc-before-size-check.md`: the codec allocates `proto.Size` bytes
  before the size check, and `make` panics above `2 ^ 48`) is no longer a grpc premise: the panic is
  in `proto.Marshal`'s model, so the premise moves to E2 (where it belongs: it is about the size of a
  marshaled message), and is discharged where messages are built.
* The alternative, contents in the extension, would make the network depend on the protobuf model
  and would skip the codecs, which are program code: rejected (C4).

## 6. At most once, retries, deadlines, endpoints, errors

**At most once (unary and streams).** The model's invariant: a gRPC stream record is dispatched at
most once and `refused` and `dispatched` are final (`GTake`, `GDrain`); an HTTP exchange is taken at
most once (`HTake`). A client model creates a **new** record to resend, and only when grpc-go or
net/http would:

* gRPC: after `GStart` returns `rNotSent` (no record: grpc's `transportStream == nil &&
  allowTransparentRetry`, `stream.go:807`), or after `GRecv` returns `rNotSent` for a refused stream
  on the first attempt (`cs.firstAttempt && unprocessed`, `stream.go:816`; `unprocessed` set on
  `REFUSED_STREAM` or a `GOAWAY` above the stream, `http2_client.go:821,1301,1447`; the server
  refuses only before dispatch, `http2_server.go:552-557`). Never after a failure of a dispatched
  stream: no service-config retry policy (etcd's config sets only the balancer; `shouldRetry`
  returns the error when there is none, `stream.go:856-858`). So the contract a caller attaches to a
  request is consumed by at most one handler run, which is today's `attemptOk_call` claim, now a
  theorem of the model.
* HTTP: the resend rules of 4.2, a non-replayable request (`onceOnly`) only after `rNotSent`
  (nothing written). So today's `reqTicket` design is a theorem; a replayable request may be
  handled twice, as today's boundary says.

The model allows refusal of **any** pending stream at any time (an over-approximation of
`MaxConcurrentStreams` and `GOAWAY`): more transparent retries than reality, each to a fresh record,
never a second dispatch.

**Deadlines and cancellation.** A client's context deadline travels as the stream's timeout (grpc's
`grpc-timeout`); the server model gives the handler a context with that timeout, also canceled
whenever `GGone` returns (any time: clock skew, the client's `RST_STREAM`, a dead connection). A
client operation fails at any time; when it does with the caller's context done, the model returns
the context's status (`Canceled`/`DeadlineExceeded`, grpc's `toRPCErr(ctx.Err())`), else an own
error. HTTP: `Request.WithContext`'s context done makes `RoundTrip`/body reads fail; the server's
`Request.Context()` is canceled by `HGone`.

**`WaitForReady(true)`** (etcd's default) only changes waiting: the attempt keeps picking and
dialing after `rNotSent` until its context is done, where `false` fails fast with `Unavailable`. Both
are executions of the model (a resend loop, or an own error); nothing about dispatch changes.

**The endpoint** is any address the resolver has reported since the `ClientConn` was built (a spec's
`A ep` holds of all of them), the connection a fresh dial or a claimed one to it.

**What a client sees when a member crashes**: its operations on streams to the dead incarnation
may fail at any time (in grpc-go: `Unavailable` "transport is closing", "error reading from server:
EOF", or its deadline's `DeadlineExceeded`), or wait. The model returns an own error (`GOwnErr`) or
the context's. A response the server finished before crashing may still arrive. A stream sent but
never dispatched is not resent (in reality grpc sees a connection error, not `unprocessed`), unless
`GStart` itself reported `rNotSent`.

**Own errors vs the server's statuses.** clientv3 maps statuses to etcd errors by message
(`rpctypes`), so the model must not produce an own error with an etcd message. `GOwnErr` produces
any code `1..16` with a message satisfying `grpcOwnMsg`: begins with one of grpc-go v1.84's own
message prefixes ("transport is closing", "connection error", "grpc: ", "context deadline exceeded",
"unknown service", ...). This makes today's opaque `grpcMsg` concrete, and `desc_not_grpcMsg`
(`rpctypes/Api.lean:359`) decidable. The list must also **exclude** the two messages clientv3
retries mutations on ("there is no address available", "there is no connection available",
`retry.go:93`), which grpc-go v1.84 never produces (today's boundary records the same: W0's
`CallErr.notSent` is never produced). C5.

## 7. Justification, and the known gaps

| rule | why grpc-go / net/http over TCP do this |
|---|---|
| FIFO, intact, once within a gRPC stream; any order across streams and connections | HTTP/2 over TCP: a stream's DATA frames in order on one connection; grpc-go frames each message with a length prefix and delivers whole messages (`rpc_util.go:1053`, `recv`); streams are independent. |
| HTTP bodies arrive as prefixes; `EOF` only at a complete body | HTTP/1.1 framing (chunked or `Content-Length`): a truncated body is `io.ErrUnexpectedEOF` or another error, never `EOF` (net/http `transfer.go`'s `body.Read`); today's `readerAt_read` law. |
| every operation may fail or wait | TCP resets and timeouts, keepalive (grpc's keepalive and enforcement `GOAWAY`), net/http's `ReadTimeout`/`WriteTimeout`, a peer's crash, flow control (a blocked write that later times out). |
| a dispatched stream is never retried; refused ones once | `stream.go:800-830`, `http2_client.go:821,1301,1447`, `http2_server.go:552-557` (above). |
| a non-replayable request is resent only when nothing was written | `transport.go:844-890` (`shouldRetryRequest`), `request.go:1561-1575` (`isReplayable`). |
| a handler per stream; per request | `server.go:1091-1107` (grpc, no `recover`), net/http's `conn.serve` (per connection, sequential requests, `recover` at `server.go:1956`). |
| status of a handler's error | `server.go:1465` (`FromError`, else `FromContextError`); `grpc-message` percent-encoded, invalid UTF-8 replaced (`internal/transport/http_util.go`): `msgArrives` keeps only "ASCII arrives unchanged". |
| the server's metadata | `http2_server.go` `operateHeaders`: keys lowercased, reserved keys (`:authority`, `content-type`, `user-agent`, `grpc-*`) added or overwritten; the TrustedCode gives any values to reserved keys (today's `mdSeen`). |
| the endpoint: any reported address | round_robin picks among ready subconns of the resolver's latest addresses; removals are asynchronous (`balancer/roundrobin`, `balancer/endpointsharding`). |
| a crash: the incarnation's ends dead; rebind takes over | a dead process's sockets are closed by its kernel (or the machine is gone); a new process binds the port afresh; nothing sent to the old sockets reaches it. |
| Listen/Dial only within the plan | the deployment's addresses (the test's configuration); outside: stuck, not modeled. |

**Known gaps** (what the model rules out or simplifies, and why it does not matter, or what it
needs):

* **G1. TLS** is not modeled: `Creds`, `https`/`unixs` URLs, `ServeHTTP` are stuck. The test is
  insecure (etcd's `sctx.insecure` path).
* **G2. Wrappers beyond the preface.** The model runs a wrapper's `Read`/`Write` on the preface
  only; net/http and grpc call them on every byte. Faithful for wrappers whose `Read`/`Write`
  delegate unchanged after the preface: all of etcd's (`timeoutConn`: a deadline, then the inner
  call; `keepAliveConn`: promoted; `limitListenerConn`: only `Close` differs; cmux's `MuxConn`:
  replays the sniffed bytes, then delegates). Their translated code can be given that property as a
  lemma, a sanity check of the claim; a wrapper that transforms bytes (TLS) is stuck.
* **G3. No flow control, no buffering**: sends never block; a response's bytes are visible on
  `Write`, before net/http would flush them. Extra interleavings only (sound); blocking is liveness.
* **G4. No time**: a timeout is only a failure at some point; the server's deadline is the client's
  timeout, not a skewed clock (and `GGone` covers an early cancellation).
* **G5. HTTP connection reuse** is not modeled (a fresh connection per `RoundTrip`), but its resends
  are (as if reused). Server-side, requests of one connection are served in order, as net/http does.
* **G6. Address aliases and port `0`** are stuck (G6 and the plan replace today's `addrFree`
  premise; the test dials the strings its members listen at).
* **G7. Another node binding a dead node's address** fails in the model where reality may succeed:
  excluded by the plan (each address is one node's).
* **G8. `logger.Fatalf`/`os.Exit`** (grpc's `RegisterService` checks, `server.go:783-797`) are not
  modeled: the model goes on where the process would exit. Sound: an exit is the node never being
  scheduled again (DistLang has no fairness) and a later restart is a crash; the model's extra
  continuation adds behaviors only. etcd registers each service once, before `Serve`, with the
  right types.
* **G9. Resource exhaustion**: `Accept`'s temporary errors are modeled; out-of-memory and the
  runtime's fatal errors are not (as OsFs's `AllocOOMS` note).
* **G10. The own-message list** (`grpcOwnPrefixes`) is a trusted extraction from grpc-go's source:
  every own status message begins with one of its entries. To be produced by a script over the
  pinned grpc-go (every `status.Error(f)`/`New(f)` and `connectionErrorf` call reachable on the
  client), kept beside the extension and rechecked when the pin moves.
* **G11. Header and metadata validation** (illegal characters, header list size): an own error or a
  failure, which the model always allows.
* **G12. `ProxyFromEnvironment`**: the model returns no proxy: the deployment sets no proxy for
  peer URLs (today's premise, kept as the model's).
* **G13. HTTP features not used**: `Expect: 100-continue`, `HEAD` bodies, trailers, `Hijack`,
  HTTP/2 over TLS, h2c: stuck or absent.
* **G14. Thread bound.** The model forks a goroutine per connection and per stream/request, as the
  libraries do; the thread tokens they need are the bounds track's (today's `handlerPool` premise,
  `notes/bounds-plan.md`), unchanged by this design.

## 8. Size, and what it lets us prove

**Size (estimates).**

* `Impl.lean`: ~600 lines (the draft: 575, 39 operations; plus the countable instance and the
  `grpcOwnPrefixes` list in full).
* `Specs.lean`: ghost state (an authoritative map of the records; exclusive fragments per end:
  `connEnd`, `hxClient`/`hxServer`, `gsClient`/`gsServer` with the queue positions they own;
  persistent witnesses: a record `taken`/`dispatched`/`refused`, a preface's connection; per plan
  address `addrFree` start resources) and the WP specs of 39 operations: ~2000 lines (Grove: 538 for
  10 operations; OsFs: 1737 plus its lemma files).
* `Adequacy.lean`: ~150 (initial state: the plan, empty tables; `initP`: epoch `0`; crash interp:
  the next incarnation's ownership).
* TrustedCode: ~95 Go functions, ~1500-2000 lines of GooseLang, with this repository translating
  `net` and `net/http` itself, as it does `os` (C7).
* Proofs: the TrustedCode functions' specs from the extension's (~95, ~6000 lines), a protocol
  prelude (~1500: today's `Proto`, `AddrContract`, contracts, tickets as definitions over the
  extension's ghost state), the existing statements discharged. Of the order of 10k lines, the
  scale of the OsFs work.

**What becomes theorems.** Every assumed statement of `Spec/google_golang_org/grpc/**` (62 files:
36 function specs, 58 laws in `Api.lean`, 6 in `peer/Api.lean`) and `Spec/net/http/**` (14 function
specs, 31 laws), and the names-only specs that sit on them in etcd's code once translated
(`client/pkg/transport`'s listeners and transports, rafthttp's `NewRoundTripper`, cmux's
functions). Their opaque predicates get definitions: `connAt`, `serves`, `addrAt`, `protoAt`,
`listenerAt`, `respW`, `readerAt`, `streamKey`, the stream halves, ... over the extension's ghost
state; `grpcMsg` is `grpcOwnMsg`; `fixUtf8` becomes the relation `msgArrives`; `grpcOver` a pair.

**Premises that go**: `addrFree` from the environment (now the plan's start resources), "one
reserved string per socket" (the plan; G6), `msgsFit` as a grpc premise (moves to E2), the
whole-program generation laws (`protoFam_gen`, `addrFree_gen`; already replaced by the per-node
crash design, `open-questions.md`). **Premises that stay**: the handler pool / thread bound (G14),
no proxy (G12), and the deployment's own facts (the plan).

**What stays library-level** (verified, not trusted): the protocol layer above the extension (the
contracts that travel with requests, the per-address protocols, the tickets), and the
content-level grpc statements composed with E2.

**A change it forces on the spec side**: a server's per-address contract may depend on its
incarnation (today's per-generation families), but a client cannot know which incarnation will
serve its request. Either contracts are incarnation-independent, or the client provides its
resource for every incarnation (`∀ L`) and the dispatching incarnation takes its instance. To
decide when the protocol prelude is designed; the model allows both (each record is served by the
incarnation that accepted its connection).

## 9. Open choices

* **C1. Finding the connection behind etcd's wrappers.** (a) **Prefaces through the wrappers**
  (section 3): byte pipes used only for prefaces, the program's wrappers run, a mismatch is stuck;
  gap G2. (b) A trusted unwrap list: the model takes the base connection out of known wrapper types
  (`timeoutConn`, `keepAliveConn`, `limitListenerConn`, `cmux.MuxConn`) by their embedded fields,
  their `Read`/`Write` never run: closer to "no bytes at all", but a trusted claim about etcd's and
  cmux's code, and stuck for a new wrapper. (c) All traffic as record references written through
  the wrappers: faithful for any byte-transparent wrapper, but an HTTP/1 and HTTP/2 framing model in
  disguise, with conn-level invariants in every proof. **Recommendation: (a).** It is the only one
  that adds no trusted claim about etcd's code and keeps the libraries' semantics at the API. It
  does put a byte pipe under the models, used only to identify connections, which reads the
  decision "no TCP model beneath" as "no HTTP or HTTP/2 over TCP". Your call whether that reading
  stands.
* **C2. One extension or three.** **Recommendation: one** (`"net"`), with operations for net,
  net/http and grpc: they share listeners (cmux splits one socket between net/http and grpc), the
  plan and the connections; separate extensions cannot see each other's state.
* **C3. The address plan.** **Recommendation: fixed in the initial global state, Listen/Dial outside
  it stuck** (as OsFs's fixed file domain), replacing the `addrFree` premise. Alternative:
  arbitrary strings, with today's premise kept.
* **C4. Payloads.** **Recommendation: byte strings, codecs run as program code, protobuf E2's**
  (section 5). Alternative: contents in the extension (couples the network to protobuf, skips the
  codecs).
* **C5. grpc's own messages.** **Recommendation: a concrete prefix list extracted by a script
  from grpc-go** (G10), excluding the two messages clientv3 retries mutations on. Alternatives: an
  opaque set with an adequacy hypothesis "no etcd error description is a grpc-go message" (a
  hypothesis about grpc's code, not the environment); arbitrary messages (sound but useless:
  clientv3 could then see an etcd error grpc never sent).
* **C6. The client port.** **Recommendation: split it in the test** (`ListenClientHttpUrls`, so
  `serve.go`'s `onlyGRPC` path serves grpc on its own listener, no cmux there), keeping the
  prefaces cmux-compatible (the HTTP/2 preface, a request line) as a cheap hedge for the unsplit
  path. The peer port's cmux (`Any()`, reads nothing) is unaffected either way.
* **C7. Where it lives.** **Recommendation: this repository** (`GooseLang/Ext/GoNet/`, with this
  repository translating `net` and `net/http` and holding their TrustedCode, as for `os`), since its
  shape (the plan, incarnations, prefaces) is driven by this proof; propose a general version to
  Perennial once it has carried a proof (CLAUDE.md, "Changes to Perennial").
* **C8. TLS.** **Recommendation: out of scope** (stuck), the test insecure.
* **C9. HTTP connection reuse.** **Recommendation: a fresh connection per `RoundTrip`, with
  net/http's resends as if reused** (G5). Alternative: model the idle pool (more state, no more
  behaviors that matter).
* **C10. `ServeMux`.** **Recommendation: a TrustedCode model of plain path patterns** (longest
  prefix, subtree redirect, `404`), other patterns stuck. Alternative: translate net/http's routing
  code (`routing_tree.go`, `pattern.go`; heavier, but no trust).
* **C11. Handles.** The draft's handles are extension values. Since the translated `net.TCPConn`
  is a struct of `net`'s own (an `fd` with an integer `Sysfd`), **recommendation: plain ids (w64)**,
  stored in the translated structs' integer fields, the ownership checks protecting them, as the
  draft already checks.
* **C12. grpc's `status`.** Translate it (over E2's `spb.Status`) if E2 lands first, else a small
  TrustedCode model (`New`, `Error(f)`, `FromError`, `Convert`, `Code`, `Status.{Code,Message,Err}`).
  Minor.

A consequence for the test, not a choice of the model: with random reconfigurations, a joining
member's node exists from the start (DistLang's nodes are fixed) and must learn its initial cluster
from the client node at run time; a small control server in each member's boot program, over the
same extension, does it.
