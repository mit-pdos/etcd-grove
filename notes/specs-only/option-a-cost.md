# What option A would cost: verifying the real grpc-go, x/net/http2 and net/http

Measured 2026-11-12 on specs-only (`ffb55d5620`). It answers one question: what it would cost to
verify the real libraries over the TCP extension (**option A**) instead of trusting Go models of them
(**option B**, `tcp-extension-design.md` §2 and §4). Both options share the TCP extension
(§1 and §2 there: 7 operations, `TrustedCode/net.lean`) and the wrappers above it (layer W). The
program measured is `examples/etcd/crashreconf` at the pins of `examples/go.mod` (grpc-go v1.84.0,
x/net v0.59.0, protobuf-go v1.36.12, go1.27.3). Nothing here is built into the repository: the
tools and data are in scratch (§8).

## 0. Summary

| library (reached from `MemberNode`, `ClientNode`, package inits) | static: funcs / Go lines | static, configuration cut | **executed** in a soak: funcs / lines | package-var initializers |
|---|---|---|---|---|
| grpc-go (`google.golang.org/grpc/...`) | 1216 / 14,951 | 1029 / 12,931 | **664 / 10,040** | 572 |
| x/net `http2` + `http2/hpack` (grpc's framer, HPACK) | 137 / 1,499 | 137 / 1,499 | **95 / 1,153** | 600 (HPACK/Huffman tables) |
| x/net, the rest (`trace`, `idna`, `timeseries`, `httpguts`) | 120 / 1,369 | 19 / 282 | 4 / 26 | 4,833 (idna tables) |
| net/http, std (`net/http`, `internal/...`, vendored `x/net/http/...`, `http2/hpack`) | 1119 / 16,539 | 626 / 8,945 | **335 / 5,861** | 1,091 |
| of which `net/http/internal/http2` + vendored hpack (net/http's own HTTP/2) | 517 / 7,420 | 102 / 1,080 | 2 / 32 (`Server.Configure`, `init`) | 652 |
| protobuf-go (E2's question, not the network's) | 1816 / 22,831 | 1814 / 22,822 | **486 / 7,635** | 1,597 |
| std support reached *only* through the three libraries, and executed | | | 48 / 561 (`net/textproto` 293, `bufio` 79, `net/url` 37, ...) | |

Lines are non-blank, non-comment lines of the function declarations (closures counted in their
function). "Static" is whole-program reachability (RTA refined by VTA). "Configuration cut" drops what
the program's configuration provably never runs (TLS, HTTP/2 in net/http, tracing, binary logging,
the DNS, unix and passthrough resolvers, proxies, ServeHTTP, reflection, compression, cookies). "Executed"
is the functions with any statement executed in two coverage soaks of crashreconf's real run (§1.2).
The code a proof of A must cover lies between the executed and the cut columns: **about 10-13k lines
of grpc, 1.2-1.5k of x/net, 6-9k of net/http, plus about 0.5-1k of std support**, so 18-25k Go
lines in all. Protobuf is the same under A and B: only 4 of its reached functions (12 lines) are
reached only through the network libraries.

**The server paths.** A member serves gRPC with `grpc.Server.Serve(cl)` on a raw `net.Listen`
listener: no cmux, no `ServeHTTP`. `handler_server.go` is statically reachable through interface
dispatch, and none of it runs. The peer handler is `http.Serve` over plain TCP, so it speaks HTTP/1.1. net/http's
HTTP/2 is no longer the bundled `h2_bundle.go` in Go 1.27 but the package `net/http/internal/http2`.
It is statically reachable, and only `Server.Configure` runs (`Serve` with a nil `TLSConfig` configures
h2 in case the listener yields TLS connections); `serveHTTP2Conn` needs TLS ALPN `h2` or
`Protocols.UnencryptedHTTP2`, neither of which is set. rafthttp's and cluster_util's transports set
`Dial`, so `Transport.protocols()` is HTTP/1 only. gRPC's HTTP/2 is its own transport
(`internal/transport`) over x/net's `Framer` and `hpack`; it uses 888 of x/net/http2's 2,874 lines.

**Goose is not the obstacle.** Running the pinned translator on every reached package (§2.1)
rejects only a handful of declarations: 5 in grpc, 1 in each of x/net/http2 and idna, 5 in
net/http, 3 in its HTTP/2 package, and 1 in each of net/url and mime/multipart. Three of them are on
the executed path:

* the labeled loop of `loopyWriter.run` (controlbuf.go:617), the transport's writer;
* a struct copy refused by modelcheck R4 in `addrConn.tryAllAddrs` (clientconn.go:1461);
* a non-unique local type name in net/http's `Transport.dialConn` (transport.go:1892).

The other causes are labeled statements, `//go:linkname` declarations, more R4 copies, a `float64`
decrement, a nested `recover()`, and `rune` in idna. Each is a small upstream rewrite or a general
goose change. A successful translation does not mean the code
can be proved, though. Every standard-library callee needs a model and a spec (`reflect` is names-only
in Perennial), and the semantic gaps in KNOWN_LIMITATIONS then cover 20k more lines.

**The obstacle is the proof.** Per connection, grpc runs a reader, a loopy writer, keepalive and
handshake/GOAWAY goroutines, and per stream a context watcher, a server handler and callback
serializers. It multiplexes streams under flow control and keeps HPACK dynamic tables that must agree
across the two nodes. Messages travel in pooled, reference-counted buffers. At-most-once and
transparent retry depend on GOAWAY's last stream id and on `REFUSED_STREAM`, which tie the two
endpoints' stream state machines together through the byte stream.

**Estimate** (§4), calibrated on this repository's proof-to-Go ratios (10x for rafthttp up to 48x
for bbolt):

| | Go to verify | trusted Go | proof (Lean lines) | relative to existing efforts |
|---|---|---|---|---|
| **A** | 18-25k (real code) | none (beyond goose and Perennial's std models) | **~0.55-0.75M** | 2.5-4x bbolt (199k), 1.5-2x the whole etcd server proof (374k) |
| **B** | ~3.1k models + ~3k real (layer R) | ~3.1k (the models' diffs) | 17k (the design's figure); **60-110k** at this repository's ratios | 0.1-0.5x bbolt |

So A costs roughly 5-12x B at the same ratios, or 30-45x the design's own figure for B. It removes
about 3.1k lines of trusted Go models, and it does not change what the end theorem says.

**Recommendation: B.** Write B's model specs so that they can later become the specs the real
libraries are proved against (the model as the spec of A). Then, if trust is to shrink later, move
toward A one piece at a time in this order:

1. the pure, sequential libraries (`hpack`, the `Framer`);
2. net/http's HTTP/1.1 client and server: one request per connection at a time, three goroutines;
3. grpc's transport last, or never.

## 1. Reachability

### 1.1 Static

A call graph of the whole program: `golang.org/x/tools` v0.52.0 `ssa`, built with generics
instantiated, over `examples/go.mod`'s module graph (`go/packages`, `LoadAllSyntax`). The roots are
`crashreconf.MemberNode`, `ClientNode` and `crashreconf.init`, which runs every package initializer.
RTA comes first: 25,691 functions reached along call edges, 33,121 when the exported methods of runtime
types are added for reflection. VTA then refines it over RTA's functions. VTA alone (18,272 functions)
is unsound here: it loses the calls of closures taken out of generic containers, for example every
callback of `grpcsync.CallbackSerializer` (an `Unbounded[func(context.Context)]`), which drives the
whole balancer and resolver machinery. So the graph used is a hybrid: VTA's callees at each call site,
RTA's where VTA found none. It reaches 23,245 functions. The coverage run confirms it: **no executed
function is missing from it**.

Interface dispatch inflates static reach. Any `io.Reader.Read` site reaches every `Read` of every
instantiated type, h2's included. That is why net/http's static count is twice the cut one, and why
the standard library reached from the network libraries totals 157k lines (8,159 functions),
mostly shared with the rest of the program or dead (x/net/trace's HTML templates, idna's and
`unicode/norm`'s tables).

The configuration cuts (`py/pruned.py`) remove these functions from the graph, each for a stated reason:
`crypto/tls` (no `Creds`, http URLs); net/http's `serveHTTP2Conn`, `maybeServeUnencryptedHTTP2`, the
h2 client hooks (`configureHTTP2`, `http2NewClientConn`, `http2RoundTrip`, `pconn.alt`) and h2's
connection objects; socks and TLS dialing (`ProxyFromEnvironment` never proxies loopback); `x/net/trace`
and grpc's `traceInfo` (`EnableTracing` false); binary logging (`GRPC_BINARY_LOG_FILTER` unset); the dns,
unix and passthrough resolvers' `Build` (clientv3 uses its manual resolver); `delegatingresolver` and
`proxyDial` (no proxy); `ServeHTTP` and `serverHandlerTransport`; otelgrpc (`EnableDistributedTracing`
false); client health checking (no `healthCheckConfig`); reflection; `tlsCreds`; compression; cookies.

### 1.2 Dynamic

`crashreconf_test.go`'s real run (members as processes, random kills, random reconfiguration), built
with `-cover -covermode=atomic -coverpkg=` the four libraries. It ran under an overlay of the test file,
so the file in the repository is unchanged. The overlay runs each member under the test framework
(`TestOptaMember`), so that coverage is set up, and the crasher sends SIGTERM, on which the member
returns and the framework writes its counters, waiting at most 3s before SIGKILL. In effect that is a
kill a few milliseconds later. It ran twice:

1. 4 minutes, 8 rounds, 30 kills, 23 adds, 18 removals;
2. 4 minutes, 7 rounds, 26 kills, 24 adds, 20 removals, on private ports (overlay of `crashreconf.go`)
   and with the standard-library packages instrumented as well.

The executed sets agree to within a few functions: 666 and 664 grpc functions. The numbers above are
the second run's.

Per grpc subset (functions / lines; `py/subsets.py`):

| subset | static | cut | executed |
|---|---|---|---|
| balancer, resolver, picker (wrappers, pickfirst, endpointsharding, gracefulswitch, idle, attributes, serviceconfig) | 225 / 2,714 | 193 / 2,196 | 139 / 1,764 |
| streams and calls (`stream.go`, `call.go`, `rpc_util.go`: retry, replay buffer) | 83 / 1,596 | 83 / 1,596 | 52 / 1,177 |
| transport: `http2_client.go` | 35 / 1,381 | 35 / 1,381 | 27 / 1,241 |
| transport: `http2_server.go` | 34 / 1,108 | 34 / 1,108 | 27 / 972 |
| ClientConn and addrConn (`clientconn*.go`, `dialoptions.go`) | 76 / 1,060 | 76 / 1,060 | 54 / 930 |
| status, codes, metadata, peer, grpclog, envconfig, grpcsync, buffer, ... | 119 / 1,016 | 115 / 995 | 88 / 734 |
| server (`server.go`) | 57 / 913 | 57 / 913 | 40 / 790 |
| transport: controlbuf, loopy writer | 42 / 598 | 42 / 598 | 37 / 566 |
| transport: the rest (`transport.go`, readers, `readyreader`) | 77 / 569 | 76 / 565 | 60 / 484 |
| encoding/proto codec and `mem` buffers | 77 / 570 | 76 / 558 | 39 / 310 |
| transport: `http_util.go` (framer wrapper, header and grpc-message coding) | 30 / 403 | 30 / 403 | 24 / 350 |
| transport: flow control and BDP estimator | 15 / 164 | 15 / 164 | 12 / 150 |
| channelz (registration cannot be turned off in v1.84) | 77 / 538 | 76 / 532 | 20 / 160 |
| stats hooks (no handler configured: the guards run) | 23 / 157 | 23 / 157 | 14 / 83 |
| binary logging | 78 / 746 | 40 / 266 | 9 / 157 (`GetMethodLogger` returns nil) |
| health (server registered by `v3rpc.Server`) | 39 / 359 | 38 / 314 | 10 / 68 |
| credentials (insecure only) | 25 / 258 | 15 / 91 | 8 / 32 |
| reflection (generated descriptor inits only) | 72 / 458 | 0 | 4 / 72 |
| ServeHTTP handler transport | 17 / 230 | 1 / 1 | 0 |
| tracing (`trace.go`), proxy `CONNECT` | 15 / 113 | 4 / 33 | 0 |

The rows sum to the grpc totals. Keepalive has no package of its own: it is
`http2Client.keepalive` (58 lines), `http2Server.keepalive` (70) and ping enforcement, all executed,
since clientv3 sets `DialKeepAliveTime` and `v3rpc` sets an enforcement policy.

net/http by file, executed lines: `transport.go` 1,678 (75 functions), `server.go` 1,351 (86),
`transfer.go` 633, `request.go` 416, `client.go` 405, `pattern.go` and `routing_tree.go` 353 (Go
1.22 mux patterns), `internal/chunked.go` 172, `status.go` 130, `header.go` 116, `httpproxy` 109,
`sniff.go` 97.

Protobuf: `internal/impl` executes 210 functions (4,040 lines), `internal/filedesc` 128 (1,607,
descriptor building at init), and the rest is small. In the executed code: 796 `reflect` uses in
72 functions, 40 `unsafe` uses, 2 method expressions (which goose rejects). That is E2's decision
under A and B alike.

## 2. Goose translatability

### 2.1 What the pinned translator does

The pinned Perennial's `goose` was built into scratch and run, with no configuration (translate
everything) and output to scratch, on every reached grpc package (46 of them), x/net's `http2`, `hpack`,
`trace`, `timeseries`, `httpguts` and `idna`, and std's `net/http`, its `internal/http2`, `internal`,
`httpcommon`, `httpsfv` and `ascii`, the vendored `hpack`, `httpguts` and `httpproxy`, plus
`net/textproto`, `bufio`, `net/url`, `mime`, `mime/multipart`, `compress/gzip` and `crypto/tls`.
goose reports the first error of each declaration and continues:

| package | rejected declarations | where, why | reached? |
|---|---|---|---|
| grpc | `loopyWriter.run` | controlbuf.go:617, labeled `for` (`hasdata:`, `continue hasdata`) | **executed: the transport's writer goroutine** |
| grpc | `addrConn.tryAllAddrs` | clientconn.go:1461, modelcheck R4: `ac.dopts.copts.KeepaliveParams = ac.cc.keepaliveParams` (struct copy between memory places) | **executed: every connection attempt** |
| grpc | `retryThrottler.throttle` | clientconn.go:1752, `rt.tokens--` on `float64` | dead (no retry policy) |
| grpc/mem | `ReadAll` | buffer_slice.go:260, labeled loop | reached, not executed |
| grpc/health | `clientHealthCheck` | client.go:62, labeled loop | dead |
| x/net/http2 | `parseUintBytes` (goroutine tracking) | gotrack.go:171, labeled loop / `goto` | debug only |
| x/net/idna | the type `runeError` | idna.go:337, "Unknown basic type rune" in a struct field | dead |
| net/http | 3 `//go:linkname` externals (request.go:1081, roundtrip.go:20, server.go:3439); `Transport.Clone` (R4 struct copy, transport.go:378); `Transport.dialConn` (transport.go:1892, a local type `connectionStater` whose name is not unique in the package) | | the linknames are exported for x/net; `Clone` not executed; **`dialConn` executed: every client connection** |
| net/http/internal/http2 | `parseUintBytes` (labels), `serverConn.notePanic` (`recover()` not directly in a deferred literal, server.go:749), an R4 copy (writesched_priority_rfc9218.go:64) | | not executed |
| net/url, mime/multipart | one `//go:linkname` each | url.go:676, readmimeheader.go:15 | |

Everything else translates: generics, `select`, goroutines, `defer`/`recover` in deferred literals,
range-over-func, `sync/atomic`, `unsafe`, method values and type switches. Even `crypto/tls`
translates, into 47k lines of Lean. The labeled statements are the only systematic gap: a general
goose change (`LabeledStmt`, labeled `break`/`continue`) would remove most of the list.

What a successful translation does not give:

* **Elaboration.** No translation was elaborated in Lean, since that needs every dependency
  translated.
* **Callee models.** Every standard-library callee needs a model and a spec. Perennial translates only
  selected std functions: `strings`, `strconv` and `bytes` are partial, `fmt` is trusted
  (`Sprintf`/`Errorf`), `reflect` is names-only. grpc's `RegisterService` and net/http's
  `onceSetNextProtoDefaults` call `reflect`. `sync.Pool`, `sync.Cond`, `time.AfterFunc`, `NewTimer` and
  `context.AfterFunc` are modelled.
* **Semantic gaps over more code.** KNOWN_LIMITATIONS applies to 20k more lines: no panic on a nil
  function call, the deferred-panic chain, the fixed evaluation order, map key checks.

### 2.2 Features in the reached code

Counted on the syntax (`py/feat.py`), for the statically reached functions and for the executed
ones. A cell is uses / functions, except in rows that name two features, where it is the uses of
each (send / receive, Pool / Cond, values / expressions, labels / `goto`, assertions / switches).

| feature | grpc static | grpc exec | x/net static | net/http static | net/http exec | protobuf static |
|---|---|---|---|---|---|---|
| `go` statements | 31 / 25 | 17 / 13 | 4 / 3 | 34 / 30 | 10 / 7 | 0 |
| `select` (cases; with `default`) | 44 / 41 (98; 13) | 28 / 26 (62; 10) | 4 / 4 | 56 / 41 (143; 19) | 17 / 10 (40; 6) | 0 |
| channel send / receive | 22 / 100 | 15 / 63 | 2 / 2 | 38 / 130 | 16 / 36 | 0 |
| `sync/atomic` | 143 / 87 | 81 / 58 | 4 / 4 | 39 / 26 | 26 / 17 | 36 / 28 |
| `defer` | 144 / 115 | 94 / 75 | 16 / 14 | 143 / 114 | 56 / 47 | 36 / 35 |
| closures | 213 / 140 | 151 / 87 | 14 / 10 | 93 / 68 | 44 / 30 | 229 / 87 |
| timers (`AfterFunc`, `NewTimer`, `After`, ...) | 13 / 11 | 10 / 8 | 0 | 26 / 23 | 5 / 5 | 0 |
| `sync.Pool` / `sync.Cond` | 12 / 5 | 5 / 5 | 2 / 0 | 44 / 18 | 11 / 3 | 6 / 0 |
| generic functions (declared) | 21 | 16 | 0 | 4 | 3 | 0 |
| range over func | 14 / 13 | 11 / 10 | 0 | 2 / 2 | 0 | 0 |
| method values / method expressions | 17 / 0 | 15 / 0 | 0 | 38 / 0 | 12 / 0 | 10 / **67** |
| labels / `goto` | 3 + 8 labeled branches / 0 | 1 / 0 | 0 | 1 / 7 (h2, dead) | 0 | 11 / **30** |
| `reflect` | 13 / 6 | 12 / 5 | 0 | 37 / 5 | 16 / 3 | **1,410 / 180** |
| `unsafe` | 16 / 8 (generated pb inits) | 8 / 4 | 0 | 0 | 0 | 68 / 38 |
| `recover` | 0 | 0 | 0 | 3 | 1 (`conn.serve`) | 2 |
| type assertions / switches | 126 / 15 | 72 / 8 | 9 / 1 | 143 / 20 | 72 / 9 | 147 / 25 |

The atomics are `Load`, `Store`, `Add`, `Swap` and `CompareAndSwap` on typed atomics (`atomic.Int64`,
`atomic.Bool`, `atomic.Pointer[T]`) and the `AddInt32`/`LoadInt32`/`StoreInt64`/`CompareAndSwapUint32`
functions. `runtime` is `Gosched` (loopy) and `Caller` (grpclog depth). Maps of funcs: 0 in grpc,
3 in net/http (`TLSNextProto`). Closures capturing a loop variable: 1 in grpc,
`endpointSharding.updateState`, which goose handles with per-iteration variables.

### 2.3 The hardest functions

Ranked by size plus weighted concurrency features (`py/hard.py`), then sorted by hand. All of these
are executed unless marked.

1. `transport.NewHTTP2Client`, http2_client.go:210 (234 lines). Spawns 4 goroutines (a handshake
   context closer, keepalive, reader, loopy). Writes the preface and SETTINGS, sets up flow control,
   BDP and channelz, and cleans up through closures on every error path.
2. `transport.NewServerTransport`, http2_server.go:151 (191). Reads the preface and SETTINGS, spawns
   loopy and keepalive, and waits in a `select` with a timer.
3. `(*http2Client).NewStream`, http2_client.go:778 (158). Waits for stream quota
   (`MaxConcurrentStreams`) on a channel. Queues the header frame through `controlBuf.executeAndPut`
   closures, marks streams unprocessed (needed for transparent retry), and has `select`s of up to 4 cases.
4. `(*http2Server).operateHeaders`, http2_server.go:377 (224). Validates HPACK-decoded headers,
   creates the stream, refuses past `MaxConcurrentStreams` (`REFUSED_STREAM`: the at-most-once
   condition), parses the deadline and builds the metadata.
5. `(*http2Client).operateHeaders`, http2_client.go:1494 (156). Turns headers and trailers into a
   status (`grpc-status`, decoded `grpc-message`) and orders the stream's close.
6. `loopyWriter.run` and `processData`, controlbuf.go:595 and :950. The labeled loop goose rejects.
   Batches frames, sends data only within flow-control and per-stream quotas, keeps a round-robin
   active-stream list, and calls `runtime.Gosched`.
7. `controlBuffer` (`executeAndPut`, `get`, `throttle`; controlbuf.go). An unbounded queue with a
   transport-response throttle (an atomic plus a channel).
8. `(*http2Client).reader`, http2_client.go:1711. The frame-dispatch loop: a type switch over frames,
   the connection closed on any error.
9. `http2Client.keepalive` (:1787) and `http2Server.keepalive` (:1197). Timers, a `lastRead` atomic,
   `kpDormancyCond`, `select`s of up to 4 cases.
10. `(*http2Server).outgoingGoAwayHandler`, :1396 (not executed: no graceful stop under load). The
    two-phase GOAWAY with a ping, in a timer goroutine. The drain semantics behind at-most-once
    live here.
11. `(*http2Client).handleGoAway`, :1384. Marks streams above `lastStreamID` unprocessed, which is the
    other half of transparent retry.
12. `(*http2Client).closeStream` (:966) and `Close` (:1027). Close races with the reader and the
    writer: `sync.Cond`, channel closes, a `select` with `default`.
13. Flow control: `inFlow`, `trInFlow`, `writeQuota` (flowcontrol.go) and `bdpEstimator.calculate`
    (`float64` RTT arithmetic), with windows shared between goroutines.
14. `newClientStreamWithParams` (stream.go:398) with `withRetry`, `retryLocked`, `replayBufferLocked`
    and `csAttempt.shouldRetry` (stream.go:800), and the per-stream context-watcher goroutine
    (stream.go:537). The transparent-retry and replay logic: the client side of at-most-once.
15. `Server.Serve`, `handleRawConn`, `serveStreams` (server.go:906, :1071). Per-connection goroutines,
    a temporary-error backoff timer, and connection tracking for `Stop`/`GracefulStop` (`stop`
    :1687 and `removeConn` :1176 use `sync.Cond`).
16. `Server.processRPC`/`processUnaryRPC`, server.go:1292 (193). Size-limited decoding, the
    compression branches, the interceptor chain, the status mapping and the trailers.
17. `addrConn.resetTransportAndUnlock`, `tryAllAddrs` and `createTransport` (clientconn.go:1325),
    with the `ClientConn` idleness manager (`internal/idle`). The connectivity state machine, with
    backoff and timer `select`s.
18. pickfirst's leaf balancer (`updateSubConnState` pickfirst.go:591, `UpdateClientConnState` :210),
    `endpointSharding.updateState` (:248, which spawns a goroutine), gracefulswitch, and
    `grpcsync.CallbackSerializer`. Three nested balancers whose state changes arrive as serialized callbacks.
19. `pickerWrapper.pick`, picker_wrapper.go:105. A blocking pick over an atomic picker generation
    and its channel; `WaitForReady`.
20. HTTP/2 framing and HPACK: x/net's `Framer.readMetaFrame` (frame.go:1707, HEADERS and
    CONTINUATION reassembly with decoder callbacks) and the `hpack.Decoder`/`Encoder` (hpack.go:352,
    huffman.go:49, the dynamic table's evictions and size updates). Plus grpc's `mem` buffers
    (buffers.go: an atomic reference count, `Free` back to a `sync.Pool`), the ownership discipline
    of every message.

On the HTTP/1.1 side, if net/http is verified too:

* `Transport.dialConn` (transport.go:1836, 255 lines, its proxy and TLS branches dead), with
  `persistConn.readLoop` (:2454), `writeLoop` and `roundTrip` (:2994): 3 goroutines per
  connection, `select`s of up to 9 cases, the idle pool (`tryPutIdleConn`, `getConn`'s `wantConn`
  queues) and `shouldRetryRequest`.
* `conn.serve` (server.go:1949): `recover`, the keep-alive loop, `connReader.backgroundRead` with
  `sync.Cond`, and `chunkWriter.writeHeader` (:1313, 168 lines of automatic headers).
* `setRequestCancel` (client.go:358): a timer goroutine and atomics.

## 3. Concurrency, and what a proof would need

**grpc's goroutines.** Per client connection (`http2Client`): reader, loopy writer, keepalive, and a
handshake-context closer. Per server connection (`http2Server`): `serveStreams` (the reader, i.e.
`HandleStreams`), loopy, keepalive, and the GOAWAY ping timer. Per stream: a client context watcher
(stream.go:537) and the server handler (`go f()`, server.go:1107). Per ClientConn: the resolver's and
balancer's callback serializers, `addrConn.connect`/`resetTransport`, endpointsharding's `exitIdle`,
and the idle timer. With clientv3's keepalive on, that is 4 goroutines per connection on each side,
plus 2 per RPC, plus about 3 per ClientConn. Shared state: `http2Client.mu`, `controlBuffer.mu` with
its consumer-waiting channel, `writeQuota` (an atomic plus a channel), `recvBuffer` (a mutex-guarded
backlog plus a 1-element channel), per-stream state words updated by CAS, the picker's atomic pointer,
and `Server.mu` with a `sync.Cond`.

**Invariants a proof of A needs**, on top of B's TCP protocol (byte pipes with protocols per address):

* **The HTTP/2 frame grammar on each direction**: the preface, then frames whose 9-byte headers
  delimit them, HEADERS/CONTINUATION atomicity, and gRPC's 5-byte message prefix inside DATA. The
  resources riding on frames work as in B's frame protocol, but a message spans several DATA frames
  and frames of different streams interleave.
* **HPACK**: the encoder's dynamic table (written by the sender's loopy) and the decoder's (read by the
  peer's reader) are equal at each header block, a two-node ghost "table history" per direction. The
  Huffman and integer codecs round-trip. Size updates and evictions happen in order.
* **Stream state machines on both ends**, linked through the pipe: id allocation (odd, increasing),
  idle to open to half-closed to closed, RST_STREAM, the trailer last.
* **At-most-once and transparent retry**: the server dispatches a stream only if its id is at most the
  GOAWAY last-stream-id it will send, and sends `REFUSED_STREAM` only for undispatched streams. The client
  retries only streams marked unprocessed (headers not sent, GOAWAY above them, REFUSED_STREAM), and
  replays from a buffer. B's protocol carries the same argument with one stream per connection and a
  `GRefused` frame. Here it runs over multiplexed streams and the two-phase GOAWAY.
* **Ownership of pooled buffers**: `mem.Buffer` reference counts. A freed buffer is reused through
  `sync.Pool`, so every `Ref`/`Free` needs a fractional, counted ownership protocol to rule out
  aliasing.
* **Locks and serializers**: the invariants of `controlBuffer`, `writeQuota`, the stream-quota channel,
  the `recvBuffer` and the callback serializers' FIFO queues, and their `ClientConn` and balancer state
  machines (idle, connecting, ready, transient failure, shutdown).
* **What safety lets a proof over-approximate**: flow-control windows, BDP, keepalive, ping
  enforcement, backoff and MaxConcurrentStreams quotas only cause failures or waits. A safety proof
  needs only that they neither panic nor break ownership, not that they compute correct windows. This
  is B's T3/U6 stance applied to real code: perhaps a quarter of the transport proof saved, but none
  of the four items above.

**Comparable verified systems** (from memory, approximate). None verifies an HTTP/2 or gRPC
implementation. The closest:

* Project Everest's F* work: the miTLS record layer, a verified QUIC record layer, and EverParse's
  verified parsers. A multi-year effort by a large team.
* Small verified HTTP/1.1-subset servers in C: the interaction-trees and VST key-value server.
  Hundreds of lines of C, tens of thousands of lines of proof.
* Grove and gokv (Perennial): exactly-once RPC over a message network, with an RPC library a few
  hundred lines long.
* Verdi and IronFleet: Raft and Paxos with their own simple RPC.
* NetSem (HOL4): a post-hoc specification of TCP and sockets, which is the T layer's kind of artifact,
  not an implementation proof.

Known scales: seL4's ~8.7k lines of C took ~200k lines of Isabelle and about 20 person-years. Human
verification projects produce roughly 10-25k proof lines per person-year.

## 4. Estimate

**This repository's own ratios** (Lean proof lines in `Proof/` of the main checkout,
`/home/ubuntu/etcd-grove`, 2026-11-12; Go lines counted by the same tool, function bodies plus
package-var initializers):

| component | Go lines | Lean lines | ratio |
|---|---|---|---|
| rafthttp (network code over assumed net/http specs) | 2,223 | 21,647 | 10x |
| etcdserver and its subpackages | 14,614 | 216,016 | 15x |
| v3rpc | 1,869 | 29,328 | 16x |
| clientv3 | 3,343 | 105,934 | 32x |
| raft (without raftpb) | 3,607 | 138,674 | 38x |
| mvcc | 2,310 | 95,922 | 42x |
| bbolt (`Proof/go_etcd_io/bbolt` + `Bbolt/`) | 4,122 | 199,318 | 48x |

For pace: bbolt's proof went from infrastructure (2026-10-19) through the plan (11-03) to all
triples proved (11-05) with a coordinated agent swarm. That is about 200k lines in under three weeks.

**A, by component** (Go lines in the proof's scope: between executed and cut):

| component | Go lines | ratio | Lean lines |
|---|---|---|---|
| grpc transport (http2_client and http2_server, controlbuf and loopy, flow control, http_util, readers, keepalive) | 3.8-4.2k | 40x (raft- or bbolt-like: concurrency plus a byte protocol) | 150-170k |
| ClientConn, addrConn, balancers, resolver, picker, idle, serializers | 2.7-3.2k | 30x | 80-95k |
| streams, calls, retry and replay, `server.go` | 2.0-2.5k | 35x | 70-90k |
| the rest of grpc (status, metadata, options, mem pools, codec, channelz and stats guards, health) | 1.6-3.0k | 15x | 25-45k |
| x/net Framer and hpack | 1.2-1.5k | 25-30x | 30-45k |
| net/http client and server, HTTP/1.1 | 5.9-8.9k | 25x | 150-220k |
| std support only the libraries need (`net/textproto`, `bufio`, `net/url`, `container/list`, ...) | 0.5-1k executed (up to 3k with error paths) | 12x | 10-35k |
| protocol preludes: HTTP/2 bytes (frames, HPACK histories, ids, GOAWAY/REFUSED), HTTP/1.1 messages, gRPC framing | | | 20-40k |
| TCP extension and `net` (shared with B) | ~0.8k trusted Lean | | ~3k |
| **total** | **18-25k** | | **~0.55-0.75M** |

**B**, from the design (§6 there): about 3.1k lines of trusted Go models and ~800 lines of trusted
Lean, and 17k lines of proof. The design assumes a ratio of about 3x for the models (6k for an
1.8k-line grpc model, 3.5k for a 1.3k-line net/http model). This repository has never done better
than 10x. At 10-20x for the models, 8-12x for layer R's ~3k lines of real code, and 8-13k for the
preludes and N, B is **60-110k**.

**A against B**: 5-12x at the same ratios, an order of magnitude. Measured in this repository's
efforts, A is 2.5-4x bbolt, or 1.5-2x the whole etcd server proof. At human rates it is tens of
person-years against one to a few. A swarm parallelizes A worse than bbolt: the cross-node HTTP/2
invariant is a serial design bottleneck, as raft's invariants were.

**Risks particular to A:**

1. The HPACK and stream-state invariants are cross-node and pass through the byte pipes. They are new
   kinds of ghost state for this repository.
2. The reference-counted buffer pools.
3. Upstream churn. grpc-go releases about every six weeks and rewrites its transport and balancers
   often: `mem` buffers in 1.66, pickfirst and endpointsharding recently. Go 1.27 moved net/http's h2
   into its own package. Every bump re-opens the proof; B's models are pinned diffs.
4. Goose's semantic gaps, and the models of std callees, over 20k more lines.
5. A's trust is still not zero: goose, Perennial's std models (`reflect`, `fmt`, timers) and the TCP
   extension remain.

**What A buys:** the ~3.1k lines of trusted model Go and the two `modelChoose` hooks go. C5's argument
about grpc's own messages becomes a proof. The faithfulness review (U2) is no longer needed. The end
theorem's statement is the same.

## 5. What would make A cheaper

* **Prove safety only.** Treat flow control, BDP, keepalive, ping enforcement, backoff, quotas and
  idleness as "may fail or wait". Prove them free of panics and ownership-preserving, not correct.
  This saves about a quarter of the transport and ClientConn proofs.
* **Configuration**, all available today and most of it already the default:
  * no tracing, binary logging, stats handlers, compression, health checking or service-config
    retries;
  * `WithInitialWindowSize`/`WithInitialConnWindowSize` set: static windows, which turns the BDP
    estimator off;
  * no `DialKeepAliveTime`: no client keepalive goroutine. That is a program change; etcdstart sets
    it today;
  * `WithIdleTimeout(0)`: no idleness manager;
  * pick_first instead of round_robin: drops endpointsharding, though clientv3 hard-codes round_robin
    (a fork change, which the "no code change if not a bug" rule argues against).

  channelz registration cannot be turned off in v1.84. HTTP/2 multiplexing, HPACK and flow-control
  framing are not optional in grpc at all. net/http's h2 is already off and only needs its guards proved.
* **Verify only what runs.** Translate the rest names-only through goose's `translate` lists, as this
  repository already does, and prove the guards that keep it unreached (`EnableTracing`, `ml == nil`,
  `len(sh) == 0`, `tlsState == nil`). That is the "cut" column against the "static" one: about 2k lines
  of grpc and 7.6k of net/http that need no proof.
* **Upstream and Perennial.** A goose change supporting `LabeledStmt` (general, so allowed) and
  local types whose names repeat in the package. Or, upstream, rewrites of the 3 labeled loops, the
  R4 copies (copy through a local, as modelcheck suggests) and the duplicate local type.
* **Incrementally, behind B's specs.** Write B's model specs (the frame protocol, `UnarySpec`,
  `StreamSpec`, the HTTP contracts) as the specs real code must meet. Then replace one model at a time:
  1. hpack and the Framer as pure libraries (~1.2k lines, sequential: the cheapest real code, and the
     part with the best-understood specs);
  2. net/http's HTTP/1.1 client and server (6-9k lines, no multiplexing, 3 goroutines per connection);
  3. grpc's transport and ClientConn last (the 0.4M of the estimate).

  Each step keeps the end theorem and lowers the trust.

## 6. Recommendation

**Choose B for the end theorem now.** A is an order of magnitude more proof, about 0.55-0.75M Lean
lines, on code that changes upstream every few weeks. For the theorem's safety it buys nothing B lacks;
its gain is ~3.1k lines of reviewed, runnable trusted Go removed. Keep A open as a direction: write
B's model specs in the shape a real-library proof could meet, and if the trust base must shrink later,
verify hpack and the Framer first, then net/http's HTTP/1.1 client and server, then grpc's transport.

## 7. Side findings

* **crashreconf cannot run twice at once on this machine.** Its addresses are package constants
  (ports 24301-24315). The first soak's round 7 overlapped a round of another session that started at
  the same second (`/tmp/crashreconf-3068158057`, not mine, 01:15:09, its history kept, so probably
  Illegal too). That round logged `crashreconf: listen failed` on slot 4, and porcupine found the
  history **Illegal**: the clients had talked to two clusters. The second soak, on private ports, was
  7/7 Ok, as were all 40 earlier rounds in `crashreconf-test.md`. The Illegal is an artifact, not a
  finding about etcd. The evidence is moved to scratch (§8). Worth either a note in
  `crashreconf-test.md` (run with an overlay of the ports, or take a lock) or ports derived from an
  environment variable in the test harness, not in the program.
* **`/tmp` is out of inodes** (1,046,880 of 1,048,576, tmpfs). Other sessions' `u6*-ol`/`u7*-ol`
  scratch trees hold about 118k each, and Go builds fail with "no space left on device" unless
  `GOTMPDIR` points elsewhere. I deleted nothing of theirs.
* Goose rejects labeled statements outright, which this repository may hit again. A candidate for
  `notes/perennial-changes.md`, which I did not edit.

## 8. Reproducing

Scratch, `/home/ubuntu/.claude-E/jobs/b4c3a1d2/tmp/optA/`:

* `cg/main.go` (binary `bin/optacg`): the reachability tool. It writes `reached.json` (every reached
  top-level declaration, with its lines, static flags and features), `reached.json.edges.tsv` (the
  hybrid graph) and `.roots.txt`. Command:
  `GOTOOLCHAIN=go1.27.3 GOPROXY=off GOFLAGS=-mod=mod bin/optacg -dir <worktree>/examples -pkg ./etcd/crashreconf -out reached.json`
  (11s, 1.6 GB).
* The aggregation scripts in `py/`: `agg.py` (per package), `pruned.py` (configuration cuts; writes
  `.pruned.json`), `cov.py` (coverage to declarations; writes `.covered.json`), `subsets.py`,
  `feat.py`, `hard.py`, `marginal.py`, `stdcov.py` and `graph.py`
  (`path REGEX [BAN]`: a shortest call path from the roots).
* `cov/`: the overlays (`crashreconf_test_cov.go`, `crashreconf_ports.go`, `overlay*.json`), the
  instrumented binaries, `run3.log`/`run4.log`, and `merged.txt`/`merged2.txt` (`go tool covdata
  textfmt` of the members' and the parent's counters). Build: `go test -c -cover -covermode=atomic
  -coverpkg=... -overlay cov/overlay2.json ./etcd/crashreconf` with `GOTMPDIR` set. Run with
  `OPTA_COVDIR=<dir>` and `-test.gocoverdir=<dir>`.
* `bin/goose` (the pinned Perennial's `goose/cmd/goose`), the module `goosemod/` (`examples/go.mod`
  with absolute replaces), and `gooseout/*.log`, one per package. Command:
  `bin/goose -lean-root google.golang.org= -lean-root golang.org/x= -out gooseout -configdir gooseconf -dir goosemod <pkg>`.
* `illegal-round/round-76739385/`: the colliding round's history, porcupine page and node logs.
