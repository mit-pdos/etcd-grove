# Library drivers: robustness theorems for gRPC, net/rpc and net/http (plan, 2026-11-24)

The user's direction (2026-11-24): a top-level robustness theorem per library, whose driver -- a
deployable client and server -- is the executable, readable specification of every behavior of the
library that our proofs rely on (`.claude/skills/robustness/SKILL.md`). Each driver section names a
behavior, states the property in a one-line comment, exercises it with the program's own
nondeterminism (`primitive.RandomUint64`: sizes, kinds of calls, concurrency, dial paths), and
panics if it fails. The theorem (`Robust` over `DistDeploy`, two stable machines over the net
extension) says the client never panics; every gap left in the proof is an axiom in the example's
trust-base collection (`etc/tcb-collections/<example>.txt`), and the library is done when the
collection is empty but for the models' trusted claims and the net extension's semantics.

Coverage comes from a survey of how etcd, Kubernetes and the dsverify kits use each library
(2026-11-24; the behaviors are numbered as there: gRPC G1-G21, net/rpc R1-R12, net/http H1-H13).
The survey's table is kept with the coordinator's notes; the parts that decide each driver are
below.

## net/rpc: `examples/net/rpcdriver`

Users: the dsverify kits SwiftPaxos, EPaxos (on `lean`), CRAQ and Gryff (branches): all over HTTP
(`rpc.DialHTTP`; `Register`/`RegisterName`/`NewServer`, `HandleHTTP`, `http.Serve`). The driver's
server serves one service both over raw TCP (`rpc.Accept`) and over HTTP (`HandleHTTP`,
`http.Serve`), and its client dials either way at random.

| section | property | survey | relied on by |
|---|---|---|---|
| register | a receiver of an exported type with a suitable method registers; one with none is refused | R11 | every kit's `Register`/`RegisterName` |
| dial | a dial may fail; nothing is asserted of a failed dial | R8 | every kit's `DialHTTP` |
| call-success | `nil` from `Call`/`Go` means exactly one run of the method on these arguments, and the reply is that run's | R1 | swiftpaxos and epaxos `master.go`, craq `node.go`, gryff `master.go` |
| server-error | a `rpc.ServerError` carrying one of the method's messages (the driver's, `"driver: ..."`) is this request's own answer: the method ran on it and failed with that message | R2 | craq `kit.go` (`string(se) == errNotFound`) |
| other-errors | any other error says nothing of whether the method ran; the reply is not looked at | R3 | swiftpaxos `master.go` (resets the reply after a failed call) |
| concurrent-calls | concurrent `Call`/`Go` on one client each get their own outcome | R6 | swiftpaxos `client.go` |
| close | after `Close`, a call fails with an error that is not a `ServerError` | R7 | the kits' `Close` |

**Finding (2026-11-24, the proof): net/rpc's own errors are `ServerError`s too.** The first driver asserted
that every `ServerError` is the method's answer. net/rpc's server (Go's, and the model's
`readRequest`/`ServeCodec`) answers `ServerError(err.Error())` when a request's header was read but its
body's read or decode failed, or its service or method is unknown; and the net extension lets a read cut
one direction of a connection (client to server) while the other still delivers, so a request whose body
is cut short gets `ServerError("unexpected EOF")`. Go's documentation promises nothing more. Net's proofs
say the same (every service spec accepts the server's own answers, `errOk`, `srvErrMsg`). The section now
asserts only of the method's own messages, marked `"driver: "` so that they are none of net/rpc's.

Left out, and why: reply decoding merging into the caller's value (R4: a property of the codec, which
the generated codec's own tests check against gob); the sticky break of a connection (R5: a
property of a connection's history the driver could only observe by steering faults); concurrent
serving (R10: not observable by a client without timing); the debug page (outside the model).

Tests (`driver_test.go`): the machines as processes over real TCP; non-vacuity, 200 client runs in
one process with every section's check counted (`reached`); both with the real libraries and with
the models (`-tags netmodel`, the GOROOT farm of `models/goroot.py`).

Statement (2026-11-24): `rpcdriver_robust.spec`
(`Net/Spec/github_com/mit_pdos/etcd_grove/examples/net/rpcdriver/TopLevelRobustness.lean`): the
two machines (`system σs σc`, `TopLevelDefs.lean`), neither crashing, deployed at `rpcAddrs`
(`DistDeploy`), are `Robust [] … rpcThreads rpcSteps`: every execution of fewer than `rpcSteps =
2 ^ 63 - 1` steps along which each machine keeps fewer than `rpcThreads = 2 ^ 30` live threads
(net/http's mux takes reader slots, `threadBound ≤ 2 ^ 30`; net/rpc's server needs `≤ 2 ^ 31`).
Restated 2026-11-24 on review: the thread bound is `Robust`'s own, separate from the steps, through
`Net.robust_of_distBootIT` (`Net/Statement/DistBridgeExts.lean`, over Perennial's
`goose_dist_adequacy_below`, as dsv-steps63's kits, 70406b8fd3); before, the bridge tied the threads
to the steps (`threadBound = receiptBound + 1`) and the statement was `∀ threads, Robust [] … threads
rpcStepBound` with `rpcStepBound = 2 ^ 30 - 1` (first `2 ^ 31 - 1`, lowered after S5's review). No premise
but the deployment's start and the programs' typing facts. Proved 2026-11-24 over four interim
axioms (`etc/tcb-collections/rpcdriver.txt`): `net.rpc.wp_init_first`, `net.http.wp_init_first`
(first-run initializers, L2 step 6), `net.http.Handle.wp_proof`, `net.http.Serve.wp_proof_rpc`
(S5; both proved 2026-11-25 over the real `ServeMux` and server, `Serve` over the two interim context axioms
`context.WithValue.wp_proofPtr`, `context.WithCancel.wp_proofValBg`); `strings.Cut`/`TrimLeft` are Perennial's proofs (pin `d9c8c1d97`). The paragraph below is the plan as of the skeleton. The trust-base collection
`etc/tcb-collections/rpcdriver.txt` lists the `sorry` and the interim axioms of net/rpc's and
net/http's initializers (`Net/Proof/net/{rpc,http}/Init.lean`; their facts, `True`, in `PkgInit.lean`,
shared with `Dsverify/`'s `InitHyp`s; retired by L2 step 6, net/rpc's and net/http's initializers
proved). The proof will rest on net/rpc's proved specs (`Net/Proof/net/rpc`), and on what is not
proved yet: `HandleHTTP`, `http.Serve` on an rpc address (phase 7 S5), the initializers
(`notes/phase7-endstate.md`; the shared design of rpc over HTTP, L2). Note for the proof: the
package fact of net/rpc is `True`, so what the server and client proofs read of net/rpc's
variables (`errFrame`, the codec registry) must come from the boot, as the kits' `RpcBoot`. The kits keep their own `True` net/rpc and net/http
facts (`Dsverify/Proof/net/{rpc,http}/Init.lean`, their `InitHyp` premises): sharing `Net/`'s stronger
facts would change what their premises say; their switch to `Net/`'s initializers is dsverify-lab's.
The two instances are never imported together (nor, so, their `wp_initialize'`s). The `True` facts of
net/http's closure (`Net/Proof/<pkg>/Base.lean`) are shared.

## net/http: `examples/net/httpdriver`

The driver (`httpdriver.go`): the server serves a `ServeMux` (`NewServeMux`, `HandleFunc("/echo")`,
`HandleFunc("/status")`, `http.Serve`); the client opens random connections from random goroutines,
writes random raw HTTP/1.1 requests on each (`/echo` with a random method, `X-Driver` value and body;
`GET /status`; `GET /nope/<word>`; a malformed line), reads each response with `http.ReadResponse` over
one `bufio.Reader` per connection and its body with `io.ReadAll`, and checks it (sections echo, status,
mux, bad-request, keep-alive, concurrent-connections). Not `http.Client`: the model's `Transport` is
`notModelled`.

Statement (2026-11-25, `Net/Spec/github_com/mit_pdos/etcd_grove/examples/net/httpdriver/TopLevelRobustness.lean`):
`GodebugHttpmuxgo121Not1 → DistDeploy httpAddrs (system σs σc) g → Robust [] (system σs σc) g httpThreads
httpSteps`, with `httpAddrs = ["127.0.0.1:7401"]`, `httpThreads = 2 ^ 30` (net/http's mux, its reader
slots), `httpSteps = 2 ^ 63 - 1` (rpcdriver's; no spec bounds the receipts). The environment premise
(`GODEBUG` does not set `httpmuxgo121=1`, #18's option (a)) makes the server's `ServeMux` run Go 1.22's
matcher, the one proved. The boot table is `etc/gen-driver-boottable.py`'s (generic over the drivers).

### The interim axioms (revised on review 2026-11-25; `httpdriver_robust` proved over them, 2026-11-25)

Vocabulary: `Net/Proof/net/http/WireDefs.lean` (pure: requests, responses, paths) and `ProtoDefs.lean`
(phase 7 S5's draft vocabulary, defined; its header lists the departures from the draft), over S5's
landed `MuxDefs` (`muxOwn`, `muxRoute`; `muxAt m Ps := inv (muxFrozenN m) (muxOwn m Ps)`). Review and
fixes: `notes/axiom-review/net-http-interim.md` (2026-11-25). Four axioms (now three: `HandleFunc` proved), each in its function's file,
each retired by S5:

1. `net.http.ServeMux.HandleFunc.wp_proof` (`Net/{Spec,Proof}/net/http/ServeMux__HandleFunc.lean`):
   `litPattern p → p ∉ Ps → f ≠ func.nil → {{ isPkgInit http ∗ muxOwn m Ps }} m.HandleFunc(p, f)
   {{ muxOwn m (p :: Ps) ∗ muxRoute m p (HandlerFunc f) }}`. Reviewed sound; **proved 2026-11-25**
   (a theorem over the real `ServeMux`, as `wp_Handle_lit`; no longer an axiom).
2. `net.http.ServeMux.ServeHTTP.wp_proof` (`ServeMux__ServeHTTP.lean`): for literal, clean patterns `L`
   (`litPattern ∧ pathClean`: no `//`, which Go's routing tree routes like a wildcard), a
   protocol allowing the mux's own answers to the requests clients send (`muxNoRoute P L`: a `307` to a
   request it redirects, `muxRedirect`: the path not clean, or not a pattern, not ending in `/`, with
   `path ++ "/"` a pattern; a `404` with `NotFound`'s body to one it does not redirect and no pattern
   routes), and a body reader bounded below `2 ^ 60`:
   `⌜threadBound ≤ 2 ^ 30⌝ ∗ isPkgInit http ∗ use121 ↦□ false ∗ muxAt m (L.map fst) ∗ [∗] (p, h) ∈ L,
   muxRoute m p h ∗ handlerOk h P p ∗ servePre P pfx w r R τ rd I S E ⊢ WP m.ServeHTTP(w, r)
   {{ v, serveDone P R τ I S v }}`. `servePre` holds what the mux reads of the request (`srvReq`: method,
   `RequestURI`, `Host`, `URL`, protocol) and the fields it writes (`reqMuxFields`).
3. `net.http.Serve.wp_proof` (`Serve.lean`, beside the proved `Serve.wp_proof_rpc`):
   `{{ isPkgInit http ∗ httpSrvEnv ∗ protoLis la P ∗ handlerOk h P "/" ∗ isListener lis l ∗ netLisOn l
   la ∗ lisInv l la }} http.Serve(lis, h) {{ err, True }}` (`Serve.specHandler`'s shape): the server
   writes, on each connection, for the `i`-th request slot the dialer wrote, the handler's complete
   response (status, header lines `hdrView` the handler's, `Content-Length` body, `□ P.resp` and
   `□ P.respEnd` of it), the head of a chunked one (only after the handler wrote more than `2048`
   bytes, with `□ P.resp` of them), or net/http's `400` answer (`httpRespP P`). Requests (`reqOk`):
   a method token but `CONNECT`/`HEAD`/`PRI`, a `reqPath`, a `Host` of `hostByte`s, header lines the
   model reads as they are, none of `Transfer-Encoding`, `Expect`, `Connection`, `Trailer`, `Upgrade`,
   `Te`, `Pragma`, at most 500 lines counting `Host`, `Content-Length` matching the body, a head within
   `2 ^ 20` bytes.
4. `net.http.ReadResponse.wp_proof_resp` (`ReadResponse.lean`, beside the proved `CONNECT` case):
   `ReadResponse(b, nil)` over a `bufio.Reader` that has delivered `D` of a progressing stream whose
   bytes past `D` are, as long as it is read, nothing yet or consistent with the wire of a response `ρ`
   the model reads as written (`respOk`: no chunked body, a `Content-Length` line or close-delimited),
   with the caller's `□ Q ρ`, and nothing after an error: an error (with the reader), or `ρ`'s status,
   its header lines (`hdrOwn`, without `Connection: close`) and a body reader (`io.readerOk`) whose
   `io.EOF` gives `□ Q ρ` of a response with that head whose body is what was read (`Content-Length`) or
   extends it (close-delimited), and gives back the reader past the response. Reviewed sound.

Changed 2026-11-25 in the proof stage (approved by the dsverify-net lead as interim text; zeldovich-proving-2
checks (2) and (3) against go1.27.3): (1) `ReadResponse.spec_resp` takes the stream's length law
`□ ∀ r, S r -∗ ⌜r.length + 2 ^ 12 < 2 ^ 62⌝` (what `bufio.NewReader` takes; without it the axiom read heads
of any size through a reader specified only below `2 ^ 62` bytes); (2) `hdrsOk hs` adds
`(hs.flatMap hdrLineWire).length ≤ 2 ^ 21` (the handler's obligation, through `respOps`), with `servePre`'s
`R.path.length ≤ 2 ^ 20` (what bounds the mux's own `307`'s `Location`); (3) `respFacts`
bounds the head of a handler's answer, `.ans` and `.chunked`, to `≤ 2 ^ 22` bytes (Go's server adds under 512
bytes of its own: `writeStatusLine`, `(*chunkWriter).writeHeader`). The client needs (2) and (3) to bound its
stream for `bufio.NewReader`. And the driver's client leaves a connection after a `400` (not only after its junk
request): after a close-delimited answer whose body a cut connection ended early, no further `ReadResponse`
precondition holds. `ServeMux.HandleFunc`, `NewServeMux`, `HandlerFunc.ServeHTTP`, `Header.Get`/`Set` (and
textproto's `MIMEHeader.Get`/`Set`) are now translated, with their bodies.

Also trusted, changed here: `net.http.wp_init_first`'s `initFirstRes` now says `use121` is `true` only if
the run's `httpmuxgo121` setting is `"1"` (what the approved trusted `init` model does), so the driver
learns `use121 = false` from the environment premise.

Proved, not assumed (proof stage): `NewServeMux` (`muxOwnS_init` on `&ServeMux{}`), `muxOwn_freeze`,
`ServeMux.HandleFunc`, `HandlerFunc.ServeHTTP` (`f(w, r)`), `Header.Get`/`Header.Set` on canonical keys,
the connection registry (`httpRegInv`), the driver's code.

How the driver uses them: its protocol `P` (`P.hreq R τ`: a request the client writes, its body saved at
`τ`; `P.resp`/`P.respEnd`: a body of at most 32 bytes, `/echo`'s `200` with the request's method, path,
`X-Driver` value and (end) body, `/status`'s `418` with (a prefix of) `"short and stout"`, `404` with
`NotFound`'s body, any `307` to a redirected path, which the driver never sends) excludes chunked answers
(`2048 < |w|`), so every answer the client reads is `respOk`; the `i`-th `ReadResponse` on a connection
is at the `i`-th answer, which answers the `i`-th request written (keep-alive).

## gRPC

To come: gRPC's driver in the main tree (`models/grpc`; unary calls, the three stream
kinds as watch and lease use them, metadata, status codes and messages, context errors, concurrent
calls on one `ClientConn`, `Close`), whose collection drives phase 7's S2/S3.
