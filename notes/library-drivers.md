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
but the deployment's start and the programs' typing facts. Proved 2026-11-24 over interim
axioms (`etc/tcb-collections/rpcdriver.txt`): `net.http.wp_init_first` (first-run initializer, L2
step 6; net/rpc's `wp_init_first` proved since dsv-fix2b, 2026-11-25); `net.http.Handle.wp_proof`,
`net.http.Serve.wp_proof_rpc` (S5) proved 2026-11-25 over the real `ServeMux` and server, `Serve` over
the two interim context axioms `context.WithValue.wp_proofPtr`, `context.WithCancel.wp_proofValBg`;
`strings.Cut`/`TrimLeft` are Perennial's proofs (pin `d9c8c1d97`). The paragraph below is the plan as of the skeleton. The trust-base collection
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

## gRPC and net/http

To come, in that order: gRPC's driver in the main tree (`models/grpc`; unary calls, the three stream
kinds as watch and lease use them, metadata, status codes and messages, context errors, concurrent
calls on one `ClientConn`, `Close`), whose collection drives phase 7's S2/S3; then net/http's with
the S5 server work, its client side limited by the model (the `Transport` and chunked bodies panic
`NotModelled`).
