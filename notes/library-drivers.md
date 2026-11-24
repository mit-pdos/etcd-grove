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
| server-error | a `rpc.ServerError` is the method's own error, after it ran on this request | R2 | craq `kit.go` (`string(se) == errNotFound`) |
| other-errors | any other error says nothing of whether the method ran; the reply is not looked at | R3 | swiftpaxos `master.go` (resets the reply after a failed call) |
| concurrent-calls | concurrent `Call`/`Go` on one client each get their own outcome | R6 | swiftpaxos `client.go` |
| close | after `Close`, a call fails with an error that is not a `ServerError` | R7 | the kits' `Close` |

Left out, and why: reply decoding merging into the caller's value (R4: a property of the codec, which
the generated codec's own tests check against gob); the sticky break of a connection (R5: a
property of a connection's history the driver could only observe by steering faults); concurrent
serving (R10: not observable by a client without timing); the debug page (outside the model).

Tests (`driver_test.go`): the machines as processes over real TCP; non-vacuity, 200 client runs in
one process with every section's check counted (`reached`); both with the real libraries and with
the models (`-tags netmodel`, the GOROOT farm of `models/goroot.py`).

Statement and proof: to come (`Net/Spec/.../rpcdriver/TopLevelRobustness.lean`). The proof rests
today on net/rpc's proved specs (`Net/Proof/net/rpc`), and on what is not proved yet:
`HandleHTTP`, `http.Serve` on an rpc address (phase 7 S5), and the initializers of net/rpc and
net/http (`notes/phase7-endstate.md`; the shared design of rpc over HTTP, L2).

## gRPC and net/http

To come, in that order: gRPC's driver in the main tree (`models/grpc`; unary calls, the three stream
kinds as watch and lease use them, metadata, status codes and messages, context errors, concurrent
calls on one `ClientConn`, `Close`), whose collection drives phase 7's S2/S3; then net/http's with
the S5 server work, its client side limited by the model (the `Transport` and chunked bodies panic
`NotModelled`).
