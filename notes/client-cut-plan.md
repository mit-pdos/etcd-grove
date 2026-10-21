# Plan: cuts between clients and members in `linkv3p`, and recovery from them

Status: in progress (2026-10-21): K0 done (branch `client-cut`, worktree `/shared/etcd-grove-cc`);
linkv3p's `partitioner`, `Main` and `Adequacy` proofs do not build until K3.

## Goal

`linkv3p_safe` (`Proof/github_com/mit_pdos/etcd_grove/examples/linkv3p/Results.lean`) covers a
three-member cluster whose **peer** links a schedule cuts and mends (`EtcdServer.CutPeer`/
`MendPeer`), with a one-attempt client at every member and linkvtxn's KV workload. Extend the
program and the theorem so that the schedule also cuts and mends the link between a **client
and its member**, and the clients recover after a cut:

> For every `clients`, `ops` and every schedule `sched` of peer cuts, peer mends, client cuts
> (blackhole, drop) and client mends, every real execution of `n` steps of `linkv3p`'s
> initialization followed by `Main(clients, ops, sched)` has no stuck thread, no thread ended in
> a panic (so the history of KV operations is linearizable against etcd's KV model), and the
> main thread's result, if any, is `Ok` or `Unknown`.

What "recovery" can mean, from cheapest to most expensive:

1. **Recovery at the same member**: after a mend, the same client's calls to the same member
   succeed again (gRPC re-dials its connection). Operations that failed during the cut are
   recorded as failed: a failed write stays pending and may take effect later, a failed read
   constrains nothing (the model already does this, `PendModel.lean`).
2. **Failover**: a client configured with all three members' endpoints keeps working through a
   cut of one member, its calls going to the others.
3. **Retries inside the client** (`MaxUnaryRetries > 1`) and **watches resumed across a cut**:
   not in this plan (below, "Later").

The plan does (1) in full and (2) as its last stage.

## What is already there

- **The model already lets any client call fail, even after the server applied it.**
  `grpc.ClientConn.Invoke`'s axiom (`Spec/google_golang_org/grpc/ClientConn__Invoke.lean`,
  `grpcInvokerOk` in `Proof/google_golang_org/grpc/InvGrpc.lean`) has an error branch with no
  precondition and "nothing about whether the handler ran"; no error code is excluded
  (`clientErr`, `statusErrOk`). So, as with peer partitions, every execution of a cut client is
  already one the theorem quantifies over. What is missing is in the program and the statement:
  nothing cuts a client's link, nothing shows recovery, and the theorem does not say it covers
  either.
- **Each attempt is independent.** `grpcConn conn addr` is an opaque persistent fact: gRPC's
  reconnection is not modeled, and none is needed for (1). After a cut, a later attempt may
  succeed.
- **One attempt per call, by design.** The linearizability proof needs a write's update (an
  ordinary atomic update) to fire at most once (D21 M6). The client gives that only when it is
  configured for one attempt (`MaxUnaryRetries: 1`, D21i: `clientKVOnce`, `etcdInterceptorOk1`).
  The interceptor's proof is general (`etcdInterceptorOk` for any retry bound), but over a
  persistent `□ Spec`.
- **One endpoint per client.** `clientCfgOk` (`Proof/go_etcd_io/etcd/client/v3/InvClientNew.lean`)
  requires `Endpoints = [ep]`, no dial options and no keepalive. `grpc.NewClient`'s axiom resolves
  to that one address for good.
- **No network below gRPC.** `net` is names-only, with `net.Listen` the only spec
  (`Proof/net/InvNet.lean`: "Perennial has no network model"). Nothing models `net.Conn`.
- **etcd's mechanism for client cuts is its integration tests' bridge**
  (`tests/framework/integration/bridge.go`, about 230 lines): a TCP proxy between a client and a
  member, with `Blackhole`/`Unblackhole` (bytes read and dropped, connections kept open) and
  `DropConnections` (every proxied connection closed), and `PauseConnections`. etcd's
  `TestKVPutAtMostOnce` drops a member's client connections during puts and checks at-most-once.
  The robustness tester has no client cut: it blackholes peer traffic only
  (`tests/robustness/failpoint/network.go`).

## Design

**D-C1. Cuts through a copy of etcd's bridge, between each client and its member.** The bridge
listens at a new client address per member and forwards to the member's client address. The
partitioner's steps gain kinds: a client blackhole, an unblackhole, a drop. The bridge is in the
program, so its goroutines are in the theorem ("no thread ends in a panic"). `newBridge` is
unexported in package `integration`, and that package is etcd's whole test framework, so the
example carries a copy of `bridge.go` (package `examples/bridge`, the file's code unchanged,
attributed), translated by Goose.

**D-C2. The trust boundary: `net`'s connections and one forwarding fact.** The bridge's code
calls `Listener.Accept`, `net.Dial`, `Conn.Read`, `Conn.Write`, `Conn.Close` and `io.Copy` (to
`io.Discard`). It needs:

- names-only trust-boundary axioms for these: each returns, `Read` fills its buffer with some
  bytes or errors, `Write` reads its buffer, `Close` may be called any number of times and from
  any thread, `Accept` and `Dial` give a connection or an error;
- **one fact that is about gRPC, not bytes**: a client that dials the bridge's address reaches
  the member's registrations (`isGrpcRpc` at the bridge's address from `isGrpcRpc` at the
  member's, for a bridge started between the two). It holds because the bridge only copies bytes
  or drops them: it never alters or invents them, and a dropped byte is a failed attempt, which
  the model already allows. It cannot be proved here, since gRPC's wire protocol is not modeled.
  It is the analogue of D21j: a restated transport contract. **It is asked of the user (K1).**

Alternatives:

- (b) the bridge axiomatized whole: `newBridge`, `Blackhole`, ... return, plus the forwarding
  fact. Fewer axioms, but its goroutines leave the program, and the theorem says nothing about
  them.
- (c) no proxy: a cut is `cli.Close()` and recovery a new `clientv3.New`. There is no new trust,
  but it is a client restart, not a network cut: no call is ever cut mid-flight by the network.

Recommendation: (a), the bridge verified over the `net` axioms, plus the forwarding fact.

**D-C3. Recovery (1) needs no new client proof.** Each attempt is independent in the model, so a
client whose link was mended may succeed again. In Go, recovery is etcd's client's own: its calls
default to `grpc.WaitForReady(true)` (`client/v3/options.go:26-29`), so a call made while the
connection is down waits in gRPC for a connection rather than failing, and gRPC re-dials the
bridge. The one-attempt configuration stays, so writes
keep at-most-once firing. The Go test shows recovery (D-C5).

**D-C4. Failover (2) generalizes the client to several endpoints.** `clientCfgOk` takes a list of
endpoints. `grpc.NewClient`'s axiom is restated: its resolver reports the list, and each attempt
goes to one of its addresses (a restatement, as D-C2's; asked). `clientOk` holds every member's
registrations, each with that member's apply environment and ids. linkvtxn's `Apply.spec` then
takes "the call is served by some member `i`", and `linkvInv_congr` already gives the invariant
at every member's names. This changes the client's results (`InvKVConn`'s `kvObjAt api ep`),
which other examples use: it is the stage most likely to grow.

**D-C5. Nontriviality by the Go test, as D-P5.** `TestMainRun` with a schedule that blackholes
member 1's client, waits, unblackholes, then drops member 2's connections, checks:

- `Ok`;
- some operations failed during the cut (count the `Apply` errors);
- operations through the cut client succeeded after the mend (the client's last calls succeed;
  the store's revision moved after the mend).

Calls use `context.Background()`, and the client's keepalive is off (`clientCfgOk`). So a call
in flight on a connection that a blackhole silences hangs until the unblackhole closes that
connection, and then fails (`Unavailable`; a write is not retried). A call made while there is no
connection, including one whose handshake the blackhole stalls, waits and then succeeds. A schedule must
therefore mend every blackhole for the test to finish. That affects only the test's running time
(liveness); the theorem quantifies over every schedule. `DropConnections` fails calls at once.

## Stages

### K0. The Go program, and a finding to confirm

- `examples/bridge`: the copy of `bridge.go` (and the `Dialer` it takes: a `net.Dial` to the
  member's address).
- `linkv3p.go`: three bridge addresses; `startMember` (or `Main`) starts a bridge per member;
  `newClient` dials the bridge; `Step` gets a kind (peer cut, peer mend, client blackhole,
  client unblackhole, client drop); `partitioner` applies it. `TestMainRun` as D-C5, and
  `-race`.
- **A finding to confirm first** (done: not a bug). etcd's client retries a write only when
  `isSafeRetryMutableRPC` (`client/v3/retry.go:85-94`) sees "there is no address available" or
  "there is no connection available", and grpc-go v1.84 produces neither. But the client's
  default call options include `grpc.WaitForReady(true)`, so an attempt made while the connection
  is down does not fail: it blocks in gRPC until there is a connection or the deadline passes. A
  probe (a default client, an endpoint that refuses connections, a 3s deadline) shows the `Put`
  and the `Get` both waiting out the deadline. The two strings are a leftover of an older grpc;
  the behavior is safe and recovers by itself. Nothing for `issues/`.

**Done (2026-10-21).**

- `third_party/bridge`: etcd's `bridge.go` (package clause changed) and `dialer.go` (etcd's
  `dialer`, copied, and an exported `New`), with `UPSTREAM.md` and etcd's `LICENSE`. Goose
  translates it unchanged (project `bridge` of `etc/goose.py`, translating `net.Conn` through
  `net`'s names, `io.Copy`/`io.Discard` through Perennial's `io`); its package fact is `True`
  (`Proof/.../third_party/bridge/Base.lean`; `Init.lean` generated).
- **A finding**: a second `Blackhole` without an `Unblackhole` in between panics ("close of
  closed channel"), holding the bridge's mutex
  (`issues/etcd-bridge-blackhole-twice-panic.md`, reproduced by
  `third_party/bridge/bridge_test.go`). Since `Main`'s theorem is for every schedule, linkv3p's
  `partitioner` records which bridges are blackholed and skips a second `Blackhole`
  (`clientStep`'s `holed`). K2's `Blackhole` spec takes the bridge unblackholed.
- `linkv3p.go`: three bridge addresses (`127.0.0.1:2385{1,2,3}`), `startBridge`, the clients dial
  the bridges, `Step.Kind` (`PeerCut`, `PeerMend`, `ClientBlackhole`, `ClientUnblackhole`,
  `ClientDrop`), `peerStep`/`clientStep` under `partitioner`. Re-translated, `gen-init` rerun.
- Tests, each that starts members in a child process (`inChild`: a member keeps its ports until
  its process exits; the child gets the parent's deadline less 30s):
  - `TestMainRun`: 3 clients of 150 operations, a schedule that isolates each member in turn for
    3s, back to back from 0.5s (so some member is isolated until the schedule ends, and every
    client waits out request timeouts until then: the run outlasts the schedule, whose leader
    isolation the re-election check needs), with member 3's client blackholed during the first
    isolation and member 2's connections dropped as it ends: `Ok`. 25 of 25 runs, 9.7-14.9s;
    every member at raft term 5 or more.
  - `TestClientCuts` (D-C5): `Main`'s pieces with an apply that records each operation's client
    and outcome, 3 workers of 600 operations. It warms each client up first (a connection begun
    during a blackhole only waits, so nothing would fail). Then it drops member 2's connections
    twice (20ms, 50ms), while every worker runs, and blackholes member 1's client from 0.1s to
    3.1s, which soon holds every worker, so the run outlasts it however fast operations are.
    Twenty of twenty runs, about 3.2s each: `Ok`; all three workers' calls through client 1 failed
    at the unblackhole; client 1 then served about 600 operations; the drops failed 0-2 calls at
    client 2.
  - `go test -race` passes (five runs of the package, 18-23s each, no race reported; and
    `third_party/bridge`'s test).
- **Porcupine's check is the test's running time** (not the network): a run of the earlier
  `TestMainRun` (8 clients of 150, or of 400, operations; isolations 0.5s apart) took minutes now
  and then, once 35 minutes, before and after the bridge (a pre-bridge loop: 1 of 15 runs past
  60s; and `TestClientCuts`, with 6 workers of 1000, once 97s). The goroutine dump: every client done, `Main` in `porcupine.CheckOperationsVerbose` (no
  timeout), stepping linkvtxn's model. A failed write stays pending in the model to the end of
  the history (`closure` explores every subset and order of the pending writes), and each client
  fails about one operation per isolation, so the cost grows exponentially with
  clients x isolations. Hence 3 clients, and 3 workers. The model is the theorem's; nothing changes
  there.

### K1. The trust boundary (asked of the user)

- The `net` axioms (D-C2), stated in `Spec/net/` and `Proof/net/`, names-only, with
  `netAddrFree` for the three bridge addresses.
- The forwarding fact, stated as a restatement next to `grpc.serve` (`InvGrpc.lean`). Its exact
  form is to be designed: a persistent `grpcForward a b`, which the bridge's start gives, and
  under which `grpcServes b` gives `grpcServes a`.
- Write the decision down (`notes/decisions.md`), as D21j's, and ask.

**Drafted (2026-10-21), not yet approved: `notes/decisions.md` D26.** The plan's forwarding fact
("a listener at `a`, given up, serves what `b` serves") is unsound alone, since byte-agnostic
`Read`/`Write` specs would let a program write invented replies. D26 instead proposes a relay:
connections accepted at `a` are paired with ones dialed to `b`, and each direction writes a prefix
of what it read. `Proof/net/InvRelay.lean` holds the forwarding fact `grpc.relay`, the relay's
predicates and the specs of `Accept`, `Listener.Close`, `Conn.Close`, `Read`, `Write` and the
pairing; `net.Dial` and `io.Copy` (to `io.Discard`) are `Spec`/`Proof` pairs. `net.Conn` is
translated as an interface (`Code/net.toml`, which now imports `time`), so the bridge's
connection fields load and store without the axiomatized type's `sorry`; that moved `net`'s
initializer and the examples' package tables (regenerated), and nothing else (the full build
passes but for linkv3p's three proofs, as before).

### K2. The bridge proved

Its functions: `newBridge`, `serveListen` (the accept loop; `pausec` and `stopc`), `serveConn`
(two copy goroutines and a local `WaitGroup`), `ioCopy` (the copy loop and the blackhole
branch), `bridgeConn.Close`/`close`, `Blackhole`, `Unblackhole`, `DropConnections`,
`PauseConnections`, `UnpauseConnections`, `Close`. These are safety specs: no panic; `Close` on a
closed channel is never reached (`select` on `stopc`, `pausec`, `blackholec` under `mu`); the
connection map under `mu`; the `WaitGroup`'s counter with thread tokens (as Perennial's
`WaitGroup` spec takes since `105fb79f5`). A lock invariant holds the map and the three channels'
states. The bridge holds no gRPC resource: its specs say nothing about the bytes.

### K3. linkv3p over the bridge

- `newClient` at the bridge's address; `clientOk`'s registrations at it, from the forwarding fact
  (`startMember`'s result, or `Main`'s).
- `partitioner`'s new step kinds, over the bridge's specs.
- `Main` starts the bridges; `Adequacy.lean`'s addresses are nine (`linkv3pAddrs`); the statement
  is otherwise unchanged.
- Gates: `lake build`, every `gen-link` mode (`--linkv3p` gains the bridge's results), `gen-init`
  (linkv3p's closure gains `examples/bridge`, `io`), `goose --check`, `tcb-report --check`
  (`--update` for the new axioms) and every collection. `linkv3p.txt` gains exactly the `net`
  axioms and the forwarding fact; nothing else moves. `verified-code.py` (the bridge's functions
  verified).

### K4. Failover (D-C4)

- The client over a list of endpoints (`clientCfgOk`, `newClient`, `dialWithBalancer`,
  `grpc.NewClient`'s restated axiom), the per-endpoint registrations, `kvObjAt` over the list.
- linkvtxn's `Apply.spec`, or linkv3p's own, at "served by some member".
- linkv3p's clients take all three bridge addresses. The Go test: during a cut of one member's
  client link, operations through every client still succeed (some fail while the balancer
  notices).
- The existing single-endpoint results stay, as the one-element case.

## Later (not this plan)

- **Watches across a cut**: the watch client's reconnection is being verified on branch
  `watch-resume` (D24; its last stage, S1e, drops `noRetryableStreamErr` from `watch_safe` and
  `cache_safe`). Using it here needs a watch workload in linkv3p (linkvtxn has none), checked as
  watchkv's. That is a plan of its own, after S1e lands.
- **Retries inside the client** (`MaxUnaryRetries > 1`):
  - for reads (`Range` is retried on `Unavailable`): a retried read runs its handler more than
    once, so its update would have to be persistent, or fire only at the returned run;
  - for writes: a retry is safe only when the attempt is known not to have been applied, which
    `Invoke`'s error branch never says. Retrying writes would need that branch to carry the
    update back for errors that imply "not sent". After K0's finding, those errors may never
    arise with grpc v1.84 at all.
- **Crashes and restarts** of members (no crash semantics), and **liveness** (that a client
  recovers within some time after a mend).

## Risks and open questions

- **The forwarding fact's form** (K1). It must not let a client obtain more than the member's
  registrations give: a dropped byte must surface as an attempt's error, which `grpcInvokerOk`
  already allows. If gRPC's HTTP/2 framing could make a truncated stream look like a success
  (it cannot: frames are length-prefixed, and the bridge never invents bytes), the fact would be
  false. This needs an audit, as D21j's.
- **Goose and the bridge**: `io.Copy`, `io.Discard`, a map of pointers as a set, `select` with a
  `default`. Each should translate (Perennial has `io`'s interfaces); `io.Copy` may need a model.
- **The test's running time** under blackholes (D-C5). Keep the cuts short and mend every one.
- **K4's reach**: the client's single-endpoint assumption is used by every client example
  (putget, putget3, linkv*, watchkv, cachekv). K4 must keep their statements, by making the
  single endpoint the one-element case.

## Sizing (rough)

- K0: small (Go, a copy of the bridge, the schedule's kinds, the test).
- K1: a decision and two small files.
- K2: medium: about 230 lines of Go with goroutines, channels, a mutex, a map and a `WaitGroup`.
  It is the size of `partitioner` plus `startMember`'s serving steps.
- K3: small to medium, edits of linkv3p's proofs.
- K4: large, because the client's results change.

(1) alone (K0–K3) is a self-contained result: client cuts, recovery at the same member, on the
present trust base plus the `net` axioms and the forwarding fact.
