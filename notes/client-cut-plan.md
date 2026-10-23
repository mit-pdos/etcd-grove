# Plan: cuts between clients and members in `linkv3p`, and recovery from them

Status: done (2026-10-21; K0, K1, K3 on branch `client-cut`, K4 on branch `failover`, both merged
into `lean`): K2 dropped (the bridge is part of the network, its code not verified:
`notes/decisions.md` D26, the user's decision); K4, failover, done (D27). `linkv3p_safe` now covers
client-member cuts, recovery at the same member, and clients of every member (failover).

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
  (`issues/nonissues/etcd-bridge-blackhole-twice-panic.md`, reproduced by
  `third_party/bridge/bridge_test.go`). Since `Main`'s theorem is for every schedule, linkv3p's
  `partitioner` records which bridges are blackholed and skips a second `Blackhole`
  (`clientStep`'s `holed`). The bridge's `Blackhole` spec (D26) takes the bridge unblackholed.
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

**Decided (2026-10-21): `notes/decisions.md` D26, the bridge as part of the network.** A first
draft, carried out through K3, specified a relay (16 axioms over `net`'s connections, so that the
bridge's proof could show it only relays) and proved the bridge. The user's question: why prove the
bridge at all? The network model already lets every attempt fail, so `linkv3p_safe` covered
client-member failures before the bridge; the bridge is test infrastructure that only makes them
happen. So the bridge's calls linkv3p makes (`New`, `Blackhole`, `Unblackhole`,
`DropConnections`) have trust-boundary specs over one axiomatized predicate (`bridgeAt`), `New`'s
giving the forwarding fact: 5 axioms (`Proof/github_com/mit_pdos/etcd_grove/third_party/bridge/`).
The relay specs, the bridge's proofs and `net.Conn`'s translation were removed (in the branch's
history, K1-K3's commits).

### K2. The bridge proved (dropped: D26)

Its functions: `newBridge`, `serveListen` (the accept loop; `pausec` and `stopc`), `serveConn`
(two copy goroutines and a local `WaitGroup`), `ioCopy` (the copy loop and the blackhole
branch), `bridgeConn.Close`/`close`, `Blackhole`, `Unblackhole`, `DropConnections`,
`PauseConnections`, `UnpauseConnections`, `Close`. These are safety specs: no panic; `Close` on a
closed channel is never reached (`select` on `stopc`, `pausec`, `blackholec` under `mu`); the
connection map under `mu`; the `WaitGroup`'s counter with thread tokens (as Perennial's
`WaitGroup` spec takes since `105fb79f5`). A lock invariant holds the map and the three channels'
states. The bridge holds no gRPC resource: its specs say nothing about the bytes.

**Done (2026-10-21), then removed with D26's decision** (what follows is what the proof took,
kept for the record). `Proof/github_com/mit_pdos/etcd_grove/third_party/bridge/`: `Defs.lean`
(the protocol), `Lemmas.lean`, and the proofs of the functions linkv3p calls and their callees:
`New`, `newBridge`, `serveListen`, `serveConn`, `ioCopy`, `bridgeConn.Close`/`close`,
`dialer.Dial`, `Blackhole`, `Unblackhole`, `DropConnections` (11 of the package's 14 functions;
`Close`, `PauseConnections`, `UnpauseConnections` are not verified: linkv3p does not call them).
`Link.lean` by `etc/gen-link.py --bridge`. What the proofs needed:

- **`b.blackholec` read without the mutex** by every copy goroutine and written by `Unblackhole`
  under it (race-free in Go because `Unblackhole` waits for every registered connection's
  `donec` first): each registration halves the mutex's fraction of the field for the new
  connection's goroutines; `serveConn` deposits the share in an invariant and closes `donec` with
  it; whoever removes the connection from the map trades a claim token for it. The mutex holds a
  wand from its fraction and the outstanding shares to the whole field, so no fraction
  arithmetic beyond halves.
- **A registry of every connection ever registered** (insert-only ghost map, persistent
  entries): `serveConn` knows its entry is its own; a fresh allocation is not registered, since a
  registered connection's fields are persistent and the fresh one's owned whole.
- **The bridge's wait group**: `serveConn`s counted by deposited thread tokens (`serveListen`
  deposits the loop's, the `go` statement gives a fresh one back); `serveListen` itself by a flag,
  since the caller of `New` keeps its token and the fresh one goes to `serveListen`, which needs
  one for its first `Add`. So the counter is below `threadBound GF + 1`, and linkv3p's run bound is
  one less (`n + 3 ≤ 2 ^ 31`).
- **`serveConn`'s local wait group** (`Add(2)`, which Perennial's join idiom, `Add(1)` at a time,
  does not cover): a pair invariant of its own.
- **`Blackhole` takes the owner's flag "not blackholed"** (`bridgeHoled γ false`): the panic of a
  second call (`issues/nonissues/etcd-bridge-blackhole-twice-panic.md`) is excluded by the premise, which
  linkv3p's `clientStep` meets by tracking the flags (`holed`).

Perennial limitations met, worked around locally (to propose upstream): `wp_load` does not load a
field through a persistent points-to of the whole struct (the connection's fields are persistent
field by field); there is no validity lemma for typed points-to (`loc_own_discard`, for `Loc`'s,
from `heapPointsto_valid`).

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

**Done (2026-10-21).** `peerStep` (the old loop body), `clientStep`, `startBridge` (`net.Listen`,
`bridge.New`: the bridge owned and `forwards bridgeAddr clientAddr`), `partitioner` over both,
`Main` (the clients at the bridges' addresses, `clientOk`'s registrations through
`isGrpcRpc_forwards`), `Adequacy` (nine addresses; the run bound unchanged, `n + 2 ≤ 2 ^ 31`) and
`Results`. Gates (after D26's decision): `lake build` (5931 jobs), every `gen-link` mode (the
`--bridge` mode removed), `goose --check`, `gen-init --check`, `tcb-report --check` (the baseline:
526 axioms, 2 sorries, D26's 5 axioms over the merge base's) and every collection (`linkv3p.txt`:
463 -> 468, exactly D26's; no other collection moves), `verified-code.py` (linkv3p 9 of 9
functions; the bridge's 14 translated, none verified: its 4 assumed specs are linked in
linkv3p's `Link.lean`, which the script counts under linkv3p's project).

### K4. Failover (D-C4)

**Done (2026-10-21, branch `failover`; `notes/decisions.md` D27, approved).** Stages:

- **K4a, K4b (done):** the gRPC boundary over a list of addresses (`grpcConn conn addrs`,
  `grpcResolverAt`, `NewClient`, `Invoke`'s attempt at one of them, `isGrpcRpcs`; streams at one
  address) and the client over it (`clientCfgOk cfg eps`, `isNewClient cl eps V`, every unary call
  at `isGrpcRpcs`; the lessor's keep-alive and the watcher at one address). The examples keep their
  statements at `[ep]` (`isGrpcRpcs [a]` reduces to `isGrpcRpc a`). No axiom added or removed.
- **K4c (done):** failover's end-to-end results: a call through a client of several members' endpoints,
  each registering its own spec, at the conjunction of the specs; the reply is some member's
  (`Proof/go_etcd_io/etcd/client/v3/Failover.lean`: `anySpec`, `isGrpcRpcs_anySpec` from
  `isGrpcRpc_mono`, `client_put_any`, `client_range_any`, `client_delete_any`, `client_txn_any`,
  for a one-attempt client).
- **K4d (done):** linkvtxn's `Apply`, `call`, `call*` and `Calls.lean` for a client of the members
  `ms` (`kvRegsAt` per member, the updates `[∧ list]`, built per member from the instance's
  invariant at its names, `bigAndL_of_sep`); linkvtxn's own `Check` the one-member case (its
  statement unchanged); linkv3p's `newClient(eps, lg)` and its three clients each of the three
  bridges' addresses (`clientOk` over the members). The closed theorem's statement is unchanged.
  The Go tests: `TestClientCuts` keeps one bridge per client (recovery at the same member), and
  `TestFailover` (every client of the three bridges; member 1's bridge blackholed and its
  connections dropped from 50ms to 3.1s) shows every client working while member 1's link is cut:
  about 2,200-2,500 operations per client succeeded during the cut, 3 failed in all; `go test
  -race` passes. Gates: `lake build` (6935 jobs), every `gen-link` mode, `goose --check`,
  `gen-init --check`, `tcb-report --check` (526 axioms, 2 sorries: none added) and every
  collection.

The original stage:

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
