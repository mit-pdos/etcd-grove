# Plan: watches across a cut (linkv3p)

Status: W0 done (2026-10-21, branch `watch-cut`); next W1. Follows `notes/read-retry-plan.md` (D29),
`notes/keepalive-plan.md` (D28) and `notes/client-cut-plan.md` (D26, D27), whose "Later" section
lists this item.

## Goal

A production client's watch survives the cut of the member it streams from. The stream breaks:
keepalive closes the connection, or the bridge drops it. The watch client re-opens the stream on
the same `ClientConn` (`openWatchClient`), and grpc's balancer picks a reachable member. The client
resumes each watch from the revision after the last one it delivered (`ws.initReq.rev`, D25). The
caller sees one gapless, duplicate-free stream of events, whichever members served it.

This plan adds a watch workload to linkv3p and extends `linkv3p_safe` to it. The watch side gets
watchkv's guarantees: events gapless from the start revision, each a write that was attempted, and
each successful write the event at its reply's revision. These must now hold through cuts and
failover, with the stream served by different members over its lifetime.

## What is there today (the survey of 2026-10-21)

The watch is tied to **one address and one member** at every layer:

- **The gRPC stream boundary**:
  - `grpc.ClientConn.NewStream`'s axiom takes `grpcConn conn [addr]` and `isGrpcStream addr …`
    (`Spec/google_golang_org/grpc/ClientConn__NewStream.lean:49-65`). D27 widened only unary
    `Invoke` to address lists and left a stream over several endpoints uncovered.
  - The server side is per address too: `grpcStreamServerAt`, `grpcServesStream`,
    `grpc.serveStream` (`InvGrpcStream.lean`). There is no list form, unlike `isGrpcRpcs`.
- **The watch client's proof assumes one server for every epoch**:
  - `WEnv` holds one `WSrv`, one member's mvcc watch names (`InvWatch.lean:109`).
  - `openWatchClient`'s spec returns a stream with `watchSpec V.R` each time.
  - The resume invariants are stated against that one store: `WatchResume.lean`,
    `WatchResumeSrv.lean` and `WatchRecon.lean` use `startOk V`, `mvcc.startRead`, `relLb` and
    `respRev` of `V.R.γ`.
  - D25's item 5 relies on the resumed start revision being one the same store notified.
  - The watcher is usable only for `eps = [V.addr]` (`isNewClient_watcher`,
    `InvClientNewResult.lean:149-155`).
- **The events are per-member facts**:
  - watchkv's event facts (`evFact`, `revAt`, `WatchFacts.lean:38`, `Defs.lean:132`) are about
    one member's sealed mvcc log, `E.γ.idx`.
  - linkv3p gives each member its own mvcc names (`Alloc.lean:62-64`), and the members share only
    the KV state variable, the model of the committed log (`ρᵢ.rd.kv.st`, `srvKVInvs`).
  - No lemma lifts a member's `revAt` to the shared log.
- **linkv3p excludes watches**:
  - A dummy watch environment, `noWatch` (`Main.lean:52-56`).
  - `startMember` builds without watch readers (`grpcCfgOk_of_started'`, not the `_w` variant).
  - `memberServed` exports the KV registrations only.
  - The bridge's `forwards`, and `bridge.New`'s trust-boundary spec, cover unary methods only.

## Design questions

**Q1. Streams over a list of addresses (a trust-boundary change, D30, asked).**
- `NewStream` on `grpcConn conn addrs` with the method registered at every address, as D27 did for
  `Invoke`. The stream is bound to the one address the balancer picked, for its whole life: one
  HTTP/2 stream on one subconnection.
- The open question is what the returned stream's spec names:
  - **(a) A spec common to the members.** Each member registers its own watch spec, but the
    client needs one spec, stated cluster-wide (Q2).
  - **(b) Some member, existentially.** The stream comes with "some member `x` of `addrs` and
    `x`'s spec". The client then needs a resume invariant that survives a change of `x` (Q3).
  - (a) is simpler at the boundary. (b) keeps the per-member specs and moves the work into the
    client proof. Q2 decides between them.
- The bridge forwards streams too: `bridge.New`'s spec gains the stream registrations, a D26
  restatement.

**Q2. Watch events stated cluster-wide.** The client's guarantee to its caller must not name the
member, because the stream changes members. Two ways:
- **(i) Lift each member's facts to the shared log.** A member's watch server, whose store is
  `srvKVInvs`-linked to the committed log's model, reports events that are the committed history's
  writes at their revisions.
  - This needs the lifting lemma, about the shared `kvModel`: revision `r` of member `i`'s sealed
    log is revision `r` of the committed history.
  - Then the watch spec can be restated over the shared names (`watchSpecShared`), and every
    member meets the same spec. That is (a).
- **(ii) Keep per-member specs** and carry a translation in the client (b).
- **Recommendation: (i).** It makes the stream boundary as simple as `Invoke`'s, and the lemma is
  the kind of fact the KV results already rest on (`srvKVInvs`). It is the first proof task to
  scope (W2 below), because the client's whole design depends on it.

**Q3. The client's resume invariant across members.**
- With (i), the resume invariant can be stated over the shared history instead of `V.R.γ`'s store:
  the next start revision is one past the last delivered, in the committed history. Each epoch's
  `startOk` and `startRead` happen at whatever member serves it.
- A lagging member, behind the start revision, holds the watch until its applied index catches up
  (etcd's `watchableStore` "unsynced" path). Its notification facts must then cover a start
  revision past its current one. Whether the existing server spec allows that (`startOk` for
  `rev > current + 1`) is to be checked (W2).
- `WatchResume*.lean` and `WatchRecon.lean` change their store, not their structure. This is
  medium-large, the biggest stage.

**Q4. The workload and its check.**
- linkvtxn's workload has deletes and transactions, and watchkv's checker handles puts only.
- **Recommendation:** a separate watch workload in linkv3p, as watchkv's: put-only writers on
  their own prefix (`wk/`), and one watcher from revision 1 through some client. Its check is
  watchkv's `check`, over all the cluster's events. Porcupine's check of linkvtxn's history stays
  as is.
- The two workloads share the revision counter, so the watch check sees gaps in `wk/` revisions.
  Either check "the revisions increase, and every `wk/` put's reply revision has its event"
  instead of "gapless", or run the watch workload alone in its own run of Main.
- To be decided at W0 by what the Go test shows. Running it alone is the simpler proof.

## Stages

### W0. The Go program, measured (no Lean)

- linkv3p gets a watch workload (Q4): writers, a watcher through client 1, the checker.
- A test, `TestWatchFailover`: blackhole the bridge the watch stream uses. Check that the stream
  resumes on another member (the stall at the keepalive close, then events again), with no gap or
  duplicate. Then mend and cut the other two, as `TestFailover` does.
- Measure what etcd's client actually does when the stream is cut: does it resume from the right
  revision on another member? Record any findings in `issues/` (the resume path has had bugs:
  D25's fork fixes F3, F4).
- `go test -race`.

**Done (2026-10-21).** `TestWatchFailover`, in the test file: the workload lives there until W4
settles Q4, so linkv3p's translation and proofs are untouched. One run under `-race`, 49s:
- the puts: 6285, of which 6270 succeeded (the 15 failures are writes in flight at a keepalive
  close);
- the events: 6277, revisions 2 to 6278, with no gap or repeat; every successful put is its event.
- **The stream was cut in each of the three blackholes, not just one.** Each time the events
  stopped for 12s, and the watch resumed on the member blackholed next (grpc's round robin moves
  on). So the resume across members ran three times, from revisions 770, 3135 and 3958.
- No finding for `issues/`: etcd's client resumes from the right revision on another member.
- Q4: only the watch workload ran, so the gapless check held. This supports running it alone
  (Q4's simpler proof). Running it beside linkvtxn's workload would need the weaker check.
- Not tested: a peer-isolated member keeps its stream (no `WithRequireLeader`), so its watch stalls
  until the member is mended, then catches up. That costs liveness, not safety, and the closed
  theorem is about safety.

### W1. The trust boundary (asked of the user; D30)

- `NewStream` over address lists (Q1, with Q2's answer).
- The bridge forwards streams (`bridge.New`'s spec, `forwards`).
- `notes/decisions.md` D30, and ask.

### W2. The server side: a cluster-wide watch spec

- The lifting lemma: a member's sealed revisions are the committed history's.
- `watchSpecShared`: each member's watch server meets it. `etcd_watch_served`'s chain gains the
  shared form.
- `startMember` builds with watch readers (the `_w` variant) and exports the watch registration
  (`memberServed`).
- Check the lagging-member case (Q3).

### W3. The client: the watch over several members

- `WEnv` without a fixed server: the shared names, and the members' addresses.
- `openWatchClient`, `run`'s reconnection and the resume invariants over the shared history.
- `isNewClient_watcher` for `eps` a list.

### W4. linkv3p

- `Main` builds the watch environment from the members (no more `noWatch`). The watch workload's
  proofs follow watchkv's (`Writes`, `WatchFacts`, the checker's).
- The closed theorem covers the watch check (`linkv3p_safe` extended, or a second theorem over the
  same `Main`).
- The gates: `lake build`, the generators' checks, `etc/tcb-report.py --check`, `go test -race`.

## Size and risks

- W3 is the largest: D25's reconnection proof reworked from one store to the shared history. W2's
  lifting lemma is the main unknown, and it decides Q1(a) against (b). If it is out of reach, stop
  and ask: (b) with an existential member per epoch, or the watch at one endpoint (no failover for
  watches, which production clients do not have either).
- Trust base: D30 restates `NewStream`'s axiom and the bridge's spec. No new axiom is expected.

## Out of scope

- Compaction. linkv3p never compacts, so a resumed watch never meets `ErrCompacted`.
- Watch cancellation, and progress notifications beyond what watchkv covers.
- The lease keep-alive stream, which stays at one address.
