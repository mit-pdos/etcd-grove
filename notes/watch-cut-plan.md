# Plan: watches across a cut (linkv3p)

Status: W0 done, the lifting lemma scoped, D30 approved (2026-10-21, branch `watch-cut`); W1 (carrying D30 out) and W2 next. Follows `notes/read-retry-plan.md` (D29),
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

## The lifting lemma, scoped (2026-10-21)

**The lemma is in reach and small.** Its pieces exist:
- A watch event's log is `evLog`: sealed and certified (`certOk`) at the member's store.
- `kv_cert_read` (`KVLemmas.lean`): a certified log has at most two revisions or is
  `kvModel γk A` of a committed prefix `A` (`srvRLogLb`).
- `srvRLogLb_prefix`: two committed prefixes are comparable, at the raft names all members share.
- `kvRaftOf_prefix`: the model grows with the raft log.
- The members' KV names agree on everything `kvModel` reads (`c0`, `ch0`, `log0`;
  `putget3/Alloc.lean`). Only the certificate map `cok` is per member.
- So two members' certified logs are in prefix order, and a revision's events agree across members.
  About a hundred lines.

**But "every member meets one shared spec" (Q1(a)) does not work.** The watch stream's spec
(`watchDn`) is about the member's own mvcc ghost state: watcher registrations, the notified log
(`notifiedLb`), the released revisions (`relLb`), the channel's coverage (`covFact`), and the header
member id. The client's resume proof uses all of it. None of it can be stated cluster-wide.
- Q1 is therefore (b): `NewStream` over `addrs` returns a stream to **some** member of the list,
  with that member's registered spec. This is also what gRPC does: a stream lives on one
  subconnection.
- The lemma is what lets the client join epochs served by different members into one history (Q2
  (i), used in W3, not at the boundary).

**The resume at another member needs a server-side change (W2).**
- A resumed create carries `startRead γ sr rev` at the member that receives it: a member-local lower
  bound (`idxCert`, `notifiedLb` or `relLb` of that member's store). For a watch with a promised
  completeness (`cplCond`: `sr = true`) the client must provide it.
- After a failover the client knows only the previous member's facts. A lagging member has not
  reached `rev`, so no member-local bound exists.
- etcd's server guards this case itself. `progressIfSync` sends no progress notification to a
  watcher whose start revision is above the store's (`if rev < w.startRev { return false }`),
  upstream since `973847aa24` and in the pinned code. So a lagging member never reports progress
  below the resumed start.
- The plan for W2: give `startRead` a cluster-wide case, "a certified log of some member reaches
  `rev`" (the lemma). Then re-prove mvcc's guarantee (`covFact`'s `sr = true → lo ≤ rev + 1`) from
  the guard rather than from `startRead_le`. If the guard alone suffices, `startRead` may be
  dropped altogether. Size: medium, in mvcc's watch proofs.

**A side finding: the examples' Go tests did not run the verified watch client.**
- Every example's `go.mod` pinned the etcd fork at `8a24be2a3`. That is before the four
  watch-resume fixes F1–F4 that the translation's pin `b3c29bc17` carries.
- `b3c29bc17` is pushed: it is the fork's branch `watch-resume-fixes`. Only the `go.mod` files had
  not been bumped.
- W0's first run therefore exercised the unfixed resume path. It passed, since no transient error
  hit a closing or canceled substream.
- **Fixed (2026-10-21):** every example's `go.mod` replaces etcd's modules by
  `v3.0.0-20261020173053-b3c29bc17f26`. `etc/goose.py --check` shows every translation unchanged.
- With the server's guard, the F3 scenario (`issues/etcd-watch-resume-below-start-revision.md`)
  looks unreachable against etcd's own server: its reproduction uses a fake server. To check, and
  to note in the issue.

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

- `NewStream` over address lists: a stream at some member of the list, with that member's spec
  (Q1 (b), per the scoping).
- The bridge forwards streams (`bridge.New`'s spec, `forwards`).
- `notes/decisions.md` D30, and ask. **Approved 2026-10-21.**
- **Done (2026-10-21):** D30's "Carried out". `NewStream` over a list, each address with its own
  content and spec, the stream at some address of the list; the bridge and `forwards` forward
  streams (`isGrpcStream_forwards`). No axiom added.

### W2. The server side: a cluster-wide watch spec

- The lifting lemma: a member's sealed revisions are the committed history's.
- `watchSpecShared`: each member's watch server meets it. `etcd_watch_served`'s chain gains the
  shared form.
- `startMember` builds with watch readers (the `_w` variant) and exports the watch registration
  (`memberServed`).
- Check the lagging-member case (Q3).

**W2a done (2026-10-21): the resume needs nothing of the member it reaches.**
- mvcc no longer takes the client's `startRead`. A watcher's ghost bit `now` (was `sr`, chosen by
  the client) is set by the server: a watch from now (start revision `0`). Its first revision is
  then within the notified log (`srBelow`, unchanged in form).
- Any other watcher starts at its start revision, and `progressIfSync`'s guard (`rev < w.startRev`:
  no progress notification) bounds it: the loop records, per watcher, `now ∨ lo ≤ rev`.
- So a response's coverage bound is unconditional (`covFact`, `covEntry`: `lo ≤ rev + 1`).
  `startRead`, `startRead_le`, `wlogQ_lb_valid`, `WatchParams.SR` and `watch`'s `sr` binder are
  gone, and so are the client's `startOk_read`, `startRead_of_etcdRead` and the `γw.sr = c.sr`
  links. `startOk` keeps only its client half: etcd had reached the revision before the start.
- The lagging-member case (Q3) is covered by the same guard.
- Specs of verified functions changed: `watchableStore.watch` and `watchStream.Watch` lose a premise
  (stronger). Trust base unchanged (530 axioms, 2 sorries).

**W2b done: the lifting lemma.** `kv_cert_cmp` and `kv_cert_rev` (`etcdserver/KVCertCmp.lean`):
two members' certified logs of more than two revisions are in prefix order, so they agree at every
revision both have. Not yet used: W3 imports it.

**W2c done: linkv3p's members serve the watch stream.**
- `startMember` keeps NewServer's 64 watchable-store readers (`grpcCfgOk_of_started_w'`, no longer
  through putget3's `memberUp`) and one request-path reader, which make one watch run slot. Run
  slots are a pool returned at a run's end (`grpc.serveStream`), so reconnects do not use them up.
- `etcd_watch_served_chain` serves `/etcdserverpb.Watch/Watch` at the client address.
  `memberServed` exports the member's watch server and the registration, which `Main` drops until
  W4.
- **The closed theorem's step bound drops** from `n + 2 ≤ 2^31` to `n + 2 ≤ 2^29`, as watchkv's:
  a watch run slot needs `threadBound ≤ actualMaxReaders` (Go's `RWMutex` reader bound, just under
  `2^30`). `linkv3p_safe` now covers executions of up to `2^29 - 2` steps.
- linkv3p's trust base gains 8 axioms, all already in watchkv's (`grpc.serveStream`, the server
  stream's `Context`/`Recv`/`Send`, ...): 480 entries. The global baseline is unchanged (530
  axioms, 2 sorries).

### W3. The client: the watch over several members

**The design (2026-10-22, from reading the client's proof).**
- The client's contract (`isEtcdRangeWatcher`, `watchRespOk`) is stated over an `EtcdModel`
  (`V.EM`), today `etcdModelOfServer V.R.E`, one member's. Its facts (an event's state, a step, a
  reached revision) all come from certified logs (`evLog`, `srvStep`'s `certOk`).
- `EtcdModel`'s laws are plain entailments (`⊢`), so a cluster model cannot open the certificates'
  invariant inside them, and `kv_cert_cmp` is a fancy update. But "the KV model of a committed
  raft prefix" (`srvRLogLb γ A ∗ ⌜kvModel γk A = log⌝`) is persistent, and two such logs compare
  by a plain entailment (`srvRLogLb_prefix`, `kvRaftOf_prefix`).
- **W3a: the history model** `etcdModelOfHistory γ γk`. Its logs are the KV models of committed
  raft prefixes, carrying their well-formedness. It names no member. Its laws are
  `ClientModel.lean`'s, with the comparison of two logs replaced. A member's certified facts become
  its facts by `kv_cert_read`, an update, which the client's proof makes inside its WPs.
  `etcdRevToken` is `False` there: no watch result produces one.
- **W3b: the watch client over a family of members.** `WEnv` keeps one `EM` and gains the members
  (their watch servers and addresses), with premises that each member's facts convert into `EM`'s
  (the identity for `etcdModelOfServer` at one member, so watchkv's and the cache's statements stay
  as they are). Each epoch's stream is at some member: the run's state names it, and the per-epoch
  facts (`regFacts`, `cur2Ok`, the coverage) are that member's. The resume invariants are already
  `EM`-level (`startOk`, `resumeOk`), so they cross epochs unchanged.
- **W3a done (2026-10-22):** `v3rpc.etcdModelOfHistory γ γk` (`api/v3rpc/HistoryModel.lean`). Its
  laws are `ClientModel`'s over `histLog` (`histLog_two` in place of `srvLog_two`). A member's
  facts convert by `histLog_of_cert`, `histStep_of_srv` and `histReached_of_cert`, at a member whose
  names agree (`memberOf`). Not yet used: W3b.
- **W3b-1 done (2026-10-22): the contract's model a field.**
  - `WEnv` gains `WM`, the watch contract's model, and `WL`, the watcher's logs as `WM` sees them.
    `V.EM` stays the server's (the KV calls').
  - `watchLaws V`, part of `watchConnFacts` and `watchAddrFacts`: reached revisions, states and
    steps of `WM` at a `WL` log (plain entailments), and a watched log of the server becomes a `WL`
    log by an update. `watchLaws_srv` proves it for a client of one server (`srvWEnv`:
    `etcdModelOfServer R.E`, `srvWL R`).
  - The six places the client made the model's facts from the server's (`ev_ok`,
    `stepCert_of_watch`, `cmpl_prog`, and those through `srvStep_of_watch` and
    `etcdReached_of_certOk`) take `□ V.WL L ∗ watchLaws V`. Their callers convert the log once,
    before the □-quantified contract: `dispatch_content`, `prog_cmpl` and the `cmpl_events`
    closures. `cmpl_step`, `prog_cmpl`, `reg_pre`'s and `bcast_pre`'s completeness steps are now
    updates at `⊤`.
  - The KV-and-watch compositions (`isEtcdClient_of_*`, the cache's end-to-end results,
    `queue_end_to_end_client`) take `hWM : V.WM = etcdModelOfServer V.R.E`. Every concrete
    environment gives it by `rfl`.
  - Statements of the closed theorems unchanged; trust base unchanged.
- **W3b-2, the design (2026-10-22): epochs at members.**
  - `WEnv` gains its members, `mem : Nat → GoString × WSrv` and `nm`; `V.atIdx i` is `V` at member
    `i` (its `addr` and `R`). A predicate that reads neither `R` nor `addr` is the same at every
    member by definition. Those are all of `run`'s but a registration's facts (`regFacts`,
    `cursorOk`, `cur2Ok`: a substream's `.reg` phase), the epochs' responses (`respcE`) and the
    member facts.
  - `watchConnFacts` holds each member's facts (`watchMemberFacts (V.atIdx i)`: its token pool,
    small logs, no duplicate keys, store names, its logs' conversion) and the stream registered at
    every member's address (`isGrpcStreams`, D30); the laws of `WM` read no member.
  - `EpInfo` records each epoch's member, and `respcE` reads an epoch's responses at it.
  - `run`'s loop invariant quantifies the epoch's environment, named `V` in the loop's body, so the
    body's proof is unchanged: `V = V0.atIdx i` for the stream's member `i` (`newWatchClient`
    returns a stream at some member, `NewStream`'s axiom, D30). At a reconnection every substream
    is queued (`RunSt.reconnect`), whose state reads no member, so it carries to the next epoch's
    environment.
- **W3b-2 done (2026-10-22): epochs at members.**
  - The design above, carried out. `WEnv.atIdx` is a `def`, so `V0.atIdx i` stays one term. `rfl`
    lemmas show what reads no member: `wsIs`, `stopBody`, `recvElem`, `reqP`, `closingP`,
    `respcE`. `bufE`, which is recursive, and through it `wsRun`, `resumeBody`, `lifeSt` and
    `wsLife` need induction and rewriting.
  - `wsElem_recon_at`: a reconnected substream at any member. `isWGS_atIdx`: the gRPC watch
    stream's facts at any member (`watchConnFacts_atIdx`).
  - `watchClient.Watch` over a list (`isGrpcStreams`). `openWatchClient`, `newWatchClient` and
    `serveWatchClient` give or take the stream's member; `EpInfo`, `prodBack` and `epochSt`
    record it; `respcE` reads each epoch's responses at its member.
  - `run`: the base environment is `V0`. The loop's invariant holds the epoch's member `mi`,
    `runCore (V0.atIdx mi) …`, the stream at `(V0.atIdx mi).R`, and `isWGS (V0.atIdx mi)`. The body
    generalizes `V0.atIdx mi` to `V` and re-derives the member's facts, so its proof text is
    unchanged. The reconnection switches the same way to the new stream's member `mi2`, and the
    teardown to the last epoch's. `closeStream` stays at `V0`: the watcher's lock invariant is
    stated there.
  - A client of one endpoint gives its one member (`watchConnFacts_of_addr`,
    `isNewClient_watcher`: `V.mem = fun _ => (V.addr, V.R)`, `V.nm = 1`); every concrete
    environment is `srvWEnv`. Closed theorems unchanged; trust base unchanged.
- **W3c (folded into W3b-2):** the watch stub over a list (`watchClient.Watch` at `addrs`), `openWatchClient`, and
  `isNewClient_watcher` for `eps` a list.

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
