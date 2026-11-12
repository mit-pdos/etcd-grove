# Batch 1b (the client's watch API): provability review, round 1

Reviewer: provability (soundness, snippets). Read-only, except this file. I formed my findings from
the specs, the Go code (`.lake/src/client/watch.go`, the fork `a4d2bb17`), the member's handler
(`.lake/src/server/etcdserver/api/v3rpc/watch.go`, `storage/mvcc/watchable_store.go`) and W0's
vocabulary. Only then did I read `batch-1b.md`. Line numbers are those of the files at the time of
review (uncommitted on `specs-only`). The batch builds (oleans dated with the sources), and
`go vet ./specreq/clientv3watch/` passes.

## Verdict

The design is sound and is the right one. Watch responses are persistent `etcdLb`-backed facts,
given by a pure `watchStep`. The wire contract `wireStep` is separate. A position-indexed
consumer `watchChAt` holds it together. I could not find a soundness problem in the idea: rev > 0
resumption has no gap and no duplicate under it, and the rev = 0 weakness is real and honestly
stated. The text has gaps, though:

- three snippets cannot be proved from the specs as written (F1 to F3), each a small fix of the
  statement;
- one snippet's assumption can never hold (F6);
- the internal specs, with the realizations their headers state, cannot prove `run` (F4, F5).

None of these needs a redesign. **Not done: round 2 needed** (first-tier findings break hard
rules: snippets unprovable, a sketch that cannot be carried out).

## First tier

### F1. `ReqWatchCompacted` is unprovable: `watchStep` allows a compaction response with a `closeErr`, and any compaction after an error

`ApiWatch.lean:235-238`. The error case says only `m.closeErr = none → (compaction facts)`. It
does not exclude `closeErr ≠ none ∧ compactRev ≠ 0`. On such a response `Err()` is
`rpctypes.Error(closeErr)` (`watch.go:125-126`), not `ErrCompacted`, so the snippet's panic
`wr.Err() != rpctypes.ErrCompacted` (`ending.go:76`) is not ruled out. `ApiWatch.lean:233-234`
(the `p.ended` branch) says only `isErr ∧ events = [] ∧ canceled`. So a first error carrying a
`closeErr` (`CompactRevision` 0: the loop continues) may be followed by a "compaction" with any
`cr`. Then `wr.CompactRevision <= rev` (`ending.go:79`) is not excluded either.

What Go does:

- `dispatchEvent` builds every compaction response with `closeErr` nil (`watch.go:737-744`).
- Every `closeErr` response has `CompactRevision` 0 (`watch.go:366,381,500`).
- `serveSubstream` returns at the first error it delivers (`watch.go:838-840`), so after an error
  only `sendCloseSubstream`'s single `closeErr` response can follow.

**Fix** (true of the code):

- error case: `m.compactRev ≠ W64 0 → m.closeErr = none`;
- ended case: `m.closeErr ≠ none ∧ m.compactRev = W64 0`.

### F2. `ReqWatchEnds` is unprovable: `WatchResponse.Err` on a `closeErr` response gives no `err ≠ nil`

In `WatchResponse__Err.lean:44` the `some ck` case gives only `callErr err ck`. No law of W0's
`Api.lean` turns `callErr` into `err ≠ nil`: I searched `SpecPlan/Spec/` for one and found none. The canceled-with-reason case (the line
after) does add `⌜err ≠ GoInterface.nil⌝`, so the gap looks like an oversight. Without it,
`ended && wr.Err() == nil` (`ending.go:97`) cannot be ruled out, because a response after an
error is a `closeErr` response.

**Fix**: `| some ck => iprop(⌜err ≠ GoInterface.nil⌝ ∗ callErr err ck)`. This is true:
`rpctypes.Error` of a non-nil error is non-nil, and `closeErrOk e (some k)` already implies
`e ≠ nil`. Alternatively, ask W0 for a law `callErr err k ⊢ ⌜err ≠ nil⌝`.

### F3. `ReqWatchOrder` is unprovable: a progress notification's `P` is not tied to the Go value of the header

`ApiWatch.lean:245-247` gives `∃ P : Nat, m.hdr.revision = W64 P ∧ (∀ c, done = some c → c ≤ P ∧
watchEvents w σ.kv (c+1) P = [])`. The only bound on the header is the first conjunct, `sint.Z
m.hdr.revision ≤ σ.kv.rev`. Take `P ∈ [2^63, 2^64)`: the Go header is then negative, `c ≤ P`
holds, and `watchEvents … (c+1) P` reads the history only up to `σ.kv.rev`
(`KVHist.eventsAt` is `[]` beyond it). So the step is satisfiable whenever the watch has no events
in `(c, σ.kv.rev]`. In that case `wr.Header.Revision < last` (`history.go:142`) is not excluded.
`ReqWatchProgressComplete` survives, because it needs only a non-negative header. The `wireStep`
`-1` case already has the missing conjunct (`ApiWatch.lean:342`).

**Fix**: `sint.Z m.hdr.revision = P`, or add `(P : Int) ≤ σ.kv.rev`. Possibly also a law
`etcdLb γ σ ⊢ ⌜σ.kv.rev < 2^63⌝` (S5), so that clients do not need the owner's invariant to bound
event revisions.

### F4. `run` is unprovable from `wireStep`: fragments are not bound to the response that completes them

The doc comment (`ApiWatch.lean:314-315`) says the next responses after a fragment "are of the
same id". The formal case (`ApiWatch.lean:327-329`) records only `frag := evs`. The response
that completes it can be any non-created, non-canceled response of **any** id (the registration
branch, `:347-350`, uses `st.frag ++ m.events` as that id's events, whatever id the fragments
had). The client does something else (`watch.go:596-603, 642-645`):

- it merges only when `cur.WatchId == pbresp.WatchId`;
- it silently drops a response of another id while a fragment is pending;
- it keeps waiting.

So under `wireStep`, a final response of id B after fragments of id A advances B's registration
with A's events, while the client delivers nothing to B. The tie between registrations and
substreams breaks, and later responses for B cannot be delivered with their facts. The server does
send a response's fragments back to back on one id (`sendLoop`'s `sendFragments`). The contract is
too weak, not the code wrong.

**Fix**:

- `WireSt.frag : Option (Int × List EventM)`;
- a fragment requires `m.watchId` equal to the pending id (if any);
- the response completing a pending fragment has the same id and is not created or canceled;
- drop the odd `st.frag ≠ [] → ∃ id w p, st.reg id = …` conjunct.

Mirror this in `req/go_etcd_io_etcd_server_v3_etcdserver_api_v3rpc.md` (2b).

### F5. The internal sketches cannot carry out `run`: `deliverOk` as described cannot be produced for the `Created` responses `run` dispatches

`WatchInternal.lean:50-52` describes `deliverOk s γ who id m` as "may be delivered … at its
current position (`id = -1`: to every registered substream), as a `watchStep`". `run` calls
`dispatchEvent` on every `Created` (`watch.go:609-612`), and `dispatchEvent.spec` requires
`deliverOk` for the target. That fails in three cases:

1. A successful `Created` of a watch **without** `createdNotify`. `watchStep`'s Created case
   requires `w.createdNotify = true` (`ApiWatch.lean:240`). The substream drops it
   (`watch.go:849-891`).
2. A **resumed** substream's `Created`. Its channel position has `started = true`, and
   `watchStep` requires `p.started = false`.
3. A **refused** create (`WatchId = -1`, `Canceled`). `dispatchEvent.spec`'s target
   expression gives id `-1` (not a progress notification), and `deliverOk` reads `-1` as "every
   registered substream", for which a refused `Created` is no `watchStep`. In Go it is
   `unicastResponse(wr, -1)`, which finds nothing (`watch.go:768-770`; no substream is ever
   registered under `-1`, `addSubstream`).

The predicates are opaque, so the triples are not false. But the realization in the header, the
one the batch must prove, cannot make `run`'s calls.

**Fix**:

- realize `deliverOk` as "what `serveSubstream` may do with it": a `Created` it forwards only when
  `retc` is pending and `createdNotify` (else drops), or a `watchStep` at the substream's position;
- distinguish broadcast from unicast in the argument (`Option Int`, or a flag), so that a unicast
  to an id not in `r.subs` needs nothing.

### F6. `ReqWatchRefused`'s assumption can never hold (the snippet is vacuous, its user unserved)

`ending.go:128-131` assumes "the client's principal was never permitted to read the range at any
state the cluster reached". `State.init` has `auth.enabled = false` (`Model.lean:274-278`), and
`State.permits` is true when auth is off (`Model.lean:778-783`). Every cluster passes through a
state that permits everyone. The event case's admitting state `σa` is any reached state
(`etcdLb γ σa`, `ApiWatch.lean:249`, `:469`), with no lower bound, so the client can never
exclude `σa = σ_init`. The snippet is provable only because its assumption is false. Its user,
`examples/etcd/auth/authkv.go:267-276`, which panics on any event of a refused watch, gets nothing
from the spec.

This is not a mistake in `σa` "any reached state". Go genuinely admits a watch on a lagging member
that has not yet applied `AuthEnable`, or a revocation (the permission check reads the member's
applied auth store). So the guarantee authkv relies on holds only for an up-to-date member (one
member: the apply finishes before `AuthEnable` returns). Uncertain: I did not test a lagging
member.

**Options** (a decision, not a text fix):

- (a) give the event case a lower bound when the cluster has one member, as part of the state
  (`σ.members.length = 1 → Reach σ₀ σa` for an `etcdLb γ σ₀` taken at the call), so that the
  spec stays one spec;
- (b) drop the snippet, and record that the authkv example's check rests on its single member.

The old spec had a one-member gate (`watchCheckOk`), which the batch dropped as a relaxation. That
relaxation lost a user.

## Second tier

- **S1. The registration and substream tie is stated as equality, but it must be a refinement**
  (`WatchInternal.lean:33,40`; `watchGRPCStream__run.lean:21-23`).
  - For `rev = 0`, after the first `Created`, `nextRev = H` (`watch.go:869-871`). A resume
    registers at `WatchPos.init H` (`done = H-1`), while the substream's position stays
    `done = none`, and `initReq.rev = done + 1` is false.
  - A compaction response's header raises `nextRev` to `H_c + 1` (`watch.go:873-878` applies to
    every non-`Created` response). If a resume comes before the buffered compaction is delivered,
    the resumed registration starts at `H_c + 1`, while the substream's position is `ended` with
    the old `done`.

  Both are harmless: the channel learns less, and an ended substream never delivers anything after
  its error. But the tie must say: "the substream's position is the registration's, or weaker
  (`done = none`); an ended substream's later responses are never delivered (any facts)".

- **S2. The resource partition in the header does not match the code.**
  - `wsOwn` (the goroutine's, exclusive) is said to hold `ws.id`. But `run` writes `ws.id` while
    the goroutine runs: `addSubstream` (`watch.go:474`), the `Canceled` branch (`:636`),
    `newWatchClient` (`:948`, after the join). `addSubstream.spec` takes only `wgsRun`.
  - `run` reads `ws.initReq.rev` for `toPB` (`:584,617,687`) while the goroutine holds `wsOwn`.
    This is race-free: the goroutine writes `rev` only after a `recvc` message, which comes only
    after the `Created`.

  **Fix**: put `id` in `wgsRun`'s per-substream part. Split `rev` by fraction: `run`'s half
  while unregistered, handed to the goroutine with the `Created` over `recvc`. Or say how the
  sketch does it.

- **S3. `rev = 0` watches could promise more, and Go's own comment is the user**
  (`watch.go:860-868`: `wch := m1.Watch("a"); m2.Put("a","b"); <-wch`).
  - Whatever the reconnects, the first event's `lo ≤ H + 1`, where `H` is the `Created` header,
    which is at most the cluster's revision when `Watch` returns. Without a resume `lo = R + 1 ≤
    H + 1`; with one, `lo = H`; a resume before `Created` re-registers before `Watch` returns.
  - So "a write committed after `Watch` returns is delivered" holds in Go, but the spec gives a
    `rev = 0` watch no bound at all (`WatchPos.init 0`: `none`, `∃ lo` unconstrained,
    `ApiWatch.lean:250`).
  - Stating it needs `Watch`'s post to carry an `etcdLb γ σ₀` bound into the position. It also
    needs `wireStep`'s registration at start `0` to bound its first event by the `Created` header.

  For the completeness reviewer: the author's "no user relies on `rev = 0` completeness" is about
  the lower end, not this one.

- **S4. `watchReqOwn`'s create carries the normalized range** (`OpM.watchReq` turns an empty key
  into `"\x00"`, `ApiWatch.lean:129`). But `toPB` sends `Key: []byte(wr.key)`, which is `""`
  (`watch.go:1084`). Say in the slot (and in `req/…etcdserverpb.md`) that `watchReqOwn p dq
  (.create w s)` means a message whose key is `""` or `w.range.key` when the latter is `"\x00"`.
  Otherwise 3h's realization cannot satisfy `watchRequest.toPB.spec` for an empty key.

- **S5. A missing bound law.**
  - Every client comparison of revisions (events' `ModRevision`, `CompactRevision`) needs
    `σ.kv.rev < 2^63` (and `compacted ≤ rev`) at the response's `σ`. Today that comes only from
    the owner's invariant (`etcdState_revFits` with `etcdLb_reach`).
  - A W0 law `etcdLb γ σ ⊢ ⌜σ.kv.rev < 2^63⌝` would let a watch consumer without that
    invariant (Kubernetes' watcher) compare revisions.
  - The snippets state the owner's invariant, so they are fine.

- **S6. `watcher__Watch.lean`'s margin** reads "the code also never delivers an event below the
  member's revision at the creation minus one". With the rev = 0 bug below, Go delivers events
  of `H` itself, and of nothing below `min(R+1, H)`. Reword it, or drop it in favour of S3.

## Go bug (b): the `rev = 0` resume, checked

The author's finding 1 is **real, and part (a) is deterministic and testable**. The steps:

1. The member registers the watch at its current revision `R` (`minRev = R + 1`,
   `watchable_store.go:141-147`).
2. It then reads the header revision `H = watchStream.Rev() ≥ R`, after the registration
   (`v3rpc/watch.go:342,360-361`).
3. The client sets `nextRev = H` on the first `Created` (`watch.go:869-871`).
4. A reconnect before any event resumes with `StartRevision = H`. `H ≤ currentRev` makes the
   resumed watcher unsynced, and `syncWatchers` sends revision `H`'s events.
5. With no write between the registration and the header read (`H = R`), those events precede
   the watch.

This contradicts `Watcher.Watch`'s documentation: "the returned channel will return watch events
that happen after the server receives the watch request" (`watch.go:68-69`).

It is reachable the way users watch "from now": put a key, watch it, then a transient disconnect.
A Go test can show it, in the style of `issues/etcd-watch-resume-below-start-revision/`'s test:

1. one member behind a bridge;
2. `Put(k)`, then `Watch(ctx, k)` (wait until `Watch` returns, or use `WithCreatedNotify`);
3. drop the bridge's connections;
4. expect no event, and observe the put at revision `H`.

No race is needed. Parts (b) and (c) (a skip of `(R, H)` when two or more writes land between the
registration and the header read, and a progress in that window) are real but racy. A test would
need a failpoint between `Watch` and `Rev()`. The batch's spec is sound against all three
(`WatchPos.init 0` is `none`, and progress at `none` stays `none`).

**Classification**: an `issues/` entry with that test, not `nonissues/` as the report suggests.
`blocks-proof: no` (the spec sidesteps it). I did not search upstream; check etcd-io/etcd for a
known report. No file exists under `issues/` or `nonissues/` on this branch.

## (a)-(e) in brief

- **(a) Persistent facts instead of a read update: sound, and enough** once F1 and F3 are fixed.
  - Every conjunct of `watchStep` is about the history at a reached `σ`.
  - Responses are combined through `etcdLb_ord`, with the clients' pure lemma that `Reach` keeps
    the history a prefix and `watchEvents` of revisions `≤ σ.kv.rev` stable.
  - "No events in `(r1, r2]`" is the progress case at `done = some r1`.
  - "Exactly these events" is `List.Forall₂ … (watchEvents w σ.kv lo c')` with `lo = done + 1`,
    and whole revisions (mvcc's `eventBatch.add` cuts at revision boundaries).
- **(b) Resumption for `rev > 0`: no gap and no duplicate.**
  - `nextRev` is updated at receipt (`watch.go:873-885`), not at delivery. The goroutines are
    joined before the resume (`newWatchClient`, `:946`), and the old `serveWatchClient` has
    exited (its error came after its last `respc` send).
  - So the resumed create's start is `done + 1` of everything received, and buffered responses
    keep their facts at the positions they will be delivered at.
  - The fork's server checks `rev < w.startRev` (`watchable_store.go:539`), so a progress is
    never below `done`.
  - For `rev = 0`: see above.
- **(c) The pieces.**
  - Fragments: F4.
  - Progress, broadcast, and RequestProgress on a shared stream: sound, given 2b's contract that
    the fork's `etcd-watch-progress-before-created` fix makes provable, and the fork's
    `etcd-watch-progress-closed-substream` fix that removes canceled substreams (`watch.go:633`).
  - Compaction: F1.
  - `Close` (post `True`) and channel close (`ok = false` keeps the position): fine.
  - The select-receive law `watchChAt_recvAu` matches Perennial's `blockingClausePre`
    (`Chan.lean:198-204`), used under `wp_select_blocking`'s `[∧list]`, so the consumer is kept
    on the other branch. The `£ 1 ∗ £ 1` is the usual idiom cost (as in `Bag.lean:74`).
- **(d) The 28 internal specs cannot prove the 10 client-facing ones as their realizations stand:**
  F4, F5, S1, S2. With those repaired, I see no further obstacle. `watcher.Watch`'s loop,
  `RequestProgress` (by Löb induction), `Close`, `closeStream` and the teardown's counts are all
  consistent with the code.
- **(e) Snippets.** Provable (sketch: `watchChAt_recv` per iteration, `watchRespAt_fields` and
  `eventOwn_unfold` for fields, `WatchResponse.Err.spec`, `watchStep`'s cases, `etcdLb_ord` and the
  pure history lemmas, the owner's invariant for "owned" and the 2^63 bounds): `ReqWatchFromGet`,
  `ReqWatchWaitDelete`, `ReqWatchRevisionWhole`, `ReqWatchFilter`, `ReqWatchHistory`,
  `ReqWatchProgressComplete`, `ReqRequestProgress`, `ReqWatchCreatedFirst`, `ReqWatcherClose`,
  `ReqWatchSelect`, `ReqWatchRewrite`, `ReqWatchPrevKV`. Not provable: `ReqWatchCompacted` (F1),
  `ReqWatchEnds` (F2), `ReqWatchOrder` (F3). Vacuous: `ReqWatchRefused` (F6).
  - `ReqWatchFromGet` and `ReqWatchHistory` also need the pure fact that a put event at revision
    `r` carries a record with `modRev = r`. The clients prove it from `Step`, and it is listed
    nowhere.

## What is good

- The client-facing contract is small and in the clients' terms: one exclusive consumer indexed by
  a pure position, one pure step relation, `etcdLb` for states. There is no ghost name, cursor or
  `Q`, and no implementation vocabulary. The `Watcher` contract fills W0's slot and is realized
  once for `*watcher` (interface bundle per PRINCIPLES).
- The relaxations are right and checked against the code:
  - any range (empty key normalized);
  - any start revision;
  - any context;
  - filters, `prevKV` (with the compaction caveat of `nonissues/etcd-watch-prevkv-nil-after-compaction.md`);
  - fragments, auth in every mode;
  - no `watchSizeOk` and no duplicate-key premise.
- The header ownership `hdrDq` (read-only without events, full with) matches both broadcast
  sharing and `serveSubstream`'s read of `wr.Header.Revision` after forwarding a `Created`
  (`watch.go:858-870`). Consumers that write responses (Election.Observe, the namespace wrapper)
  are served.
- The rev > 0 resumption design is exactly right, and the `rev = 0` analysis is honest and
  matches the code.

## Targets ranked by need of revision

1. `ApiWatch.lean`: `watchStep`'s error, ended and progress cases (F1, F3); `wireStep`'s fragments
   (F4); slot doc for `watchReqOwn` (S4).
2. `WatchInternal.lean` with `watchGRPCStream__{run,dispatchEvent,unicastResponse}.lean`:
   `deliverOk`'s meaning and target (F5), the tie (S1), the partition (S2).
3. `examples/specreq/clientv3watch/ending.go` `ReqWatchRefused` (F6, a decision).
4. `WatchResponse__Err.lean` (F2, one conjunct).
5. `watcher__Watch.lean`: the margin text (S6); `rev = 0` strength (S3, optional).
6. The rest (`watcher__{RequestProgress,Close,closeStream,newWatcherGRPCStream}`,
   `Client__{Watch,RequestProgress}`, `NewWatcher`, `NewWatchFromWatchClient`,
   `WatchResponse__IsProgressNotify`, `ensureWatchHeader`, the internal helpers): no findings.
