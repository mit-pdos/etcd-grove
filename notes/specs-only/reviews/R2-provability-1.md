# R2 (raft core) — provability review, round 1

Reviewer: provability. Commit reviewed: `627da340d6` (the R2 files are unchanged since; R1's round-2
repairs, `575e238bd7`, landed during the review and are taken into account where they touch R2:
`RawNode.Ready/HasReady/Advance` now use `rawNodeAt`, and `req/go_etcd_io_raft_v3.md` item 8 asks for
a client-chosen view point after a snapshot). Go: `.lake/src/raft/{raft,rawnode,node,logger}.go`.
I read `batch-R2.md` only after writing the findings below; where the author already raised a point,
I say so.

## Summary

The design is right in its main lines, and I could not break it. `raft.Step` takes only the
message's provenance. Most of what a single per-message spec would need can be carried by an
invariant inside `raftCore`. I checked the R1 obligations the brief singled out: (b) items 8-10, and
(c) the receipt design. Both hold, with the invariant stated below. The R1 finding (d) is correct,
and R1 has since adopted the fix.

What fails is the layer under `raft.Step`, and several snippets:

- the 15 helpers left out were all proved in `specs-ref`;
- the specs of the helpers that do exist relate nothing to their result, so the handlers' proof
  sketches cannot be built from them;
- the term bound has no statement to rest on yet;
- three snippets are unprovable for want of a law.

## (a) Can `raft.Step` with only provenance be proved? The invariant `raftCore` must carry

I tried to break it by message type and state. Each candidate failure below either turned out
unreachable, or is covered by a fact that `msgSent`'s realization can carry. The invariant
`raftCore r γ id ρ` (with its share of the cluster invariant at `γ.ns`) needs at least:

1. **Per-term leader logs** (ghost, monotone): the entries the leader of term `T` appended, including
   ones lost in a crash before they were written (send-before-write, R1's `readyCheck`). Each
   `MsgApp`/`MsgHeartbeat`/`MsgSnap`/`MsgTimeoutNow` fact is stated against this log
   (`msgSent_leaderOf`). Election safety: `leaderOf` comes from a quorum of durable votes, one per
   voter and term.
2. **The node's log and commit**: its commit index is a prefix of the committed log; log matching
   against every term log; leader completeness (by induction on terms). The leader's self `Match`
   is set to `lastIndex` at `becomeLeader` (`raft.go:821`). It is durable-backed because every entry
   is in a batch at or before the one carrying the self-vote, and that self-vote is acknowledged
   only at `Advance` (`StepSrc.ack`).
3. **Responses**: a `MsgAppResp`/`MsgVoteResp` fact holds at the sender's durable state; it is
   minted at `readyEnter` (`msgsAfterAppend`). An append acknowledgement at term `T` with index `i`
   means one of two things. Either the sender's log matches the term-`T` log up to `i`. Or the
   sender installed a replaced snapshot (`msgSent_replaceSnap`, with R1 round 2's `s'.term ≤
   m.term`), and the term-`T` leader had already left `T` when the snapshot was taken from its
   delivered log, so the response is stale where it lands. I checked the dangerous orders:
   - a follower's `Match` above its log after a restore: `handleHeartbeat`'s `commitTo` cannot
     overrun, because the heartbeat's commit is at most the leader's term-`T` commit, which is at
     most the agreement point;
   - a delayed term-`T` `MsgApp` after a restore: `a.prev.index < committed` returns before
     `maybeAppend` (`raft.go:1811`), and a later `prev` mismatches and is rejected.

   No panic, no wrong `MaybeUpdate`. This is item 10's realization; write it down in `ApiCore.lean`.
4. **Reads**: the realization in `ApiCore.lean:60-62` says the read updates are "fired when a quorum
   ... acknowledges a heartbeat". That is wrong, see finding 2.3. What works is the old proof's
   scheme (`specs-ref/notes/raft-readindex-spec.md` §4.1):
   - at the first `raft.Step` of the local `MsgReadIndex`, put the persistent update (`readCtx`) into
     raft's invariant;
   - fire it at every ghost commit from then on;
   - `readState γ c i` then needs only `L(deposit) ≤ i ≤ L(now)`, which the heartbeat confirmation
     gives through `L(registration) = i`.

   I checked a duplicate `MsgReadIndex` under `γ.dup`, whose stale acknowledgements confirm the
   later registration (`readOnly.recvAck` keys by context). It is sound under this scheme, because
   the leader's commit only grows.
5. **Configurations**: see (b).
6. **Term and index bounds**: see (c).

Other checks that pass:

- **A forwarded `MsgTransferLeader`** is stamped with the term (`send`, `raft.go:543`). It is
  forwarded again only by a follower of the same term with a leader set, and `send` panics on a
  non-zero term for that type (`raft.go:536`). The receiver led the term, and after stepping down it
  keeps `lead = None` at that term (`becomeFollower(r.Term, None)`; a restart does the same). So no
  second forward. This is the fact `stepFollower`'s sketch claims.
- **A local `MsgTransferLeader`/`MsgSnapStatus`/`MsgUnreachable` with any `From`** changes only
  progress. The transferee must have a progress entry (`raft.go:1388-1391`, `:1656`).
- **The `hup` guard survives the pre-vote round**: the pre-candidate's commit does not move without a
  leader message, which makes it a follower. A client `ApplyConfChange` in between can only be a
  no-op: any entry above raft's applied index was already in `(applied, committed]` at `hup`.
  `stepCandidate`'s claim holds.
- **The `StepSrc.ack` acknowledgements at a newer term** are ignored (stale), and a stale storage
  acknowledgement still runs `appliedSnap` (`raft.go:1197`). `ackPost` covers both.

Verdict on (a): provable, provided `raftCore`'s realization states items 1-4 and the configuration
invariant below. It is not provable with the layer below it as specified (findings 1.1, 1.2).

## (b) R1's items 8-10: a configuration point above the commit, or past the node's own log

The author's doubt (`batch-R2.md`, 8a) is that "it can only win with a log at least as up to date as
a quorum" is not enough by itself. It is not. The argument that closes it:

**The invariant**:

- **(V1)** the node's view `⟨a, m⟩` (R1's `nodeConf`) is `confAt γ a m`, with `a` at least raft's
  applied index. This holds at `newRaft`, at `applyConfChange`, and after `appliedSnap` (where the
  view may move back, `a' ≥ s.index = applied`).
- **(V2)** the "one pending change" invariant. If a node's log holds a conf entry `g`, and the log of
  the leader that proposed `g` held a conf entry `f` before it, then the node's commit is at least
  `f`. This is because the leader proposed `g` only after applying `f` (`pendingConfIndex`), so the
  `MsgApp` carrying `g` carried a commit of at least `f`. It survives restarts because the commit is
  written with the entries (R1's `Durable.wcommit`, `StorageHolds`' `wcommit ≤ σ.hs.commit`).
- **(V3)** consequence of V1 and V2 with `hup`'s guard: when a leader first commits an index, its view
  is `C_q`, with `q` at least the last conf entry before the last conf entry in its log, and below
  the commit.

**The argument.** Take a candidate whose view is `C_a` and whose log ends below `a`. Let `f₀` be the
last conf entry at or below `a`, and `f₁` the first conf entry after `a`.

- The index `f₁` (or, if there is none, the last committed index) was first committed under a view
  in `[f₀, f₁)`. That view is `C_a` itself.
- So every `C_a` quorum holds that entry.
- The usual lemma (a candidate as up to date as a holder of a committed entry holds it) then makes
  the candidate hold an index above its log's end. Contradiction: it cannot win.

The same chain covers a node lagging several configurations behind: its next conf entry, if held,
forces its commit past the previous one by V2, and then `hup` refuses. The joint and auto-leave
cases are adjacent pairs.

So item 8 can be met without reverting to `a ≤ commit`, and so can item 8b (a snapshot's
configuration ahead of its index, the same shape after `appliedSnap`). The fault is that none of
V1-V3 is written in `ApiCore.lean`'s realization (finding 2.2). Item 9 holds as the author says.
Item 10: see (a) item 3.

## (c) Terms and indices from time receipts

The design is sound in principle:

- receipts are global to the execution, across crash generations (`CrashAdequacy.lean:10-13`);
- every Go instruction can give `⧗ 1` (`Lifting.lean:2097`, `wp_GoInstruction_receipt`), so
  `campaign` and `appendEntry`'s per-entry loop can each take one;
- a cluster invariant holding `⧗ maxTerm` bounds every term below `receiptBound`;
- terms from messages and storage are bounded by the same invariant: `cluster_alloc` starts every
  durable state at `Durable.init`, so no term predates the execution;
- the bootstrap's term 1 needs an offset of one (`maxTerm ≤ receipts + 1`).

It is also necessary: at `r.Term = 2^64 - 1`, `becomeCandidate` wraps the term to 0 (`raft.go:926`),
and `send` then panics on the `MsgVote` (`raft.go:532`). A pre-vote at `r.Term + 1` does the same
(`raft.go:1055`). So it is dischargeable, but only once some statement carries the bound: see
finding 1.3.

## (d) The `Ready` phases; R1's `RawNode.Ready.spec`

R2's claim is confirmed. R1's round-1 `RawNode.Ready.spec` took `rawNode ∗ nodeDriver` and gave
`readyGot`, whose `readyEnter` returns `nodeDriver` before `Advance`. A second `Ready` then reaches
`rawnode.go:412` ("two accepted Ready structs") whenever the first batch queued an acknowledgement.
R1 round 2 now takes `rawNodeAt … k false` and gives `… (k+1) true`, which is sound.

`readyWithoutAccept` and `acceptReady` are sound against the code. `readyFresh` holds `rd`'s slices,
and `rd.Messages` aliases `r.msgs` (`rawnode.go:145`, `:181`): a later `r.msgs = append`
(`raft.go:598`) overwrites `rd`'s tail. This is harmless only because no `readyKept` `Ready` with
messages is ever made fresh again (see 2.5).

R1's new `HasReady` (`false` gives `readyFresh` back) is sound, but only through a monotonicity fact
the realization must state. Between two `acceptReady`s:

- `msgs`, `msgsAfterAppend`, `readStates` and the next entries only grow;
- the hard state, once different, stays different (the term only grows; a vote is reset only with a
  new term; the commit only grows);
- the soft state can return to the previous one only through a message from the term's leader
  (`MsgApp`/`MsgHeartbeat`/`MsgSnap`), each of which queues a response (`raft.go:1806-1873`).

So `HasReady() = false` after a non-empty `rd` is impossible. The snippet header's "still the current
one but for its soft state" (`ready.go:33`) is therefore wrong.

## (e) The 15 helpers left out

The author left out `raft.send`, `sendHeartbeat`, `bcastHeartbeatWithCtx`, `appliedTo`, `appliedSnap`,
`reset`, `becomeCandidate`, `becomePreCandidate`, `becomeLeader`, `campaign`, `poll`,
`switchToConfig`, `loadState`, `responseToReadIndexReq` and `sendMsgReadIndexResponse`
(`batch-R2.md`, "Left out"; open question 3). The stated reason is that their specs "need a guard
only the caller's check establishes".

That is not a reason to leave them out. All 15 have specs and complete proofs in `specs-ref`
(`Proof/go_etcd_io/raft/v3/<fn>.lean`, 0 `sorry` each, 61-589 lines). Each is called from a spec in
this batch, and each is cited by name in some proof sketch. Each can get a spec whose premise names
the caller's check. They need one internal, unsealed predicate the clients never see, for example
`raftOpen r γ id σ`: the struct with its protocol invariant opened, where `σ` holds what the helpers
touch (term, vote, lead, role, votes, `pendingConfIndex`, the applied index). It comes with
`raftCore_open`/`raftCore_close` laws, the close law taking the invariant's conditions. The premises
are the callers' checks:

| Helper | Premise (the caller's check) | Post |
|---|---|---|
| `becomeCandidate`/`becomePreCandidate` | `role ≠ Leader` (`raft.go:923`, `:938`) and a campaign guard produced by `hup`'s checks | for `becomeCandidate`: term + 1 with a receipt, vote `id` |
| `campaign` | the same guard | |
| `becomeLeader` | `role ≠ Follower` and `leaderOf γ term id` | |
| `poll` | the vote's provenance (a `msgSent` response, or the acknowledged self-vote) | the tally, and `VoteWon → leaderOf` |
| `send` | an internal `msgJust r γ id m` (the message's protocol fact at the current state), `m.term` as `send` requires (`raft.go:530-545`), `m.to ≠ id` unless a response | |
| `appliedTo` | `index ≤` the delivered log, with `ackPre`'s resources | |
| `appliedSnap` | `ackPre`'s resources (snapshot arm) | `ackPost`'s snapshot arm |
| `switchToConfig` | R4's tracker at a valid membership equal to the view's | |
| `loadState` | `committed ≤ hs.commit ≤ lastIndex` (Go panics otherwise) | |
| `responseToReadIndexReq`/`sendMsgReadIndexResponse` | a leader with an entry of its term committed, and the request's provenance | |

## (f) Snippets

| Snippet | Provable? |
|---|---|
| `step.go`: `ReqStepReceived`, `ReqStepPropose`, `ReqStepRead`, `ReqStepReports` | Yes, from `raft.Step.spec` (the `err` disjunct gives the `MsgProp` case), given the term bound (1.3) |
| `step.go`: `ReqTick` | Yes, via `raftCore_peek` (`r.tick` is one of the two methods) and the tick specs; same bound |
| `ready.go`: `ReqNewRawNode` | Yes (`MemoryStorage.InitialState` on the detached `memStor`, then `newRaft`'s post `ρ.hs = σ.hs`, `lead = 0`, `Follower`; `isHardStateEqual` is nil-safe) |
| `ready.go`: `ReqReadyAdvance` | **No**: finding 1.4 |
| `ready.go`: `ReqReadyStale` | **No**: finding 1.5 |
| `status.go`: `ReqStatus` | **No**: the write `s.HardState.Term = …` needs a field-write law for raftpb's `hardStatePts` (3h); finding 2.6 |
| `status.go`: `ReqFields` | Yes |
| `status.go`: `ReqLogger` | **No**: finding 1.6 |
| `conf.go`: `ReqApplyConf` | Yes, except `cs == nil`, which needs a non-null law for `confStatePts` (3h); finding 2.6 |

---

## Findings

### First tier

**1.1 Fifteen verified functions have no spec.** Principle broken: PRINCIPLES "A smaller API is not a
narrower scope" (the user: "Do not leave out any methods that we have verified previously"), the hard
rule "an unsound candidate is replaced by a sound one, not dropped", and the author brief §4 (only a
function that "nothing calls" may be left out).

- *Evidence*: `specs-ref`'s proofs of all 15 are complete. Callers in the batch: `hup` → `campaign`;
  `stepCandidate` → `poll`, `becomeLeader`, `campaign`; `raft.Step` → `appliedTo`, `appliedSnap`;
  `newRaft` → `loadState`, `switchToConfig`; `bcastHeartbeat` → `bcastHeartbeatWithCtx` →
  `sendHeartbeat` → `send`; `stepLeader` → `sendMsgReadIndexResponse` → `responseToReadIndexReq`.
- *Affects*: every handler's proof sketch, which cites these functions with no spec to check against.
- *Fix*: the internal `raftOpen` layer and the premises in the table in (e). This is open question 3
  answered: state them now, over an internal predicate, rather than "with the proof".

**1.2 The helper specs that exist hide the result their callers' safety turns on.**

- *Evidence*: these posts relate nothing of the result to the state (the docstrings' Margin: "The
  result is not related to the view"):
  - `raft.hasUnappliedConfChanges.spec`, `raft.promotable.spec`, `raft.pastElectionTimeout.spec`,
    `raft.committedEntryInCurrentTerm.spec`: `{{ (b : Bool), RET #b; raftCore r γ id ρ }}`;
  - `raft.maybeCommit.spec`: the commit is not tied to `b`;
  - `raft.restore.spec`.

  `raftCore` is opaque, so:
  - `hup`'s proof cannot learn from `false` that no conf entry is unapplied. That is the campaign
    guard the (b) argument needs.
  - `stepLeader`'s `MsgReadIndex` arm, and `releasePendingReadIndexMessages`, cannot learn from
    `true` that an entry of the term is committed. That is what makes `L(registration) = i`.
- *Affects*: `raft.hup.spec`, `stepLeader.spec`, `releasePendingReadIndexMessages.spec`,
  `raft.tickElection.spec`.
- *Fix*: give each result its meaning, as an internal fact the next callee consumes:
  - `b = false → campaignGuard r γ id ρ` (consumed by `campaign`/`becomeCandidate`);
  - `b = true → termCommitted γ ρ.hs.term` (persistent; consumed by `sendMsgReadIndexResponse`);
  - `promotable`: `b = true → (ρ.prs !! id).isSome ∧ ¬ learner ∧ no pending snapshot`.

**1.3 The term and index bound rests on no statement yet.**

- *Evidence*: `raft.hup.spec`, `raft.tickElection.spec`, `raft.Step.spec` (`MsgHup`, `MsgTimeoutNow`,
  a granted pre-vote) and `stepCandidate.spec` are false of a state with `r.Term = 2^64 - 1`: the
  term wraps (`raft.go:926`), then `send` panics (`raft.go:532`). They are true only if `raftCore`'s
  realization carries `maxTerm < receiptBound ≤ 2^64 - 1`. Nothing in R1 or R2 states the bound, so
  that realization cannot exist yet: `cluster_alloc.spec` has no `ReceiptBoundLe` binder.
- *Fix*: add the binder to `cluster_alloc.spec`, inside the statement (PRINCIPLES "An instance binder
  a statement must carry goes inside the statement"). `∀ [ReceiptBoundLe GF (2^64 - 2)]` would do,
  or a named constant; R1 owns the statement. Say in `ApiCore.lean` that the cluster invariant holds
  `⧗` per campaign and per appended entry. The author's open question 1; I recommend accepting it, as
  sound (see (c)).

**1.4 `ReqReadyAdvance` (`ready.go:17-30`) is unprovable, and so is R1's `RawNode.Advance` proof.**

- *Evidence*: the loop needs the queued acknowledgements (from `rawNodeAt_advance.spec`) and
  `raftCore` (from `rawNodeAt_core.spec`) at the same time. Each law consumes the whole
  `rawNodeAt rn γ id k adv`, and neither gives the other's part. Separately, the snippet's
  `err != nil → panic` needs the acknowledgements not to be `MsgProp`, and no law of `ackOk` says so:
  `raft.Step`'s post leaves `⌜m.type = MsgProp⌝ ∗ errIs ErrProposalDropped err` open.
- *Fix*: one opening law, `rawNodeAt ⊢ ∃ r ρ sl ps ms, raftOf rn r ∗ raftCore r γ id ρ ∗ field ↦ sl ∗
  ownSlice … ∗ [∗list] (msgPts ∗ ackOk) ∗ (∀ ρ' sl', raftCore r γ id ρ' ∗ field ↦ sl' ∗ … ∗ ⌜ps' =
  []⌝ -∗ rawNodeAt rn γ id k false)`, and `ackOk_type.spec : ackOk rn γ m ⊢ ⌜m.type ∈ [MsgAppResp,
  MsgVoteResp, MsgPreVoteResp, MsgStorageAppendResp, MsgStorageApplyResp]⌝` (or put
  `m.type ≠ MsgProp` in `ackPost`).

**1.5 `ReqReadyStale` (`ready.go:32-46`) is unprovable.**

- *Evidence*: R1's new `HasReady` turns `false` into `readyFresh … rd`, but no law relates
  `readyFresh` or `HasReady = false` to `rd`'s content. The snippet's panic (`len(rd.Entries) != 0 ||
  …`) cannot be discharged.
- *Fix*: on `false`, `HasReady`'s post should also give `⌜rd.Entries, CommittedEntries, Messages,
  ReadStates empty ∧ Snapshot = nil ∧ HardState = nil⌝`, provable from the monotonicity in (d). Or
  restate the snippet on what the spec gives. Drop "but for its soft state" from the header (see
  (d)).

**1.6 `ReqLogger` (`status.go:41-47`) is unprovable.**

- *Evidence*: `getLogger.spec` gives `loggerOk lg`, but no law says `loggerOk lg ⊢ ⌜lg ≠
  interface.nil⌝`. `SetLogger(l)` stores whatever it is given (`logger.go:45-48`), so the guarantee
  must come from `loggerOk`.
- *Fix*: the law `loggerOk_nonnil.spec` (R1's predicate: a request in `req/`), or `⌜l ≠ nil⌝` in
  `SetLogger`'s pre and `getLogger`'s post. Both need the package-init law that `raftLogger` is
  guarded by `raftLoggerMu` and meets `loggerOk` (`X.init.spec`, README); it is missing.

**1.7 `ackPost`'s snapshot arm no longer meets R1's `RawNode.Advance` (integration with R1 round 2).**

- *Evidence*: R1's `RawNode.Advance.spec` now gives the client
  `∀ a m, confAt γ a m -∗ ⌜s.index ≤ a ∧ s.conf.Is m⌝ -∗ |={⊤}=> nodeConf rn γ ⟨a, m⟩`.
  `ackPost` (`ApiCore.lean:220`) gives `∃ a mm, nodeConf ⟨a, mm⟩`, with `a` chosen by raft. The
  existential is weaker, and the wand cannot be derived from it. R1 requested the change in `req/`,
  item 8.
- *Sound to give*: the tracker holds `m` (`ConfState.Is` fixes it), and V1 accepts any committed
  `a ≥ s.index = applied`.
- *Fix*: give R1's wand in `ackPost`.

### Second tier

**2.1 `newStorageAppendRespMsg.spec` omits `Index`/`LogTerm`** ("`ackOk` carries it"). `acceptReady`'s
proof mints `ackOk` from this post, and the acknowledgement's `stableTo` is sound only if
`(Index, LogTerm)` is the log's last entry id at the hand-out (`rawnode.go:355-356`). State
`mm.index`/`mm.logTerm` as the log's last entry id, or the absence of both.

**2.2 The configuration invariant is unstated.** (b)'s V1-V3 are what make R1's item 8 dischargeable,
and they answer the author's doubt. Put them in `ApiCore.lean`'s realization, with the backward move
of the view at `appliedSnap`. Cross-batch note for 2d: after such a backward move, the client must
apply or skip the entries between the new and the old point again, which etcd's replay does not do
for conf entries below its consistent index.

**2.3 The read updates' firing point** (`ApiCore.lean:60-62`). Firing at confirmation fires at the
commit length then, which exceeds `i` whenever the leader commits between registration and
confirmation, contradicting `readState_fire.spec` (`l'.length = i`). Restate as in (a) item 4.

**2.4 The term-bound bookkeeping** in `ApiCore.lean:67-70` should name the owner's protocol (the
deposited `⧗`) and the bootstrap offset.

**2.5 `readyFresh`/`readyKept` realization.** Say that `readyKept` keeps no claim on `rd`'s Go memory.
`rd.Messages` aliases `r.msgs`, and later sends overwrite it (`rawnode.go:145`, `:181`;
`raft.go:598`). Say also that the `HasReady` law's soundness is the monotonicity in (d), and request
the "next" sets' monotonicity from R3 (already in `req/`, "To R3").

**2.6 Missing small laws.** None is R2's own predicate, so each goes into a request in `req/`:

- `confStatePts p … ⊢ ⌜p ≠ null⌝` (3h; `ReqApplyConf`);
- a field-write law for `hardStatePts` (3h; `ReqStatus`);
- `globalRand`'s init law (`lockedRand.Intn.spec` takes `globalRand ↦□ lr` with no source).

**2.7 Weak posts, to note as margin.** `getStatus` does not relate `Progress`/`Config` to `ρ.prs`.
`raft.restore.spec`'s result says nothing of the commit; `handleSnapshot` does not need it. Fine as
margin, but the docstrings should say what the code guarantees (PRINCIPLES "Know the margin").

**2.8 `msgSent_leaderOf.spec` and `leaderOf` are exported from `ApiCore.lean`**, which clients
reach. They are internal facts of raft's handlers ("Internal" heading); move them to an internal
module, or mark them internal in `etc/api` when the API list is made.

### Bugs in the Go code

None new. Two candidates I checked are unreachable:

- the second forward of a stamped `MsgTransferLeader`, which would make `send` panic at
  `raft.go:536`: see (a);
- a heartbeat commit past the log after a replaced snapshot: see (a) item 3.

`electionElapsed` wraps after 2^63 ticks at a non-promotable follower: liveness only, no panic; not
filed.

## Targets ranked by need of revision

1. **The internal layer** (the 15 missing helpers; the result-less `hasUnappliedConfChanges`,
   `promotable`, `pastElectionTimeout`, `committedEntryInCurrentTerm`, `maybeCommit`, `restore`): 1.1,
   1.2.
2. **`ApiCore.lean`**: the term bound's source (1.3); the opening law and `ackOk_type` (1.4); `ackPost`
   to R1's wand (1.7); the realization of reads, configurations, responses and the term bound (2.2,
   2.3, 2.4, 2.5).
3. **Snippets** `ready.go` (`ReqReadyAdvance`, `ReqReadyStale`) and `status.go` (`ReqLogger`,
   `ReqStatus`): 1.4-1.6, 2.6.
4. **`raft.Step`, `hup`, the ticks, `stepCandidate`**: sound once 1.3 holds; their sketches need 1.1
   and 1.2.
5. **`newStorageAppendRespMsg`, `getStatus`**: 2.1, 2.7.
6. **Sound as written**: `newRaft`, `raft.applyConfChange` (checked both branches against
   `confAt_skipped`/`confAt_decided`), `Config.validate` (matches `raft.go`'s `validate`, including
   the defaulting), the `Ready` phase specs, the getters, `becomeFollower`, `handle*`, `send*`/`bcast*`
   (all premised on `role = Leader`), the trace hooks (no-ops in `state_trace_nop.go`).

## Verdict

The specs are not ready. The core design survives every attack I tried: `raft.Step` with provenance
only, the configuration ahead of the log, the replaced snapshot, reads, and receipts. The three
questions the author put to reviewers can be answered "sound":

- (b): yes, with V1-V3;
- (c): yes, once `cluster_alloc` carries the bound;
- (d): yes, and R1 has adopted the fix.

What blocks it:

- the batch drops 15 verified functions;
- the remaining helper specs cannot carry the handlers' proofs (1.1, 1.2);
- the term bound has no statement (1.3);
- three snippets need laws that do not exist (1.4-1.6);
- `ackPost` must follow R1's round-2 wand (1.7).

A second round is needed.
