# Draft S4: the simulation on paper (2026-11-08)

Part of `notes/trace-validation-plan.md` (layer B; Draft S4, "the simulation on paper": `R`, each
hook's correspondence, determinism, the invariants' mapping). It decides what increment 2 of the
hooks' specs is (`notes/trace-validation-hooks.md`: the logger's contract) and what layer D must
discharge.

**Revision 12 (after review round 11, 2026-11-08; `notes/trace-validation-reviews/s4-r11.md`).**
**Round 11 found nothing first-tier: the Review is clean on that tier.** Changed (second and third
tier): `RestartNode` keeps `TraceLoggerOk` everywhere it is named, Q1 included (S1); the allocation's
premises all conditional on a traced cluster, `tr.isSome → |peers| ≤ 3 ∧ ¬dup ∧ boot ≠ []`, since
`cluster_alloc` is shared by every client (S2); the filter's deadness by P3, the cursors in step
(1), the law giving untraced clients their fact (`cluster_alloc`'s post gains `γ.raft.reTrace =
tr`) and the statements it changes, the revived mode's node facts a cost of S5 (third tier).

**Revision 11 (after review round 10, 2026-11-08; `notes/trace-validation-reviews/s4-r10.md`).**
Round 10 found round 9's repairs made and one first-tier item, one clause: `RestartNode` keeps
the nil-logger premise beside `reTrace = none` (F1). Also: the permit is `⌜False⌝` (S1); the
exported `memStorage_isStorage` takes the untraced fact, the server's `compactRaftLog` does not
(S2); what reviving `reNoSnap` touches (S3); third tier. The reviewer saw nothing first-tier left.

**Revision 10 (after review round 9, 2026-11-08; `notes/trace-validation-reviews/s4-r9.md`).**
Round 9 found round 8's repairs in place and two first-tier gaps, both one sentence: `storBnd`'s
gate needs the `c = 0` exemption (F1), and the gate was moved to the cluster field `reTrace` only
in part (F2): now every gate reads "in a traced cluster" (`γ.raft.reTrace = some γt`), `StartNode`
ties its logger to it and `RestartNode` takes an untraced cluster. Also: the allocation in three
steps (S1); untraced clients' one new pure fact (S2); the empty snapshot by reviving raft's
`reNoSnap` mode (S3); third tier.

**Revision 9 (after review round 8, 2026-11-08; `notes/trace-validation-reviews/s4-r8.md`).**
Round 8 found round 7's repairs right and one first-tier gap: with the trace gate, the harness
cannot prove its `ApplySnapshot` branch (the gate denies `storBnd`'s permit) while `Ready` may
still carry a snapshot: Q6 gains "with the trace gate, `Ready`'s snapshot is empty" (F1). Changed
also: the gate is a cluster field `reTrace` (as `dup`), so untraced clients need no witness (S1);
`CommittedIsDurableInv`'s inherited commit argued from the campaign's `Ready` (S2); the `Match`
clauses for the leader's own entry (S3); a `simInv` clause for a message handed to the run loop
and not yet stepped (S4); third tier.

**Revision 8 (after review round 7, 2026-11-08; `notes/trace-validation-reviews/s4-r7.md`).**
No further behavior the specification cannot follow; round 7 saw nothing else blocking a freeze
once these and Q4-Q6 are settled. Changed: the voter-count half of P9 enters raft as a premise of
the allocation law, `|peers| ≤ 3` (F1, Q6); the compaction permit a logger-gated conjunct of the
generic storage bound `storBnd` (S1); the per-link frontier split (authority in `simInv`, an
exclusive fragment in the receiver's `simNode`), clause (a) a `simInv` clause with "one `MsgVote(T)`
per link", the self-addressed messages outside the cursor (S2); `QuorumLogInv`'s three missing
clauses, its text rewritten (S3, T1, T2); round 7's T3-T8 (the `CommittedIsDurableInv` case by
induction, the harmless calls, no `RawNode` in the API list, the index bound with `|peers|`, the
non-`dup` gate on the allocation).

**Revision 7 (after review round 6, 2026-11-08; `notes/trace-validation-reviews/s4-r6.md`).**
No further behavior the specification cannot follow. Changed: P2 (no compaction) enters raft through
a gated compaction permit the allocation never hands out (F1); P9's mechanism is an exclusive
per-link cursor owned by the link's deliverer, with the two clauses that turn it into raft's
refusal (F2); both join Q6. The budget gated on a non-`dup` cluster and non-empty proposal data (S1);
the `histsOk` copy's per-node set and the response clause (S2, S3); P7's read-index and
leader-transfer half gated (S4: `TransferLeadership`, `ReadIndex`, `Campaign`, `ForgetLeader`); the
log bound from raft's `isEntryR_receipt` (S5); round 5's C3 (`CommittedIsDurableInv`'s
`index ≤ commitIndex` reply); third tier.

**Revision 6 (after review round 5, 2026-11-08; `notes/trace-validation-reviews/s4-r5.md`).**
No further behavior the specification cannot follow. Changed: the tokens carry their position on
their link, `simInv` a per-link frontier, so P9 reaches raft's proof (A1); layer B's other premises
(the configuration, no restart, no configuration change, each node's piece of the allocation) enter
raft through gated premises on the constructors and the API (A2); both join Q6. `QuorumLogInv` is
not raft's: a per-server copy of raft's `histsOk` (B1); the commit-point clause's maintenance
clauses on messages and the leader's `Match` (B2); the `int` bounds' arithmetic and the term
bound's source (B3); the budget a counter, at `Propose` only if raft's tickets carry forwarded
proposals (B4); the term row dropped (B5); third tier.

**Revision 5 (after review round 4, 2026-11-08; `notes/trace-validation-reviews/s4-r4.md`).**
Round 4 found no further behavior the specification cannot follow (with Q4's guard and Q5's FIFO
network); its findings are about the proof's design. Changed: P5's inflight half is a workload
bound raft cannot see: a proposal budget on the node API, listed with increment 2's API changes
for the user (A1); no global bootstrap mode: `σ_init` allocated up front, a per-node bootstrap
flag (A2); one commit-point clause replaces two rows of the facts table, its source raft's
`commitIn`/`commitJ` (B1); `QuorumLogInv`'s truncation reason (B2); `ElectionSafetyInv`'s
invariant over every term-`T` entry (B3); a raft-side event record, the transcription in a module
raft may import (B4); the bounds the `int` conversions need, from the budget (B5); third tier.

**Revision 4 (after review round 3, 2026-11-08; `notes/trace-validation-reviews/s4-r3.md`).**
Changed: the logger contract hands over a persistent representation of the event and the trace is
a list of events (A1); `MoreUpToDateCorrectInv` is not raft's either (A2: item 8 of
`notes/raft-trace-validation.md`, TLC confirms; not reached by `Main`): P5 strengthened to what it
needs, a per-server clause; `ElectionSafetyInv` by route (b), `MoreThanOneLeaderInv` from
`isLeader_unique` alone (B1); the table's clauses for the corrected LC and `QuorumLogInv` (B2);
P4's extra premise and the bootstrap transition (B3); `Advance`'s stopped branch (B4); the phase
threaded through raft's internal functions, and the opened sites' reads (B5); tokens keyed by
raft's own message abstraction (B6); P9's wording and the FIFO harness's enqueue (B7); the third
tier.

**Revision 3 (after review round 2, 2026-11-08; `notes/trace-validation-reviews/s4-r2.md`).**
Open on the user (the plan's Q4, Q5): upstream's `LeaderCompletenessInv` is not an invariant of
raft (N1: item 7 of `notes/raft-trace-validation.md`), and P9 is false with three voters (N2: gap 6
by the leader's own delayed `MsgVote`); the closed theorem is false until both are decided.
Changed: increment 2's contract is a generic logger contract, the simulation raft's own (N4); the
simulation's invariant carries each server's persistent raft facts (N3); the bootstrap mode, the
`inFlight` tokens' route through the node API, tokens per message value (N5); the phantoms'
argument, the bootstrap `ApplyConfChange`, the `Step` table, `msgAbs`'s defaults,
`CommittedIsDurableInv`, P5 (third tier).

**Revision 2 (after review round 1, 2026-11-08; the report:
`notes/trace-validation-reviews/s4-r1.md`; its findings and what changed, at the end).**
Changed: the bags' phantom replies (F4); premises P5 restated on the configuration (F3), P8
(receipt after the sender's `Ready`, F1, with the harness changed: Q3 of the plan) and P9 (at most
three voters, F2, gap 6); the simulation carries `σ` itself, not a function of raft's state (S1);
the bootstrap's `ApplyConfChange` and the leader's ticks (S2); the invariants' routes corrected (S3,
S4, S5); increment 2 changes the constructors' premise again (S6); `becomeLeader`'s tally (S7);
`AppSlices` pairwise (S8); the third-tier points.

The specification side is the Lean transcription
(`Proof/github_com/mit_pdos/etcd_grove/examples/raft/tracecheck/etcdraft/Tla/`): `State` (`σ`: per
server `currentTerm`, `state`, `votedFor`, `log`, `commitIndex`, `votesResponded`, `votesGranted`,
`matchIndex`, `pendingConfChangeIndex`, `config`, `durable`; the bags `pendingMessages`,
`messages`; `reconfigCount`), `Trace.stepLine`, `checkTrace`, `traceAccepts`. The raft side is the
existing proof's (below).

## Revision 13 (2026-11-09): against the corrected specification

Trace-check resumed against `etc/tla-fixes/` (`notes/decisions.md`, "Trace-check against the
corrected `etcdraft.tla`"). What changes below, the rest standing:

- **`R_i` gains `lead`**: `σ.s i`'s `lead` (0006) is raft's `s.lead` (`PState.lead`), field for
  field. Every place raft sets it matches 0006: `becomeFollower(m.Term, m.From)` for a
  higher-term `MsgApp`/`MsgHeartbeat`/`MsgSnap` is `UpdateTerm` (lead `nil`) then the handler's
  `lead' = j`; `becomeFollower(term, None)` for a higher-term vote (request or response) is
  `UpdateTerm`'s `nil`; a candidate's `becomeFollower(m.Term, m.From)` on a same-term append is
  `ReturnToFollowerState` with `lead' = j`; `stepFollower`'s `r.lead = m.From` is `lead' = j`;
  `becomeLeader` (`lead = id`), `becomeCandidate` (`reset`: `None`) and `Timeout`'s `nil`; a
  heartbeat or append of the current term at a follower already led by `j` leaves it `j`.
- **`durable.log` is the log itself** (0002): `durableOf (σ.s i)` at the node's last `Ready` line,
  as before, now carrying the entries.
- **P5 and P9 are gone**: an append request's `commitIndex` is the leader's (0003), raft's
  `Commit` always (determinism case 2 below holds without P5); P9's order is not needed (0006). The
  tokens keep both halves (at most once, after the sender's `Ready`: the user's, 2026-11-08).
- **Determinism case 6**: `NoConflictAppendEntriesRequest` now requires a new entry (0006), so at
  every state inside a receive line exactly one of `AppendEntriesAlreadyDone`, `Conflict`,
  `NoConflict` is enabled; no "already visited" argument. `lineFuel` is gone (Q7, the relation).
- **The invariants are seven** (0009: `MoreUpToDateCorrectInv` not checked); `LeaderCompletenessInv`
  is 0007's.
- **Ghost names**: `γ.raft.reTrace = some γd` names a persistent directory of the simulation's
  ghost names (`traceDir`), so they can be added to without changing `RaftNames`.
- **Found while drafting the per-rule lemmas (2026-11-09): two `StepR` rules are looser than raft**,
  sound for raft's safety proofs (which over-approximate) but not enough for a simulation, which
  needs raft's actual, deterministic choice:
  - `rejectVote` has no guard (any `MsgVote` may be refused), while raft refuses exactly when it
    cannot grant, `¬(canVote ∧ isUpToDate)`, which is what `HandleRequestVoteRequest` computes; the
    trace line records the choice (`reject`), so a refusal where the specification grants would make
    `TraceMatched` fail, and only the code's condition rules it out;
  - `commit` lets the leader commit any index acknowledged by a quorum and of its term, while raft's
    `maybeCommit` commits exactly `trk.Committed()` (the largest such), which is what
    `AdvanceCommitIndex` computes (`maxAgree`, then the term check).
  S5 makes both exact: `StepC`/`StepCF`/`StepR.rejectVote` gain the code's condition (known in
  `Step`'s reject branch, `raft__Step/ElectionLemmas.lean`'s reject lemma), `StepR.commit` gains
  `n = ` the quorum's largest acknowledged index (known in `maybeCommit`); raft-internal relations
  (not the node API), so the acceptance test's statements are unaffected, but their pattern matches
  (`StepLemmasR.lean`, `RefinementDyn.lean`, `StepRInv.lean`, ...) gain the hypotheses. The other
  rules are exact where the trace is: their guards determine raft's choice (`appAccept`/`appStale`/
  `appReject`, `heartbeat`, `recordVote`, `win`, `lose`, `higherTerm`, `campaign`, `propose`), or
  the trace line fixes it (`sendApps`, `beat`: each message sent is a line).
  **A third (found 2026-11-09, writing `heartbeat_send`):** `beat`'s `HeartbeatOk` only bounds a
  heartbeat's commit (`≤ committed`, `≤ Match`), while `sendHeartbeat` sends exactly
  `min(Match, committed)`, which is what `Heartbeat(i, j)` builds; the line logs the commit, but the
  specification's message must equal it, so `HeartbeatOk` must be exact too (known in
  `sendHeartbeat`). `sendApps`'s `ReplOk`/`AppCommitEq` already fix a `MsgApp`'s fields
  (`appendEntries_send`).
  **`rejectVote` cannot be made exact on `StepR` (found 2026-11-09, trying it):** `toPState`
  abstracts a pre-candidate's leader to 0 (`Defs.lean`, `toPState`), while raft's `canVote` reads
  the real `r.lead`; a pre-candidate with a leader and no vote refuses a vote request that
  `PCanVote (toPState s)` allows, so the premise `¬(PCanVote ∧ isUpToDate)` would be false there and
  the branch proof (`MsgVote_eq_novote`'s `lead ≠ None` case) could not supply it. The exactness is
  the traced proofs' instead: pre-vote is off in a traced cluster (`TracedConfigOk`), so no node is
  a pre-candidate and the vote branches' code facts (`canVote`, `isUpToDate`) give it where the
  simulation's obligation is discharged. **Superseded the same day for all three:** the lines
  that `commit` and `beat` produce are logged at hooks inside raft's code (`traceCommit`, deferred in
  `maybeCommit`; `traceSendMessage`, in `send`), and the specification's step for a line is taken
  at its hook, inside that function's proof, where the code facts are in scope (`Committed()`'s
  quorum index, `IsQuorumIndex`, with its maximality; `sendHeartbeat`'s `min(Match, committed)`).
  So the exactness is supplied at the hook points by the traced specs of raft's internal functions,
  and `StepC`/`StepCF`/`StepR` stay as they are (no rebuild of the protocol's importers).

## What the statement needs

`traceAccepts events` = `(checkTrace t true).tlcOK`: from `t.initState`, every line has **exactly
one** successor state up to TLC's view (`stepLine` returns one state and `branched` stays false:
no state reached *inside* a line, a receive line's intermediate states included, has two fresh
successors), no state reached violates the eight invariants, and nothing fails evaluating. States
are compared by `State.eq` (`TState.eq`): the bags as multisets, `matchIndex` on the servers only.

So the simulation carries the specification's state `σ` itself (a ghost value, not a function of
raft's state: no function of raft's state reproduces a bag's order, and `σ` keeps values raft
forgets, the ghost copies below), with a relation `R` between `σ` and the cluster, and shows at
every line that `stepLine t ⟨σ, l, pl⟩` returns `[⟨σ', l+1, l⟩]` with `branched = false`, `σ'`
related again, and the invariants at every state visited.

## The raft side (surveyed 2026-11-08)

- The per-node protocol state is `PState` (`Protocol/Model.lean:434`: term, vote, lead, role,
  votes, outbox, base, log, commit, matched, rd), with `toPState : NState → PState`
  (`Defs.lean:1487`) and the composite step `StepR` (`Protocol/StepR.lean:144`; rules
  `higherTerm`, `campaign`, `grantVote`, `rejectVote`, `recordVote`, `win`, `lose`, `appAccept`,
  `appStale`, `appReject`, `heartbeat`, `appResp`, `commit`, `sendApps`, `propose`, ...). Each
  `raft.Step` branch delivers `StepCD` (`StepLemmasR.lean:574`), its `StepR` from `rOf s` to
  `rOf s'` consuming the received message.
- **There is no cluster-wide record of messages**: a sent message carries the persistent
  `isMessage γ m` (`Protocol/GhostState.lean:177`), so raft's own proof allows loss, duplication,
  reordering. The shared invariant `raftCommitInv` holds the committed log, the vote and win tables;
  no node's `PState`.
- The facts left after the model-level results were removed (2026-10-21): `isLeader_unique`,
  `isVote_agree`, `isCommitted_agree`/`_prefix`, `logRecs_agree`, `leadPrefix_agree`,
  `isEntryR_agree`, `plog_match_down`, `lc_core`, `cq_agree`, `heartbeat_commit_le_last`.
- At a `Ready`, `ownRaftGhost_cut` (`Protocol/Enter.lean:446`) splits the outbox: the handed-out
  messages leave, self-addressed responses stay for `Advance`.

## The relation `R`

### A server

`R_i(s, σ.s i)` relates node `i`'s state at a trace point to the specification's server:

| specification | raft | note |
|---|---|---|
| `currentTerm` | `s.term` | |
| `state` | `s.role` (`StateFollower`/`Candidate`/`Leader`) | pre-vote off: no pre-candidate |
| `votedFor` | `s.vote` | |
| `log` | `entAbs` of each entry of `s.logst.sents ++ s.logst.uents` (no compaction: `prev` is index 0) | below |
| `commitIndex` | `s.logst.committed` | |
| `votesResponded`, `votesGranted` | `dom s.votes`, `{j | s.votes j = true}` while a candidate | unconstrained otherwise: `σ` keeps them (the specification never resets them but at `Timeout`; raft's `reset` clears them), read only by `RequestVote`/`BecomeLeader`, which need a candidate; at `BecomeLeader`, see "`becomeLeader`'s tally" |
| `matchIndex` | `j ↦ pr(j).Match` while a leader | unconstrained otherwise |
| `pendingConfChangeIndex` | `0` | unrelated to raft's `pendingConfIndex` (which `becomeLeader` sets to the last index); no `ChangeConf` line in the workload (P3) |
| `config` | `⟨voters, [], []⟩` | |
| `durable` | `durableOf` of `σ.s i` at node `i`'s last `Ready` line; before its first, `TraceInit`'s | |

`entAbs`, by entry type: an `EntryConfChange` of the bootstrap log (indices up to the bootstrap
length) is `⟨1, .config, .conf C []⟩` (`newTrace`'s `serverOf`), `C` the bootstrap voters; an
`EntryNormal` is `⟨e.term, .value, .val 0⟩` (every one a `Replicate` line's `ClientRequest(i, 0)`:
proposals and the leader's empty entry alike; the proposals' data is abstracted away). There are no
other entries (P3).

### The messages

Only the traced types count (`traceSendMessage`'s switch: `MsgApp`, `MsgHeartbeat`, `MsgSnap`,
`MsgAppResp`, `MsgHeartbeatResp`, `MsgVote`, `MsgVoteResp`); the rest (`MsgProp`, `MsgHup`,
`MsgBeat`, `MsgReadIndex`, `MsgTimeoutNow`, `MsgUnreachable`, ...) are invisible to the
specification. `msgAbs` maps a traced raft message to the specification's `Msg`, with
`term := m.Term`, `source := m.From`, `dest := m.To`, every field not named below at its default
(`subtype ""`, numbers `0`, `false`, `[]`; the `Msg` structure's defaults), and: `MsgVote` a request with
`lastLogIndex := m.Index`, `lastLogTerm := m.LogTerm`; `MsgVoteResp` a response with
`voteGranted := !m.Reject`; `MsgApp` an append request of subtype `app` (`prevLogIndex := m.Index`,
`prevLogTerm := m.LogTerm`, `entries := entAbs <$> m.Entries`, `commitIndex := m.Commit`);
`MsgHeartbeat` subtype `heartbeat` (`commitIndex := m.Commit`, the rest `0`/`[]`); `MsgAppResp` an
append response of subtype `app` (`success := !m.Reject`, `matchIndex := if m.Reject then 0 else
m.Index`); `MsgHeartbeatResp` subtype `heartbeat` (`success := true`, `matchIndex := 0`).

The bags are `msgAbs` of raft's messages **plus phantoms**:

- `pendingMessages` = `msgAbs` of every node's traced messages sent and not yet handed out in a
  `Ready` (its outbox's traced messages), plus the phantoms not yet moved;
- `messages` = `msgAbs` of the traced messages handed out and not yet received, **dropped ones
  included** (the specification's network never forgets one), plus the phantoms moved.

**Phantoms.** The specification replies to every request of a lower term
(`RejectAppendEntriesRequest`; `HandleRequestVoteRequest` with `voteGranted := false`); raft, with
check-quorum and pre-vote off (P7), sends nothing ("ignore other cases", `raft.go:1200`). Each such
receipt leaves a reply in `pendingMessages` that raft never sent and nobody receives: a ghost
multiset of phantoms in the simulation's invariant. A receive line is always of a real message
(raft received it), which is in the bag (P6, P8); a phantom equal to it gives the same successor
(the bag is a multiset: which copy is taken is not observable), and a phantom equal to no received
message is never taken.

Raft's proof has no record of the messages in flight, so the bags are ghost state of the
simulation: an authoritative bag in its invariant, and an exclusive token `inFlight γt m` per
handed-out traced message, created at the `Ready` line, owned by whoever holds the message (the
harness's network), consumed at its receive line; a dropped message's token is thrown away (the
bag keeps the message). **No duplication** is a premise on the network (P6): a message delivered
twice has one token (the specification's `DuplicateMessage` is not in `TraceNext`).

### Self-addressed messages

Raft's self-addressed messages (the candidate's own vote, `MsgVoteResp` to itself; the leader's
own append acknowledgement, `MsgAppResp` to itself) go through `msgsAfterAppend`, are traced as
sent (`SendRequestVoteResponse i→i`: `RequestVote(i, i)`; `SendAppendEntriesResponse i→i`:
`AppendEntriesToSelf(i)`), stay in raft past the `Ready` (`rawnode.go:414-417` keeps them in
`stepsOnAdvance`; `ownRaftGhost_cut`) and are stepped at `Advance`, where they are traced as
received. The specification moves them to `messages` at the `Ready` line (`Ready(i)` moves every
pending message from `i`), so their tokens are created there and owned by the node
(`RawNode.stepsOnAdvance`) until `Advance` steps them.

### Phases

`σ` is cluster-wide, but every line is one node's event, and its action touches only that node's
server, the messages it sends, the one message it receives, and nothing else (`reconfigCount` and
`server` are constant in the workload). So the ghost is split: `simAuth γt σ L Φ` (the state, the
trace `L` so far, the phantoms `Φ`) in the simulation's invariant, `simNode γt i (a, P)` per node
(`a = σ.s i`, `P` its pending messages), `inFlight γt m` per message.

`R_i` holds **at the hook points**, not at every moment: raft's code updates its fields around the
hooks (`appendEntry` traces `Replicate` before the append; `maybeCommit`'s `Commit` is deferred to
its end; `becomeFollower` traces after `reset`; `Step` traces the receipt at its entry, before the
handling). So a phase:

- **idle** (between two calls into raft): `R_i(s, a)`, `P = msgAbs` of the outbox's traced
  messages not yet handed out (phantoms aside);
- **handling `m`** (inside `Step(m)`, after its `Receive*` line): the specification has done all of
  the handling at that line (`UpdateTerm`, the handler, the reply, for an append request the
  conflict truncations and the append), so `a = handle(a_entry, msgAbs m)` while raft has not; each
  hook reached during the handling is checked against `a` updated by the lines logged since, and at
  `Step`'s return the phase is idle again: `R_i(s_exit, a)`;
- the hooks inside other calls are each logged once their changes are made (or, for `Replicate`,
  just *before*: the specification's `ClientRequest` appends at the line, raft right after, with
  nothing traced in between): idle with a known pending change.

The **handling** phase is where the proof is: for each `raft.Step` branch (`StepCD`'s `StepR`
rule), the specification's handling of `msgAbs m` from `a_entry`, followed by the specification
actions of the lines raft logs inside the branch, is related by `R_i` to `s_exit`. A pure lemma per
`StepR` rule, stated on `PState`, proved from the model's definitions; each `raft.Step` branch's
proof composes them. The lines a branch logs, by rule:

| received | raft's branch | lines it logs after `Receive*` | their specification actions |
|---|---|---|---|
| `MsgVote`, higher term | `becomeFollower`, then vote | `BecomeFollower` (skipped: update term), `SendRequestVoteResponse i→j` (skipped) | none: the receive line did `UpdateTerm` and `HandleRequestVoteRequest` |
| `MsgVote`, same term | vote or refuse | `SendRequestVoteResponse i→j` (skipped) | none |
| `MsgVoteResp` at a candidate | `poll`: win, lose, wait | win: `BecomeLeader`, `Replicate`, `SendAppendEntriesResponse i→i`, `SendAppendEntriesRequest`×n; lose: `BecomeFollower` | `BecomeLeader`, `ClientRequest`, `AppendEntriesToSelf`, `AppendEntries`/`Heartbeat`; `StepDownToFollower` |
| `MsgVoteResp` not at a candidate, same term | ignored | none | `HandleRequestVoteResponse` records it (unconstrained fields) |
| `MsgApp`/`MsgHeartbeat` at a follower | append or reject, commit | `SendAppendEntriesResponse i→j` (skipped) | none |
| `MsgApp`/`MsgHeartbeat` at a candidate, same term | `becomeFollower`, then as a follower | `BecomeFollower` (skipped: return to follower) | none |
| `MsgAppResp` at a leader | `MaybeUpdate`, `maybeCommit` (when the match moved, or the probe shortcut; a rejection commits nothing), sends | `Commit` (then), `SendAppendEntriesRequest`×k | `AdvanceCommitIndex`, `AppendEntries` |
| `MsgHeartbeatResp` at a leader | sends if behind | `SendAppendEntriesRequest` | `AppendEntries` |
| a response, lower term | ignored | none | `DropStaleResponse` |
| a request, lower term | ignored (P7) | none | the reply as a phantom |
| any, higher term, not a vote | `becomeFollower`, then as above | `BecomeFollower` (skipped) and the above | `UpdateTerm` and the above, at the receive line |
| `MsgProp` (forwarded or local; untraced) | at a leader `appendEntry`; at a follower with a leader forwarded; at a candidate, or a follower without a leader, dropped | `Replicate`, `SendAppendEntriesResponse i→i`, one `SendAppendEntriesRequest` per peer not paused; otherwise none | `ClientRequest`, `AppendEntriesToSelf`, `AppendEntries` |
| `MsgUnreachable` (`ReportUnreachable`; untraced) | the peer's progress to probe | none | none |

Outside `Step`: `Tick` at a follower or candidate (`campaign`: `BecomeCandidate`, the self vote
`SendRequestVoteResponse i→i`, `SendRequestVoteRequest`×n), at a leader (`bcastHeartbeat`:
`SendAppendEntriesRequest` heartbeats); `Propose` at a leader (`appendEntry`: `Replicate`, the self
acknowledgement, `bcastAppend`); the application's `ApplyConfChange` of the bootstrap entries
(after a node's first `Ready`: an `ApplyConfChange` line, always at a follower:
`hasUnappliedConfChanges` blocks any campaign until the first `Advance`); `Ready` (`acceptReady`: the `Ready` line); `Advance` (the
self-addressed messages' receipts, whose handling at a leader logs as the `MsgAppResp` row:
`Commit`, `SendAppendEntriesRequest`).

### `becomeLeader`'s tally

`becomeLeader` clears the vote tally (`reset`, `raft.go:957`, defined at `:799`) before `traceBecomeLeader`, so at the
hook raft no longer has what `BecomeLeader(i)` checks (`isQuorum(votesGranted[i], config)`). The
hook's spec carries the won tally as ghost state from `poll`'s win (the `win` rule), equal to
`σ.s i`'s `votesGranted` at that point.

## Determinism (no branching)

At every line, the specification's successor is unique. By line kind:

1. **Node events** (`BecomeCandidate`, `BecomeLeader`, `Replicate`, `Commit`, `Ready`,
   `ApplyConfChange`, `BecomeFollower` not skipped): the line names its node, the action is a
   function of `σ`. `BecomeFollower`: exactly one of `SkipUnusedLogline` (update term or return to
   follower: the node's previous line is the receive that caused it) and `StepDownToFollower`
   applies.
2. **`SendAppendEntriesRequest`, `MsgApp`**: `AppendEntriesIfLogged(i, j, b, e)` with
   `b = index + 1`, `e = b + entries`, so `(i, j, b, e)` is fixed; it needs
   `matchIndex[i][j] + 1 ≤ b` (raft keeps `Match < Next` on every path: `reset`, `BecomeProbe`,
   `BecomeReplicate`, `MaybeDecrTo`, `MaybeUpdate`, `initProgress`; `prevIndex = Next − 1`) and `e ≤ Len(log[i]) + 1`.
   Its message's commit must be **raft's `Commit` = `Min(commitIndex, lastEntry)`**: false in
   general (gap 5 of `notes/raft-trace-validation.md`): P5.
3. **`MsgHeartbeat`**: `commit = Min(commitIndex[i], matchIndex[i][j])`: raft's heartbeat commit
   is `min(pr.Match, committed)` (`sendHeartbeat`): equal under `R`.
4. **Sends with `from ≠ to` of responses** (`SendAppendEntriesResponse`,
   `SendRequestVoteResponse`): skipped, and no other action applies (the self actions need
   `from = to`).
5. **Receive lines**: the line fixes the message up to the fields it logs, so it selects one
   message of `messages` provided **any two messages in `messages` (real or phantom) agreeing on
   the logged fields are equal** (a `σ` invariant, `MsgsDet`). By type: a vote request logs every
   field (term, from, to, index, logTerm); a vote response every field (term, granted); a heartbeat
   its commit, the other fields constant; an append response `success` and, unless a rejection or a
   heartbeat response, `matchIndex`, and the specification sets the other cases' `matchIndex` to 0;
   an append request logs everything but its entries' terms (their number is logged), so
   `AppSlices`: **two append requests of term `T` from the same source agree on the entries at
   every index both carry** (the term-`T` leader's log is append-only during `T`: raft's
   `isLeader_unique`, `leadPrefix_agree`, `logRecs_agree`); stated pairwise so that it survives
   a later truncation of the leader's log.
6. **Inside a receive line** (the states with `pl = l`): at each, exactly one handler is enabled
   (`UpdateTerm` needs a higher term, the handlers a term at most the server's;
   `Reject`/`ReturnToFollower`/`Accept` are exclusive; within `Accept`, `AppendEntriesAlreadyDone`,
   `Conflict`, `NoConflict` are exclusive but for `NoConflict` with every entry present, whose
   successor is a state already visited, so not fresh; the truncation stops at
   `prevLogIndex`, so `logOk` stays true between truncations), and the loop ends (`lineFuel`).

## The invariants

`Traceetcdraft.cfg`'s eight, at every state `stepLine` visits, the intermediate states of a
receive line included: `LogInv`, `MoreThanOneLeaderInv`, `ElectionSafetyInv`, `LogMatchingInv`,
`QuorumLogInv`, `MoreUpToDateCorrectInv`, `LeaderCompletenessInv`, `CommittedIsDurableInv`.

They are about `σ`, which during a handling phase is ahead of raft, and a receive line's
truncation states correspond to no raft state at all. Two routes:

- (a) **from raft's ghost facts through `R`**, for the idle nodes, with the node being handled
  contributing the specification's handled state;
- (b) **as inductive invariants of the specification**, proved once on the Lean transcription.

None of the eight is cheap:

- `MoreThanOneLeaderInv` from `isLeader_unique` (`Ghost.lean:1111`) through the table's leader
  clause (the win is recorded at `poll`'s `win` rule, before `traceBecomeLeader`);
- `ElectionSafetyInv` (a leader holds the highest-indexed entry of its own term) by route (b): a
  `σ` invariant, each entry linked to its leader by its term, "while `i` leads `T`, every term-`T`
  entry in any server's log and in any append request (of any term: a later leader re-sends term-`T` entries while a stale leader of `T` still
  leads) is at an index `≤ len(σ.s i.log)`" (only `i` creates term-`T` entries, its log only grows
  while it leads, truncation and `ClientRequest` preserve it), since no persistent raft fact gives
  the upper bound and the leader's own term log is not visible at another node's hook;
- `MoreUpToDateCorrectInv` is **not** raft's either (A2; item 8 of `notes/raft-trace-validation.md`:
  five voters and cut batches violate it, TLC confirms): it holds because every `MsgApp` carries
  the leader's log to its end (P5), so a server that learns a commit index in term `T` from a leader
  holds the commit point's entry: the commit-point clause below (with `lc_core`: a log at least as
  up to date has last term at least the commit point's entry's term, so at least the quorum's);
- `QuorumLogInv` is **not** raft's (round 5's B1: raft proves nothing about a quorum's *current*
  logs; a quorum member that moved to a higher term on a vote request keeps no `ackAgree` of its
  acknowledgement): route by a per-server copy of raft's `histsOk` (`GhostState.lean:554-556`:
  for every acknowledgement in a set, the history of the node's current log, `hist`,
  `Ghost.lean:3509`), over a per-node set the node snapshots at its `SendAppendEntriesResponse`
  hooks (an ack becomes raft's `isAcked` only once durable, `ownLogGhost_ack`,
  `StepGhost.lean:584-620`, so the copy keys on its own set), which with a commit quorum and
  `lc_core`/`cq_agree` gives each member's log the committed prefix (raft's own `lc_adj_gen`
  argument, `LeaderCompleteness.lean:176-189`); `hist` at truncation states takes the divergence
  disjunct at the first conflict (the history's bound is the copy's own choice). It quantifies over
  every server's committed prefix, including a follower's inherited commit, so three clauses
  (round 7's S3; for `j ≠ l`; the leader's own match is `E_T − 1` from `BecomeLeader` until it
  receives its self-acknowledgement at `Advance`, then at least `E_T`: round 8's S3, round 9's T2): a leader's `matchIndex[l][j]` is 0, or its
  response is in `j`'s set, or at most
  `j`'s commit index; the per-node sets only grow; a cluster-wide commit record naming, for each
  commit index any server holds, its quorum, with raft's `cq` at that commit;
- `LogInv`, `LeaderCompletenessInv`,
  `CommittedIsDurableInv` (a leader's commit index is within its durable log: every response
  that reaches a leader answers a request handed out at one of its `Ready`s (P8), at which its
  whole log was persisted, and its own match counts toward a quorum only with the others'; the
  commit index a leader inherits at its election is within its durable log because its
  campaign's `Ready` persisted its whole log before any vote could be won (the self-vote too is
  stepped at `Advance`, `raft.go:1070-1078`): round 8's S2) are
  raft's safety theorems: route (a) from `isCommitted_agree`, `lc_core`, `cq_agree`, the
  leader's log records; **`LeaderCompletenessInv` is not one** (N1, Q4: false of raft; with the
  guard `currentTerm[l] >= currentTerm[i]`, from `lc_core` in its "committed at term `Tc`,
  leaders of later terms" form);
- `LogMatchingInv` from `logRecs_agree`/`plog_match_down`;
- at a receive line's truncation states (`ConflictAppendEntriesRequest` drops one entry at a time):
  `QuorumLogInv` by the `hist` copy above (the divergence disjunct at the first conflict),
  `MoreUpToDateCorrectInv` the commit-point clause (a
  shorter log is not more up to date, and the commit point stays), and the others are preserved
  by a truncation outright.

So route (a), with per-action preservation lemmas for the specification's intermediate states. A
hook of node `i` holds only node `i`'s part and raft's shared invariants, not the other nodes'
(N3), so the simulation's invariant carries, **for every server `j`, the persistent raft facts
`σ.s j` stands for**, maintained by node `j`'s steps:

| clause | raft fact | used by |
|---|---|---|
| `σ.s j` a leader of `T` | `isLeader γ j T` (`Ghost.lean:1081`) | `MoreThanOneLeaderInv`, the corrected LC |
| `σ.s j`'s log, entry by entry | `logRecs`/`isEntryR` records of `j`'s log (at a truncation state of a receive line: a strict prefix of one) | `LogMatchingInv`, `MoreUpToDateCorrectInv`, `QuorumLogInv` |
| `σ.s j`'s committed prefix | committed in `raftCommitInv` (`isCommitted`) | `LogInv`, `QuorumLogInv`, `MoreUpToDateCorrectInv`, LC |
| **commit point**: `j`'s commit index `c` is covered by a commit quorum at a term `t ≤ term(σ.s j.log[c])` (so `t ≤ σ.s j.currentTerm`) | `commitIn γ F c T` (`commitJ`, `Ghost.lean:3248-3252`: a `cq γ t n G` with `c ≤ n`, `t ≤ T`), which `isMessage` carries for append requests and heartbeats (`GhostState.lean:198`, `:216`) and a live node's ghost pairs with its commit persistently (`ownLogGhost_commitIn`, `Protocol/ReadIndex.lean:686-689`), strengthened to `t ≤ term(log[c])` by P5 and two maintenance clauses (round 5's B2): every append request in the bags carries its sender's stronger certificate (`t ≤ term` of the sender's entry at the commit), and a leader's `Match[j]` (`j ≠ l`; its own match is `E_T − 1` from `BecomeLeader` until it receives its self-acknowledgement at `Advance`, then at least `E_T`: round 8's S3, round 9's T2) is 0, at or past its term's empty entry, or at most `j`'s commit index (so a heartbeat's `min(Match, committed)` is covered); holds at truncation states (entry `c` is never removed) | the corrected LC, `MoreUpToDateCorrectInv` |
| `j`'s acknowledgements' histories | raft's `histsOk` of `j` (`GhostState.lean:554-556`) over a per-node set of acknowledgements snapshotted at `j`'s `SendAppendEntriesResponse` hooks (the ack is recorded in raft's ghost outside any hook: the copy keys on its own set, not on `isAcked`), with a bag clause: every successful append response handed out is in its source's set | `QuorumLogInv` (at a `Commit` line, from the leader's match-index quorum: its members' responses are in their sets) |
| successful responses | every successful append response of term `T` in the bags has `matchIndex ≥ E_T` (the term's empty entry) or `≤` its source's commit index (route (b), from P5 at each send; raft's `isMessage` carries only `isAcked`) | the commit-point clause's `Match` clause |
| `σ.s j`'s durable record | none: `σ`'s own value (route (b)), set at `j`'s `Ready` lines | `CommittedIsDurableInv` |

At a receive line, `σ` already holds the receiver's appended log and new commit index while raft
does not: the receiver's clauses there come from the received message's facts (`isMessage`: the
carried entries' records, the commit's certificate) with its own records (C5).

This is the largest part of layer B's proof; S5's estimate starts here.

## Premises (layer B's), discharged by layer D

- **P1** no restart (`InitState` only at bootstrap: gap 1);
- **P2** no compaction, so no snapshot (`MsgSnap` never sent: gap 3): compaction is the client's
  (`MemoryStorage.Compact`), so in a traced cluster it needs a permit the allocation never hands
  out (round 6's F1; round 7's S1: a gated conjunct of the generic storage bound `storBnd`; in
  `Main` the branch that would compact is dead by `SnapshotEvery = 0`, `concurrent.go:330-336`,
  and the empty-snapshot law below covers `ApplySnapshot`: round 9's T5;
  `InvNodeRule.lean:596-605`, since `ApplySnapshot` of a client-made snapshot and a custom storage
  compact too; Q6);
- **P3** no configuration change but the bootstrap's (gaps 2, 4; the application applies the
  bootstrap entries' `ConfChange`s, logged `ApplyConfChange`; `FullCConfig`'s changes are not in
  `Main`);
- **P4** every node starts by `StartNode` with the same peers (its bootstrap lines `InitState`,
  `BecomeFollower`, `ApplyConfChange`; the bootstrap log the `C` of `entAbs`), and **no node's first
  line after its bootstrap segment is a bootstrap-named line** (else `bootstrapOf` counts it and
  moves `TraceInit`): a node's first line after `StartNode` is its first `Ready` or a receipt,
  since `hup` refuses while `hasUnappliedConfChanges`, and the application applies the
  bootstrap's changes only from a `Ready`, which is logged first (`confc` is served after
  `acceptReady`). The nodes' segments may interleave with each other's other lines, as
  `Traceetcdraft.tla`'s per-node `BootstrapLogIndicesForServer` allows;
- **P5** (gaps 5, 8) **every `MsgApp` carries the leader's log from `Next` to its last index**, by
  the configuration and a **proposal budget** (round 4's A1: the inflight half is a workload bound,
  60 proposals, which raft's proof cannot see: `isMessage .app` says only that the entries are a
  prefix of the leader's log; a finite pool of credits allocated with `γt`, one taken by each
  `Node.Propose` in a traced cluster and carried by a forwarded `MsgProp`, gives
  the leader's invariant "entries appended this term ≤ credits spent + 1 < `MaxInflightMsgs`"; a
  `maybeSendAppend` lemma: with `noLimit` and the inflights not full, the entries are the whole
  suffix from `Next`): `MaxSizePerMsg` unlimited (`^uint64(0)`; raft's `noLimit`: a
  batch is never cut, while Goose's semantics, which ignores delays, allows unboundedly many
  elections, so an unboundedly long log) and `MaxInflightMsgs` above the entries a leader appends
  in one term (256 against at most `Proposals` + 1; in `StateReplicate` each
  `MsgApp` with entries carries entries not sent before, and `reset`/`BecomeProbe` empty the
  inflights), so no `MsgApp` is throttled or cut and each carries `Commit ≤ Index + len(Entries)`;
- **P6** no message duplicated by the network;
- **P7** pre-vote, check-quorum, `AsyncStorageWrites` off (the configuration premise), and
  `TransferLeadership`, `ReadIndex`, `Campaign`, `ForgetLeader` not called in a traced cluster (gated,
  round 6's S4: they look followable, `Campaign`/`MsgTimeoutNow` reaching `hup` as a `Timeout`,
  `ForgetLeader` only making raft grant more, `ReadIndex`'s context dropped by `msgAbs`, but that is
  not checked, and the harness calls none): no `MsgPreVote` (whose campaign the specification has no
  action for), no reply to a stale request (the phantoms), no lease or read-index state; every
  proposal a normal entry;
- **P8** (F1) a message is received only after its sender's `Ready` line: the harness sends a
  `Ready`'s messages after `Advance`, which the run loop takes only after `acceptReady` has logged
  the `Ready` (`concurrent.go`'s `app`; Q3 of the plan; `nonissues/raft-trace-ready-logged-after-handout.md`);
- **P9** (gap 6), in its final form (with Q5 (a)): **a voter that learns of its term-`T` leader
  without having voted in `T` never receives a `MsgVote` of term `T`**. Its two halves: at most
  three voters (the allocation law's premise `|peers| ≤ 3`, round 7's F1, Q6: with five, a second
  candidate's `MsgVote` reaches such a voter on another link; four are still safe), and each link
  delivering in order (the per-link cursor, Q6: the leader's `MsgVote` to the voter was handed out
  before any of its heartbeats, so it comes first or is dropped). Without the FIFO network it is
  false with three voters (N2: the leader's own delayed `MsgVote`). The FIFO harness must
  enqueue each link's messages synchronously, in the application goroutine, in `rd.Messages`
  order across `Ready`s; only the link's goroutine delivers.

## S5: the hook paths (2026-11-09)

The call graph from raft's entry points to its hooks (computed from the pinned source,
`.lake/goose/raft`, by a syntactic pass over the package: calls by name, `r.step` resolved to the
three `step*`, `r.tick` to the two `tick*`; a few name collisions removed by hand). The functions on
some path, whose specs carry the simulation's capability (Q8 of the plan: `trCap s.tr r id ph`):

- entry points: `raft.Step` (from `RawNode.Step`, `node.run`; `Advance`'s self-addressed
  messages), `raft.tickElection`/`tickHeartbeat` (`RawNode.Tick`), `RawNode.acceptReady`
  (`traceReady`), `RawNode.ApplyConfChange` (`applyConfChange`, `switchToConfig`:
  `traceConfChangeEvent`), and the bootstrap ones, not simulated (`newRaft`: `traceInitState`;
  `RawNode.Bootstrap`: `becomeFollower`, `applyConfChange`);
- `raft.Step`'s branches: `stepLeader` (`traceChangeConfEvent`), `stepCandidate`, `stepFollower`,
  `hup`, `campaign`, `handleAppendEntries`, `handleHeartbeat`, `handleSnapshot` (no snapshot in
  the workload: P-level, but on the path), `appliedTo`/`appliedSnap`;
- the hooks' direct callers: `send` (`traceSendMessage`), `appendEntry` (`traceReplicate`),
  `becomeCandidate`, `becomeFollower`, `becomeLeader` (theirs), `maybeCommit` (`traceCommit`,
  deferred), `switchToConfig` (`traceConfChangeEvent`);
- `send`'s callers: `sendAppend`, `maybeSendAppend`, `maybeSendSnapshot`, `bcastAppend`,
  `sendHeartbeat`, `bcastHeartbeat`, `bcastHeartbeatWithCtx`, `sendTimeoutNow`,
  `sendMsgReadIndexResponse`, `releasePendingReadIndexMessages`, and the above.

Every other function of the package owns the physical predicate without touching the logger, so its
spec is unchanged under Q8's option (a).

## S5 Draft: the capability (2026-11-09)

`Proof/go_etcd_io/raft/v3/TracedHooksDraft.lean`. The mode is the node's (`NGhost.tr`, Q8), so the
statements below are uniform: one spec per function, whose untraced instance is the current spec.

- **`TraceFire tr tl E Q`**, the event builder's gate (`traceEvent`/`traceNodeEvent`): untraced, a
  nil logger and `Q`; traced, the logger's contract and, for every event `e` the builder may log
  (`E e`: `NodeEvOf evt id s c` for a node event, the fields read from the state, the voters a
  permutation of each half's, as `Slice()`'s spec gives and `toSet` ignores), the atomic update
  appending `e` and giving `Q`. The builder needs the state's reads (`ownRaftPhysCV`, given back):
  the opened sites of "Increment 2" either hold it whole there or lend the read fields.
- **`trCap tr r id Φ`**, a hook path's capability: `emp` untraced; traced, the node's share
  `simNode tn id c P` with the phase `Φ C c P`, the logger's field and contract, the simulation's
  invariant (`inv simNS (simInv C tn)`), the directory (`traceDir γd tn`, its voters `C`).
- **The phases are relations, per function**, between the node's state and its share: the idle
  relation `SimIdle C s c P` (`SimServerR` with the bootstrap log `|C|` configuration entries, the
  log uncompacted, `P` the outbox's traced messages) at most entries and exits; a hook's own
  precondition is what its line's step needs, stated with the specification's action (for
  `traceCommit`: the server is a leader whose `AdvanceCommitIndex` commits exactly to `n`,
  `AdvancesTo a n`, and the server so committed is idle-related to the state, which raft has already
  moved). `maybeCommit`: idle to idle; its proof supplies `AdvancesTo` from `Committed()`'s quorum
  index (`advanceCommitIndex_eq`; for `false`, the same lemma's no-change case, to be proved).
- **Handling phases** (inside `Step`, after the receive line: the specification ahead of raft by
  the handling of `m`) are stated the same way, with the specification's handling of `m` at the
  share's server (next slice: `stepLeader`'s `MsgAppResp`, the first that reaches a hook inside).
- **Local and global (decided by the agent, 2026-11-09).** Every line is one node's event, and its
  action touches only that node's server, its pending messages and (receive and `Ready` lines) the
  message bag. So each line has a **local effect**, the specification's own action applied to a
  local state (`locSt C a P`: the servers `C`, every server `a`, the pending bag `P`, no messages;
  the actions read only server `i`'s variables and its configuration): `LineEffect e a P a' P'`.
  The function proofs show local effects only (from the code facts and the per-rule lemmas); one
  **global theorem**, proved once in the hook proofs, lifts a local effect to the whole state's
  step: from `simInv`'s `σ` whose node `i` is `(a, P)`, a line `e` of `i` with that local effect
  steps `σ` uniquely (determinism: no other server's action matches a line naming `i`; the receive
  lines' one matching message, `MsgsDet`/`AppSlices`) to `σ'` whose node `i` is `(a', P')`, the
  others unchanged, the invariants holding (through `R`). A hook's traced spec is then
  phase-polymorphic: it takes the caller's phase `Φ` and `Φ'` with the premise that every event
  `e` it may log (`NodeEvOf …`) has, from every `(a, P)` with `Φ`, a local effect into `Φ'`; `send`
  likewise (a traced type's line is the leader's action, `AppendEntries`/`Heartbeat`/`RequestVote`/
  `AppendEntriesToSelf`, or a reply the receive line already queued, a skipped line; another type
  logs nothing).

**The local effect, in Lean (Draft, 2026-11-09, `TracedHooksDraft.lean`).** `LineEffect C e0 e a P M
a' P' M'`: the specification's own `next`, iterated over single successors (`NextChain`, the search's
freshness and invariant checks left to the global step), on a two-line local trace (`locTrace`: the
node's previous line `e0`, which only a `BecomeFollower` line's skip reads, then `e`; no bootstrap
flag) from the local state `locSt C a P M` (every server `a`, pending `P`, messages `M`), to node
`i`'s server `a'`, pending `P'`, messages `M'`. A hook path's phase premise is `PhaseStep E Φ Φ'`:
from every share in `Φ`, each event `E` allows has a local effect into `Φ'` (any previous line). The
hooks themselves (`traceSendMessage`, `traceReceiveMessage`, `traceBecome*`, `traceReady`,
`traceReplicate`) take only the caller's update (`TraceFire`; `TraceFireOpt` for a type the hook does
not trace; `TraceFireN` for `traceReplicate`'s one event per normal entry), stated on what the code
reads (`MessageM`, `absMsg`); `raft.send.tracedSpec` is the first caller with a phase step. The
global theorem (to be stated next): inside the logger's update, `simInv` with node `i`'s share and a
local effect steps `σ` to `σ'` (uniquely: other servers' actions do not match a line naming `i`; a
receive line's message is the one `MsgsDet` selects), the share updated, the invariants from the
per-server facts.

**A revision of `LineEffect` under consideration (2026-11-09, pending review round 1).** The local
two-line trace and the all-`a` local state make the global theorem shift a line's position and graft
a local state into `σ`, both new and large proofs. Every per-line lemma proved so far is generic in
the trace and the line's position (`next_receive`, `chain_appAccept`, `nonReceive_*`: any `t`, any
`l0`), so the effect can be stated **for every trace and every global state** meeting the line's
conditions: the line `ln` (parsed from `e`) at `t.line l`, past the bootstrap, the trace's servers the
voters, `BecomeFollower`'s skip a given bit; `σ`'s servers the voters, node `i`'s server `a`, pre-vote
and check-quorum off, and for a receive line the message `m` it consumes present and the only one
the line matches; then the rounds from `⟨σ, l, l - 1⟩` are single fresh successors (the search's
`memEq`) through intermediate states `mids` to `σ` with node `i`'s server `a'` and the bags `fM`,
`fP` of `σ`'s (the line kind's bag effect: a send `with`s a pending message, a receive `without`s
its message and `with`s its reply, a `Ready` moves the node's pending messages). The global theorem
then instantiates `t` with the run's trace and needs only the invariants at `mids` and at the end,
from the per-server facts (the intermediate states' shapes, a term change or a log prefix of
node `i`, stated in the effect).

**The invariants from the facts (2026-11-09, `TraceSimFacts.lean`).** Proved from `srvFacts`
(every voter's server: raft's log `es` read by `logAbs`, its records, its committed prefix
committed, a leader's `isLeader`): `MoreThanOneLeaderInv`, `LogInv`, `LogMatchingInv` (the
specification's entries are functions of position and term: `logAbs_match`), `CommitOk`. Reduced to
specification invariants (route (b)), whose preservation by each line is still to prove:
`ElectionSafetyInv` to `LeaderEntries` (every term-`T` entry anywhere sits where `T`'s leader's log
has one), `CommittedIsDurableInv` to `DurInv` (a leader's commit index, match indices, handed-out
requests and successful responses to it within its durable log). Left:

- `LeaderCompletenessInv`, through `lc_core`: each server's facts gain its commit certificate
  `commitJ γ es c (term)` (a `cq γ t n G` with `c ≤ n`, `t ≤` the server's term, `G` agreeing with
  `es` at `c`, or the bootstrap arm), a leader's its campaign `isCamp γ l T F0` with its log reaching
  `F0`'s last entry, and the global step opens raft's commit invariant for `votesTbl`. For a leader
  `l` of `T_l ≥ term_i` and `t < T_l`: `lc_core` puts term `t` at `n` in `l`'s log, then
  `plog_match_down` twice (`l`'s log against `G` down to `c`, then against `i`'s below `c`). For
  `t = T_l`: the certificate is `l`'s own (`isLeader_unique`), and `leadPrefix_agree` relates `G` to
  `l`'s current log (a leader's facts gain its `leadPrefix`); only the entries of terms below `T_l`
  are asked, which sit below the term's first index. **Found (2026-11-09):** that last step needs
  more than the persistent facts give: `leadFull_agree` relates two full logs of a term only where
  both are defined, and a commit fact's log `G` may be longer than any full log persisted for `l`
  (raft's term log grows; the facts record no upper bound), while `leadFrags` does not say that the
  entries past the campaign log are of the term. The step then needs `c ≤ |log_l|` whenever `i`'s
  certificate is of `l`'s term (so `term_i = T_l`): a specification invariant (a follower of term
  `T` learns its commit index from `T`'s leader's messages, each within the leader's log, which only
  grows during `T`), maintained with `LeaderEntries` and `DurInv`; or a leader clause from `l`'s term
  log authority at its hooks. `restart_ack_one` (`Protocol/Enter.lean`) is the template of the
  three cases (bootstrap, same term, earlier term).
- `QuorumLogInv`: the acknowledgement-history copy of the table above (`histsOk`), as planned.

## Increment 2 of the hooks' specs (what S4 decides)

**The logger's contract is generic** (round 2's N4; the `spec` skill's "TaDa, not HoCAP"): the
logger only fires the caller's atomic update, and names nothing of the TLA+ specification; it is
handed a persistent, read-only representation of the event (round 3's A1: the recorder copies
`*ev` and `Main` reads the message, the configuration slices and the `cc` property through it).

    isTraceLogger γt tl :=
      ⌜tl = nil⌝ ∨
      □ ∀ (p : Loc) (e : TraceEv) Q, tracingEventRep p e -∗
          AU⟨∀ L, traceAuth γt L⟩⟨traceAuth γt (L ++ [e]), Q⟩ -∗ WP tl.TraceEvent(#p) {Q}

`tracingEventRep p e`: `↦□` of the `TracingEvent` at `p`, its message, its slices, its map and the
map's values, `e : TraceEv` their abstract value, a raft-side record mirroring `TracingEvent`
(`ApiVocab`), with a pure map to the checker's `Event` that `ConvertEvents`' spec states (round 4's
B4: raft's public API names nothing of the example);
raft gives `↦□` since it never touches an event after the call. The trace `L : List TraceEv`. The
harness's `SyncRecorder` proves it with `traceAuth γt L` in its lock invariant (its slice of copies
pointing at the shared, read-only parts). `traceEvent`'s non-nil spec builds `tracingEventRep` and
supplies `e = eventOf …` with the caller's update.

The simulation (`σ`, the phantoms, `R`, the per-server facts) is raft's own: `simInv γt` in raft's
package (which then imports the transcription: it moves out of the example's proof directory to a
module root raft may import, listed in `etc/api/raft.txt`'s neighbour `etc/api/tracecheck.txt`)
owns `traceFrag γt L` in lockstep with `σ`, with the bounds the checker's `int` conversions need
as clauses (round 6's S5: both from raft's time receipts, terms by `budgetInv`
(`InvNodeChan.lean:192-194`) and every entry's index by `isEntryR_receipt` (`Ghost.lean:2481`),
with the adequacy theorem's receipt bound at most `2^62 − 2`, stated where that bound is owned,
an index then at most `2^62 − 3 + |peers|`, under `2^63` with `|peers| ≤ 3`; no budget needed for
them), and each hook's call site supplies the update,
stepping `σ` inside it; raft's API exports the law from `simInv γt ∗ traceAuth γt L` to "`L` steps,
line by line, to a unique state with the invariants" (layer D gets `traceAccepts` from it), and the
allocation law, in three steps (round 9's S1: `cluster_alloc` takes its name fields as inputs),
which the harness applies before the first `StartNode`: (1) allocate `γt` with `traceAuth` and
`traceFrag`, the budget, and the per-link cursors `linkCur`; (2) `cluster_alloc` with
`tr := some γt` (raft's `γ`, its cluster voters the peers), under the premise
`tr.isSome → |peers| ≤ 3 ∧ ¬dup ∧ boot ≠ []` (P9; the budget's tickets; the revived mode needs a
bootstrap log, `reNoSnap_ok`, `Ghost.lean:352`), conditional because `cluster_alloc` is shared by
every client (kvreconf and kvdurable allocate with `dup` and no bootstrap log, the server with any
number of peers: round 11's S2); its post gains `γ.raft.reTrace = tr` (which gives untraced
clients their pure fact) and gives `isCommittedLogLb γ boot`; (3) establish `simInv` at `σ_init`
(from the peers), taking `traceFrag`, the cursors' authority, the budget's authority and
`isCommittedLogLb γ boot`, and giving the nodes' `simNode`s with their bootstrap flags (round 10's
T2, round 11's T2). The harness's storage predicate is its own `MemJust` with
`B := storBnd γ K` (it cannot use `memStorJ`; `memStorInvP_alloc` at 0 and
`memStorage_isStorageP` suffice: round 10's T3, round 11). The exported law takes as premise that every peer's bootstrap lines are in
`L` (a peer not yet started contributes `σ_init`'s value for it, from the allocation).

What changes, besides the hooks' specs: `StartNode`'s premise (Q1) becomes
`isTraceLogger γt cv.TraceLogger'` inside the triple (`γt` a new binder; `isTraceLogger_nil` for a
nil logger, any `γt`), while `RestartNode` keeps `TraceLoggerOk` (a nil logger; round 10's F1,
round 11's S1); `simNode` is owned only in a traced cluster, so untraced clients carry only
the one pure fact below (round 10's T1).

What the contract's proof meets:

- **The phase is threaded, not local** (round 3's B5). `R_i` does not hold between hooks (e.g.
  `becomeLeader` after `reset`, before `traceBecomeLeader`), so the specs of raft's internal
  functions between each entry point (`Step`, `Tick`, `Propose`, `acceptReady`, `Advance`, the
  application's `ApplyConfChange`, `ReportUnreachable`) and each hook carry `simNode` and the phase
  with its pending lines: `send` and its callers (the exact list from the call graph), `becomeFollower`,
  `appendEntry`, `maybeCommit`, and their callers; `send`'s hook ignores the phase for untraced
  message types, which narrows the threading to the traced sends' callers. The list (the call graph from each entry point to each hook) and the phase
  predicate's laws come first in S5; the Probe proves one hook with its phase through `send`'s
  callers.
- **The opened sites' reads** (B5): the non-nil hooks read `hardState()`, `raftLog.lastIndex()`,
  `trk.Voters[0/1].Slice()`; at `acceptReady` the tracker is inside `Hclose`, at `send_tail` the
  rest is in the wand `Hback`, at `switchToConfig` the tracker field is being replaced
  (`traceConfChangeEvent` reads the old `r.trk.Voters`), at `newRaft` the struct is a literal. Each
  such site gets an accessor that lends the read fields and closes again (as `ownRaftPhysC_traceLogger`
  lends the logger), or the hook's spec takes the event's values from the caller.
- **The bootstrap lines** (`newRaft`'s `InitState`, `Bootstrap`'s `BecomeFollower`, the bootstrap
  `ApplyConfChange`s) are not simulated (`TraceNext` steps over them): `σ_init` is allocated up
  front, from the peers (`Bootstrap` is deterministic: each server's `serverOf` value is term 1,
  follower, vote 0, `|peers|` configuration entries of term 1 with `newconf = peers`, commit
  `|peers|`, `matchIndex` 0; `server` is the peers, with the invariant that only they log), and
  each `simNode` has a **bootstrap flag**, set until the node's first non-bootstrap line (exactly
  the per-node `BootstrapLogIndicesForServer`); while set, the node's hooks append without
  stepping. No global mode, no transition law (round 4's A2).
- **The `inFlight` tokens** of a `Ready`'s messages are created at its line, inside `acceptReady`,
  after the application already holds the `Ready` (`readyc <- rd` comes first). They reach the
  application after `Advance`: raft's `advancec` protocol already passes resources from the run
  loop back to the driver (`InvAdvance.lean:285-295`), and the run loop deposits them where
  `Advance`'s stopped branch (`node.go:555-560`, the `nodeStopped` disjunct) also finds them (B4).
  `Advance`'s post names the tokens of the `Ready`'s traced messages to others (the driver state
  `nodeDriver`'s `handling` gains `rd.Messages`), and `Node.Step` (internally `RawNode.Step`, `raft.Step`) takes a
  traced message's token (given back on a timeout), and `Propose` a budget credit (P5): **changes
  to raft's node API**, each a new
  client-owned ghost on a public spec, the user's to approve with increment 2's draft (gated on a
  traced cluster, so the existing clients are unaffected but for one pure fact, below).
- **The tokens' key** is raft's own message abstraction (the protocol model's `Msg`, which
  `isMessage` already uses), a multiset (equal messages occur: repeated heartbeats); `msgAbs` is
  applied inside `simInv`, so raft's public node API names nothing of the transcription (B6).
  **And its position on its link** (round 5's A1, round 6's F2): without order, a client holding a
  delayed `MsgVote`'s token could step it after the voter heard of the leader, where raft refuses
  and the specification grants (gap 6). An exclusive per-link cursor `linkCur γt (c, i) f`,
  allocated with `γt` and owned by the link's deliverer (the FIFO harness's link goroutine):
  `Node.Step` takes `inFlight` at position `p > f` with `linkCur … f`, returns `linkCur … p` on
  success and `linkCur … f` with the token on a timeout, a stop or an error; a `simInv` clause
  records the messages handed to the run loop and not yet stepped (a per-link set of pending
  positions above the frontier, added at the hand-off, removed at `raft.Step`: round 8's S4,
  round 9's T3; the run loop's filter of a response from an unknown sender, `node.go:394-397`, is
  dead in a traced cluster, by P3); the frontier is split,
  its authority in `simInv` (frontier `≤` cursor) and an exclusive fragment in the receiver's
  `simNode`, so "`p` above the frontier" stays true from `Node.Step`'s hand-off (`recvc`,
  `node.go:514-523`) to `raft.Step` (the run loop steps the message it took before taking another,
  `node.go:394-399`); a drop skips positions. Two clauses turn it into raft's refusal: (a) a
  `simInv` clause (used at the receiver's hook): a candidate `c` hands out at most one `MsgVote(T)`
  per link, before any term-`T` append or heartbeat on it; (b) node-local: "`lead = c` and no vote
  in `T` ⇒ the link `(c, i)`'s frontier is past `c`'s `MsgVote(T)`". The self-addressed messages
  `Advance` steps are outside the cursor (no `lead` question on a self link). (Not needed if Q5 (b)
  changes the specification instead.)
- **Layer B's other premises enter through the API** (round 5's A2), gated on a traced cluster:
  the configuration (P5's half and P7: `PreVote`, `CheckQuorum` off, `MaxSizePerMsg` unlimited,
  `MaxInflightMsgs` above the budget's per-term appends) as a premise of `StartNode`; no
  `ProposeConfChange` (P3), no `RestartNode` (P1), no compaction (P2: the permit), none of
  `TransferLeadership`, `ReadIndex`, `Campaign`, `ForgetLeader` (P7) in a traced cluster; each
  `StartNode` takes its node's `simNode` from the allocation and is called with the allocation's
  peers (P4), at most three (P9). (`RawNode` has no public spec: its changes are internal.)
  **The gate** is a cluster field `reTrace : Option GName := none` of raft's names (as `dup`);
  "in a traced cluster" means `γ.raft.reTrace = some γt` throughout. `StartNode` takes
  `cv.TraceLogger' ≠ nil ↔ γ.raft.reTrace ≠ none` (with a logger, `γ.raft.reTrace = some γt`),
  `RestartNode` takes `γ.raft.reTrace = none` **and a nil logger** (`TraceLoggerOk`, as now:
  round 10's F1; with a logger and no `simInv` raft could not commit the logger's update, since
  `traceFrag` is `simInv`'s) (round 9's F2: else a nil-logger node in a traced cluster proposes
  without a credit, or a logger node in an untraced one compacts and sends a traced `MsgSnap`).
  `storBnd γ K c := (∃ k, ⌜c ≤ k⌝ ∗ nodeAppliedLb γ K k) ∗ ⌜c = 0 ∨ γ.raft.reTrace = none⌝`
  (round 9's F1: `MemoryStorage`'s invariant needs `J.B 0`; round 10's S1: the "permit never handed
  out" is `⌜False⌝`, since `storBnd` must be persistent, `MemJust.B_pers`, and raft refutes it at
  every `ErrCompacted`, `InvStorage.lean:253`, `:265`, `:282`). Untraced clients carry one new pure
  fact, `⌜γ.raft.reTrace = none⌝`, from a law raft exports for a cluster allocated untraced: the
  `rfl` proofs of `kvJ_bnd`, `KvrStorageApi`, `KdStorageApi`, and the exported
  `memStorage_isStorage` (`MemstorageApi.lean:84-95`, used by the server's `NodeStart.lean:322`),
  which gains the premise (in a traced cluster it is false: `nodeAppliedLb` holds for some `c > 0`
  once the bootstrap is applied); the server's `compactRaftLog` compacts through `memStorJ`, whose
  `B` is not `storBnd`, and is unaffected (round 10's S2). In a traced cluster `Ready`'s snapshot is
  empty (`L = none`), so the client never needs `ApplySnapshot`'s storage bound (round 8's F1):
  raft proves it by reviving its no-snapshot mode `reNoSnap` (`Ghost.lean:344-352`, dropped in U8
  v2, its plumbing still there: the outbox's "no `.snap`", `LemmasReadyR.lean:236`, and
  `snapshotCert`'s `⌜reNoSnap = false⌝`, `InvApi.lean:1497`) as `reNoSnap := reTrace.isSome`, the
  empty snapshot a law on `readySnap` as `readySnap_bootLen` is (decided by the agent; round 9's
  S3). The revival touches (round 10's S3): `DecNames` (`InvApiBoot.lean:50-57`, `InvApi.lean:170-174`)
  and `UniNames.noSnap` (`InvApi.lean:2047-2051`), which pin the mode off for `StartNode`'s
  clusters, and `api_sentSnapCert` (`InvApi.lean:2015`); `isRaftMsg` (`ApiVocab.lean:423-428`) gains
  "in the mode, not a `MsgSnap`" (receiving one would leave the next `Ready` without its
  `snapshotCert`); `NsCap` (`InvRaftPhys.lean:852`) a real cap in the mode (the storage never
  compacted past 0); `cluster_alloc`'s `tr.isSome → boot ≠ []`. Whether the mode's node-level facts
  were proved for the dynamic mode `StartNode`'s clusters use is to check in S5. Proposals are never dropped for size: that limit is
  `MaxUncommittedEntriesSize`, which the harness leaves 0, raft's "no limit" (`raft.go:313-315`,
  `:2101`; round 9's T4). `ReportSnapshot`, `Status`, `Stop` stay callable: they log nothing the specification cannot
  follow (`ReportSnapshot` with no snapshot ever sent, `raft.go:1626-1628`).
- **The budget** is a counter (so `etc/bounds-check.py` does not count it as a list of tokens),
  taken at `Propose`; raft's per-proposal tickets are consumed at the append (`propTk_set`,
  `Ghost.lean:1233`), so a forwarded `MsgProp` carries it, except in a `dup` cluster
  (`Ghost.lean:403-409`) and for empty-data entries (`Ghost.lean:1171`, `:1353-1355`), which
  could be stepped any number of times: so in a traced cluster, the allocation requires a non-`dup`
  cluster (a property of the cluster, round 7's T7) and `Propose` non-empty data (round 6's S1; the
  harness proposes non-empty data).

### The recorder's side, proved (layer D, 2026-11-09)

`Proof/github_com/mit_pdos/etcd_grove/examples/raft/tracecheck/` (`Recorder`, `Logger`, `Convert`
and the proofs of `SyncRecorder.TraceEvent`, `SyncRecorder.Events`, `ConvertEvents`): the recorder's
lock invariant holds `traceAuth γt L` and its slice of copied events (`traceEventsRep`, built from
`tracingEventVal`, `tracingEventRep` without its pointer); `isSyncRecorder_traceLogger` gives
`isTraceLogger γt` of `c.rec`; `syncRecorder_alloc` gives `isSyncRecorder γt r ∗ traceFrag γt []`
from `&SyncRecorder{}`; `Events` takes `traceFrag γt L` and returns a slice holding `L`;
`ConvertEvents` returns `eventsRO out (L.map evConv)`, `NewTrace`'s input. `evConv` agrees with
`ConvertEvents` on the numbers (`sint.Z`, the `int(·)` conversion), the message, the properties
(present when the map has a key; `cc` only when it holds a configuration change) and the ignored
`ConfChange` field, with one premise: **the copied strings ASCII** (`TraceEv.Ascii`). The checker's
representation relates strings byte by character (`strRel`), which only an ASCII string satisfies,
while `evConv`'s `gsStr` maps any byte `c` to `Char.ofNat c`: they agree exactly on ASCII strings.
Raft's event names, roles and message types are ASCII constants and its ids `strconv.FormatUint`'s,
so the premise holds, but layer B has to state it (a `simInv` clause: every event of the trace is
`TraceEv.Ascii`, or the hooks' `eventOf` shown ASCII). Two smaller points: `isTraceLogger`'s update
is over `traceAuth`, which `InvTrace.lean` calls the logger's half, while the client (the
simulation) holds `traceFrag`; both are `ghostVar γt ½`, so the proof goes through, but the update
would read better over `traceFrag`. And a Lean gotcha met in `ConvertEvents`' proof: a local named
`done` (an existential's witness) made `word`'s auxiliary proofs ill-applied (a kernel "application
type mismatch" on `_proof_1_N`); renaming it fixed it.

## Open (for the next round)

- The handling phase's statement inside `raft__Step`'s 36 branches (one shape per branch kind,
  `wp_trace_hookC`'s successor) and how much of `StepCD` it reuses.
- Whether `simNode` lives in `ownRaftPhys` (every raft proof sees it) or beside it in `ownRawNode`
  (only the hooks' call sites thread it, as the logger field now).
- `StartNode`'s premise: increment 2's shape (`isTraceLogger γt …` inside the triple) now, rather
  than changing Q1's statement twice (`RestartNode` keeps `TraceLoggerOk`).
- The revived `reNoSnap` mode's node-level facts hold only vacuously today (`InvRaftPhys.lean:844-850`,
  `StepGhostMode.lean:427-433`): proving them is a cost in S5's estimate (round 11's T4). The
  statements the untraced fact changes: kv's exported `kv_storage_isStorage` (`kv/Results.lean:124`),
  kvreconf's and kvdurable's `isStorage` laws, the server's `srvMem_bootStorage` and its cluster
  names (`SrvRaftLog.lean:755-763`), `memStorage_isStorage` (round 11's T3).

## Review round 1 (2026-11-08): findings and what changed

First tier: **F1** a receipt can be logged before its sender's `Ready` line (`traceReady` runs after
the hand-off): P8, the harness sends after `Advance` (Q3), `nonissues/`; **F2** gap 6 (a voter that
knows its term's leader): P9, `notes/raft-trace-validation.md` item 6; **F3** P5's size half false
under Goose's semantics (unboundedly many elections): `MaxSizePerMsg` unlimited (Q3), P5 restated on
the configuration; **F4** the bags' phantom replies: added. Second tier: **S1** `σ` carried, compared
by `State.eq`; **S2** the bootstrap's `ApplyConfChange` and the leader's ticks: added; **S3**
`CommittedIsDurableInv`'s reason was false: corrected, route (a); **S4** the leader invariants need a
vote-record invariant (`VotesOk`); **S5** the truncation states need lemmas; **S6** "widened in
place" was false: increment 2 changes the statements again; **S7** `becomeLeader`'s tally: carried
as ghost; **S8** `AppSlices` pairwise. Third tier: `durable` before the first `Ready`, `entAbs` by
type, `pendingConfChangeIndex` unrelated to raft's, three more `Step` rows, `AsyncStorageWrites` in
P7, `msgAbs`'s term/from/to, `simNode` only with a logger: all done.
