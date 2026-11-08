# Draft S4: the simulation on paper (2026-11-08)

Part of `notes/trace-validation-plan.md` (layer B; Draft S4, "the simulation on paper": `R`, each
hook's correspondence, determinism, the invariants' mapping). It decides what increment 2 of the
hooks' specs is (`notes/trace-validation-hooks.md`: the logger's contract) and what layer D must
discharge.

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
  (round 7's S3): a leader's `matchIndex[l][j]` is 0, or its response is in `j`'s set, or at most
  `j`'s commit index; the per-node sets only grow; a cluster-wide commit record naming, for each
  commit index any server holds, its quorum, with raft's `cq` at that commit;
- `LogInv`, `LeaderCompletenessInv`,
  `CommittedIsDurableInv` (a leader's commit index is within its durable log: every response
  that reaches a leader answers a request handed out at one of its `Ready`s (P8), at which its
  whole log was persisted, and its own match counts toward a quorum only with the others'; the
commit index a leader inherits at its election is within its durable log by induction on
`CommittedIsDurableInv` itself (round 7's T3: an `index ≤ commitIndex` reply raises no commit
index)) are
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
| **commit point**: `j`'s commit index `c` is covered by a commit quorum at a term `t ≤ term(σ.s j.log[c])` (so `t ≤ σ.s j.currentTerm`) | `commitIn γ F c T` (`commitJ`, `Ghost.lean:3248-3252`: a `cq γ t n G` with `c ≤ n`, `t ≤ T`), which `isMessage` carries for append requests and heartbeats (`GhostState.lean:198`, `:216`) and a live node's ghost pairs with its commit persistently (`ownLogGhost_commitIn`, `Protocol/ReadIndex.lean:686-689`), strengthened to `t ≤ term(log[c])` by P5 and two maintenance clauses (round 5's B2): every append request in the bags carries its sender's stronger certificate (`t ≤ term` of the sender's entry at the commit), and a leader's `Match[j]` is 0, at or past its term's empty entry, or at most `j`'s commit index (so a heartbeat's `min(Match, committed)` is covered); holds at truncation states (entry `c` is never removed) | the corrected LC, `MoreUpToDateCorrectInv` |
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
  (`MemoryStorage.Compact`), so with a logger it needs a permit the allocation never hands out
  (round 6's F1; round 7's S1: a logger-gated conjunct of the generic storage bound `storBnd`,
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
  `Node.Propose` with a non-nil logger and carried by a forwarded `MsgProp`, gives
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
  `TransferLeadership`, `ReadIndex`, `Campaign`, `ForgetLeader` not called with a logger (gated,
  round 6's S4: they look followable, `Campaign`/`MsgTimeoutNow` reaching `hup` as a `Timeout`,
  `ForgetLeader` only making raft grant more, `ReadIndex`'s context dropped by `msgAbs`, but that is
  not checked, and the harness calls none): no `MsgPreVote` (whose campaign the specification has no
  action for), no reply to a stale request (the phantoms), no lease or read-index state; every
  proposal a normal entry;
- **P8** (F1) a message is received only after its sender's `Ready` line: the harness sends a
  `Ready`'s messages after `Advance`, which the run loop takes only after `acceptReady` has logged
  the `Ready` (`concurrent.go`'s `app`; Q3 of the plan; `nonissues/raft-trace-ready-logged-after-handout.md`);
- **P9** (gap 6; its voter-count half enters raft as the allocation law's premise `|peers| ≤ 3`,
  round 7's F1, Q6: with five voters a second candidate's `MsgVote` reaches a voter that knows the
  leader, on another link; four are still safe) **false as stated** (N2): with three voters, the leader's own `MsgVote`, delayed
  past its first heartbeat, still meets a voter that knows the leader without having voted. Open
  on the user (Q5); with a per-link FIFO network (Q5 (a)): "three voters, and each link delivers
  in order", so **a voter that learns of its term-`T` leader without having voted in `T` never
  receives a `MsgVote` of term `T`** (the leader's `MsgVote` to it was handed out first, so it came
  first or was dropped; no other candidate of `T` exists with three voters). The FIFO harness must
  enqueue each link's messages synchronously, in the application goroutine, in `rd.Messages`
  order across `Ready`s; only the link's goroutine delivers.

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
an index then below `2^62 − 3 + |peers|`, under `2^63` with `|peers| ≤ 3`; no budget needed for
them), and each hook's call site supplies the update,
stepping `σ` inside it; raft's API exports the law from `simInv γt ∗ traceAuth γt L` to "`L` steps,
line by line, to a unique state with the invariants" (layer D gets `traceAccepts` from it), and the
allocation law: `γt` with `traceAuth`, `traceFrag`, `simInv` at `σ_init` (from the peers), the
nodes' `simNode`s with their bootstrap flags, and the budget, which the harness applies before
the first `StartNode`; the exported law takes as premise that every peer's bootstrap lines are in
`L` (a peer not yet started contributes `σ_init`'s value for it, from the allocation).

What changes, besides the hooks' specs: the constructors' premise (Q1) becomes
`isTraceLogger γt cv.TraceLogger'` inside the triple (`γt` a new binder; `isTraceLogger_nil` for a
nil logger, any `γt`); `simNode` is owned only with a logger, so nil-logger clients carry nothing
new.

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
  non-nil logger, so the existing clients are unaffected).
- **The tokens' key** is raft's own message abstraction (the protocol model's `Msg`, which
  `isMessage` already uses), a multiset (equal messages occur: repeated heartbeats); `msgAbs` is
  applied inside `simInv`, so raft's public node API names nothing of the transcription (B6).
  **And its position on its link** (round 5's A1, round 6's F2): without order, a client holding a
  delayed `MsgVote`'s token could step it after the voter heard of the leader, where raft refuses
  and the specification grants (gap 6). An exclusive per-link cursor `linkCur γt (c, i) f`,
  allocated with `γt` and owned by the link's deliverer (the FIFO harness's link goroutine):
  `Node.Step` takes `inFlight` at position `p > f` with `linkCur … f`, returns `linkCur … p` on
  success and `linkCur … f` with the token on a timeout, a stop or an error; the frontier is split,
  its authority in `simInv` (frontier `≤` cursor) and an exclusive fragment in the receiver's
  `simNode`, so "`p` above the frontier" stays true from `Node.Step`'s hand-off (`recvc`,
  `node.go:514-523`) to `raft.Step` (the run loop steps the message it took before taking another,
  `node.go:394-399`); a drop skips positions. Two clauses turn it into raft's refusal: (a) a
  `simInv` clause (used at the receiver's hook): a candidate `c` hands out at most one `MsgVote(T)`
  per link, before any term-`T` append or heartbeat on it; (b) node-local: "`lead = c` and no vote
  in `T` ⇒ the link `(c, i)`'s frontier is past `c`'s `MsgVote(T)`". The self-addressed messages
  `Advance` steps are outside the cursor (no `lead` question on a self link). (Not needed if Q5 (b)
  changes the specification instead.)
- **Layer B's other premises enter through the API** (round 5's A2), gated on a non-nil logger:
  the configuration (P5's half and P7: `PreVote`, `CheckQuorum` off, `MaxSizePerMsg` unlimited,
  `MaxInflightMsgs` above the budget's per-term appends) as a premise of `StartNode`; no
  `ProposeConfChange` (P3), no `RestartNode` (P1), no compaction (P2: the permit), none of
  `TransferLeadership`, `ReadIndex`, `Campaign`, `ForgetLeader` (P7) with a logger; each
  `StartNode` takes its node's `simNode` from the allocation and is called with the allocation's
  peers (P4), at most three (P9). (`RawNode` has no public spec: its changes are internal.)
  `ReportSnapshot`, `Status`, `Stop` stay callable: they log nothing the specification cannot
  follow (`ReportSnapshot` with no snapshot ever sent, `raft.go:1626-1628`).
- **The budget** is a counter (so `etc/bounds-check.py` does not count it as a list of tokens),
  taken at `Propose`; raft's per-proposal tickets are consumed at the append (`propTk_set`,
  `Ghost.lean:1233`), so a forwarded `MsgProp` carries it, except in a `dup` cluster
  (`Ghost.lean:403-409`) and for empty-data entries (`Ghost.lean:1171`, `:1353-1355`), which
  could be stepped any number of times: so with a logger, the allocation requires a non-`dup`
  cluster (a property of the cluster, round 7's T7) and `Propose` non-empty data (round 6's S1; the
  harness proposes non-empty data).

## Open (for the next round)

- The handling phase's statement inside `raft__Step`'s 36 branches (one shape per branch kind,
  `wp_trace_hookC`'s successor) and how much of `StepCD` it reuses.
- Whether `simNode` lives in `ownRaftPhys` (every raft proof sees it) or beside it in `ownRawNode`
  (only the hooks' call sites thread it, as the logger field now).
- The constructors' premise: increment 2's shape (`isTraceLogger γt …` inside the triple) now,
  rather than changing Q1's statement twice.

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
