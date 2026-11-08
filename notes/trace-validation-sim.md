# Draft S4: the simulation on paper (2026-11-08)

Part of `notes/trace-validation-plan.md` (layer B; Draft S4, "the simulation on paper": `R`, each
hook's correspondence, determinism, the invariants' mapping). It decides what increment 2 of the
hooks' specs is (`notes/trace-validation-hooks.md`: the logger's contract) and what layer D must
discharge.

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
`term := m.Term`, `source := m.From`, `dest := m.To` and: `MsgVote` a request with
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
multiset of phantoms in the simulation's invariant. A phantom has a lower term than its
destination's current term at its creation, and terms only grow, so no receive line consumes one
unless a real message equal to it is in the bag (then either may be taken: they are equal).

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
| `MsgAppResp` at a leader | `MaybeUpdate`, `maybeCommit`, sends | `Commit`, `SendAppendEntriesRequest`×k | `AdvanceCommitIndex`, `AppendEntries` |
| `MsgHeartbeatResp` at a leader | sends if behind | `SendAppendEntriesRequest` | `AppendEntries` |
| a response, lower term | ignored | none | `DropStaleResponse` |
| a request, lower term | ignored (P7) | none | the reply as a phantom |
| any, higher term, not a vote | `becomeFollower`, then as above | `BecomeFollower` (skipped) and the above | `UpdateTerm` and the above, at the receive line |

Outside `Step`: `Tick` at a follower or candidate (`campaign`: `BecomeCandidate`, the self vote
`SendRequestVoteResponse i→i`, `SendRequestVoteRequest`×n), at a leader (`bcastHeartbeat`:
`SendAppendEntriesRequest` heartbeats); `Propose` at a leader (`appendEntry`: `Replicate`, the self
acknowledgement, `bcastAppend`); the application's `ApplyConfChange` of the bootstrap entries
(after a node's first `Ready`: an `ApplyConfChange` line, at a leader also `Commit` and `MsgApp`
lines, `raft.go:2011-2028`); `Ready` (`acceptReady`: the `Ready` line); `Advance` (the
self-addressed messages' receipts).

### `becomeLeader`'s tally

`becomeLeader` clears the vote tally (`reset`, `raft.go:812`) before `traceBecomeLeader`, so at the
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
   `MaybeDecrTo`, `MaybeUpdate`, `initProgress`; `prevIndex = Next − 1`) and `e ≤ Len(log[i]) + 1`.
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

- `MoreThanOneLeaderInv`, `ElectionSafetyInv` need an invariant over every record of a granted
  vote (`votedFor` is forgotten when the term changes): a vote-record invariant on `σ`'s messages
  and servers, `VotesOk` (a granted vote of term `T` by `j` is unique), maintained through `R` from
  raft's `isVote_agree`, plus `isLeader_unique`;
- `LogInv`, `QuorumLogInv`, `MoreUpToDateCorrectInv`, `LeaderCompletenessInv`,
  `CommittedIsDurableInv` (a leader's commit index is within its durable log: the leader's own
  match is set by `becomeLeader` (`raft.go:820-821`) to its last index, persisted or not, so the
  proof needs leader completeness and the persistence order, not the self-response) are raft's
  safety theorems: route (a) from `isCommitted_agree`, `lc_core`, `cq_agree`, the leader's log
  records;
- `LogMatchingInv` from `logRecs_agree`/`plog_match_down`;
- at a receive line's truncation states (`ConflictAppendEntriesRequest` drops one entry at a time):
  `QuorumLogInv` and `MoreUpToDateCorrectInv` each need a lemma (a truncation removes only entries
  past the follower's commit index, which no committed prefix needs; a shorter log is not more up
  to date), and the others are preserved by a truncation outright.

So route (a), with `R` extended by the facts each needs, and per-action preservation lemmas for the
specification's intermediate states. This is the largest part of layer B's proof; S5's estimate
starts here.

## Premises (layer B's), discharged by layer D

- **P1** no restart (`InitState` only at bootstrap: gap 1);
- **P2** no compaction, so no snapshot (`MsgSnap` never sent: gap 3);
- **P3** no configuration change but the bootstrap's (gaps 2, 4; the application applies the
  bootstrap entries' `ConfChange`s, logged `ApplyConfChange`; `FullCConfig`'s changes are not in
  `Main`);
- **P4** the bootstrap first: every node's `StartNode` (its bootstrap lines, `InitState`,
  `BecomeFollower`, `ApplyConfChange`) before any other line (`newTrace`'s `bootstrapOf`), and a
  node's bootstrap log the `C` of `entAbs`;
- **P5** (gap 5) the configuration: `MaxSizePerMsg` unlimited (`^uint64(0)`; raft's `noLimit`: a
  batch is never cut, while Goose's semantics, which ignores delays, allows unboundedly many
  elections, so an unboundedly long log) and `MaxInflightMsgs` above the entries a leader appends
  in one term (256 against at most `Proposals` + 1 + the bootstrap's; in `StateReplicate` each
  `MsgApp` with entries carries entries not sent before, and `reset`/`BecomeProbe` empty the
  inflights), so no `MsgApp` is throttled or cut and each carries `Commit ≤ Index + len(Entries)`;
- **P6** no message duplicated by the network;
- **P7** pre-vote, check-quorum, read-index and leader transfer off, `AsyncStorageWrites` off (the
  harness's `Config` and workload): no `MsgPreVote` (whose campaign the specification has no
  action for), no reply to a stale request (the phantoms), no lease or read-index state; every
  proposal a normal entry;
- **P8** (F1) a message is received only after its sender's `Ready` line: the harness sends a
  `Ready`'s messages after `Advance`, which the run loop takes only after `acceptReady` has logged
  the `Ready` (`concurrent.go`'s `app`; Q3 of the plan; `nonissues/raft-trace-ready-logged-after-handout.md`);
- **P9** (gap 6) at most three voters (`DefaultCConfig.Nodes = 3`): a voter that learned its
  term's leader without voting refuses a vote the specification grants, impossible with three.

## Increment 2 of the hooks' specs (what S4 decides)

`TraceLoggerOk tl` (a `Prop`) becomes `isTraceLogger γt tl` (an `IProp` with a ghost name): `tl`
nil, or a logger whose `TraceEvent(ev)` is a logically atomic update `simStep γt i ev` over the
simulation's invariant: from `simNode γt i (a, P)` (and, at a receive line, `inFlight γt m`), given
that `ev` is the event of the node's state as `R` relates it (`ev = eventOf …`, the hook's
computation: term, vote, commit, role, log size, configuration, the message), it appends `ev` to
`L`, steps `σ` to its unique successor, and returns `simNode γt i (a', P')` (and, at a `Ready`
line, the new messages' `inFlight` tokens). So the statements that carry `TraceLoggerOk` change
again, the constructors' premise (Q1) included: `isTraceLogger γt cv.TraceLogger'` in the
precondition, with `γt` a new binder; `isTraceLogger_nil` gives it for a nil logger with any `γt`,
and `simNode` is owned only when the logger is not nil, so nil-logger clients carry nothing new.
Each hook's spec takes the node's `simNode` and the phase facts its call site holds; `Step`'s
branches carry the handling phase.

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
