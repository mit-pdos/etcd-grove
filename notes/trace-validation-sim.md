# Draft S4: the simulation on paper (2026-11-08)

Part of `notes/trace-validation-plan.md` (layer B; Draft S4, "the simulation on paper": `R`, each
hook's correspondence, determinism, the invariants' mapping). It decides what increment 2 of the
hooks' specs is (`notes/trace-validation-hooks.md`: the logger's contract) and what layer D must
discharge. Not yet reviewed (Review: a fresh `spec-reviewer` round on this note and the hooks'
specs together).

The specification side is the Lean transcription
(`Proof/github_com/mit_pdos/etcd_grove/examples/raft/tracecheck/etcdraft/Tla/`): `State` (`σ`: per
server `currentTerm`, `state`, `votedFor`, `log`, `commitIndex`, `votesResponded`, `votesGranted`,
`matchIndex`, `pendingConfChangeIndex`, `config`, `durable`; the bags `pendingMessages`,
`messages`; `reconfigCount`), `Trace.stepLine`, `checkTrace`, `traceAccepts`. The raft side is the
existing proof's (`notes/STATUS.md`; the survey below).

## What the statement needs

`traceAccepts events` = `(checkTrace t true).tlcOK`: from `t.initState`, every line has **exactly
one** successor state up to TLC's view (`stepLine` returns one state and `branched` stays false:
no state reached *inside* a line, a receive line's intermediate states included, has two fresh
successors), no state reached violates the eight invariants, and nothing fails evaluating. So the
simulation is a functional one: an abstraction `α` of the cluster's state, with
`stepLine t ⟨α(before), l, pl⟩ = ([⟨α(after), l+1, l⟩], {})` at every line, and `Inv (α …)` at
every state `stepLine` visits.

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

## The abstraction `α`

### A server

`α_i` maps node `i`'s state at a trace point to the specification's `Server`:

| specification | raft | note |
|---|---|---|
| `currentTerm` | `s.term` | |
| `state` | `s.role` (`StateFollower`/`Candidate`/`Leader`) | pre-vote off: no pre-candidate |
| `votedFor` | `s.vote` | |
| `log` | `entAbs` of each entry of `s.logst.sents ++ s.logst.uents` (no compaction: `prev` is index 0) | below |
| `commitIndex` | `s.logst.committed` | |
| `votesResponded`, `votesGranted` | `dom s.votes`, `{j | s.votes j = true}` while a candidate | a ghost copy otherwise (the specification keeps them after the election, raft's `reset` clears them; read only by `RequestVote`/`BecomeLeader`, which need a candidate) |
| `matchIndex` | `j ↦ pr(j).Match` while a leader | a ghost copy otherwise |
| `pendingConfChangeIndex` | `0` | no `ChangeConf` line in the workload |
| `config` | `⟨voters, [], []⟩` | |
| `durable` | `durableOf` of `α_i` at node `i`'s last `Ready` line | a ghost of the simulation, below |

`entAbs e = ⟨e.term, .value, .val 0⟩` for an entry after the bootstrap log (every one is a
`Replicate` line's `ClientRequest(i, 0)`: proposals and the leader's empty entry alike), and
`⟨1, .config, .conf C []⟩` for the bootstrap log's (`newTrace`'s `serverOf`), `C` the bootstrap
voters. The values carried by proposals are abstracted away: the specification's are all `0`.

### The messages

Only the traced types count (`traceSendMessage`'s switch: `MsgApp`, `MsgHeartbeat`, `MsgSnap`,
`MsgAppResp`, `MsgHeartbeatResp`, `MsgVote`, `MsgVoteResp`); the rest (`MsgProp`, `MsgHup`,
`MsgBeat`, `MsgReadIndex`, `MsgTimeoutNow`, `MsgUnreachable`, ...) are invisible to the
specification. `msgAbs` maps a traced raft message to the specification's `Msg`:
`MsgVote` to a request with `lastLogIndex := m.Index`, `lastLogTerm := m.LogTerm`; `MsgVoteResp`
to a response with `voteGranted := !m.Reject`; `MsgApp` to an append request of subtype `app`
(`prevLogIndex := m.Index`, `prevLogTerm := m.LogTerm`, `entries := entAbs <$> m.Entries`,
`commitIndex := m.Commit`), `MsgHeartbeat` subtype `heartbeat` (`commitIndex := m.Commit`, the
rest `0`/`[]`); `MsgAppResp` an append response of subtype `app` (`success := !m.Reject`,
`matchIndex := if m.Reject then 0 else m.Index`), `MsgHeartbeatResp` subtype `heartbeat`
(`success`, `matchIndex := 0`).

- `pendingMessages` = `msgAbs` of every node's traced messages sent and not yet handed out in a
  `Ready` (its outbox's traced messages; for the self-addressed ones, "Self-addressed messages"
  below);
- `messages` = `msgAbs` of the traced messages handed out and not yet received, **dropped ones
  included** (the specification's network never forgets one).

Since raft's proof has no record of the messages in flight, the bags are new ghost state of the
simulation: an authoritative bag in the simulation's invariant, and an exclusive token
`inFlight γt m` per handed-out traced message, created at the `Ready` line, owned by whoever holds
the message (the harness's network), consumed at its receive line. A dropped message's token is
thrown away (the bag keeps the message). **No duplication** is then a premise on the network: a
message delivered twice has one token (the specification's `DuplicateMessage` is not in
`TraceNext`). The concurrent harness never duplicates (layer D).

### Self-addressed messages

Raft's self-addressed messages (the candidate's own vote, `MsgVoteResp` to itself; the leader's
own append acknowledgement, `MsgAppResp` to itself) go through `msgsAfterAppend`, are traced as
sent (`SendRequestVoteResponse i→i`: `RequestVote(i, i)`; `SendAppendEntriesResponse i→i`:
`AppendEntriesToSelf(i)`), stay in the outbox past the `Ready` (`ownRaftGhost_cut` keeps them)
and are stepped at `Advance` (`stepsOnAdvance`), where they are traced as received. The
specification moves them to `messages` at the `Ready` line (`Ready(i)` moves every pending message
from `i`). So `messages` also holds the self-addressed responses kept for `Advance`, and their
tokens are owned by the node (`RawNode.stepsOnAdvance`) until `Advance` steps them.

## The relation and its phases

`σ` is cluster-wide, but every line is one node's event and its action touches only that node's
server, the messages it sends (`pendingMessages` from it), the one message it receives
(`messages`), and nothing else (`reconfigCount` and `server` are constant in the workload). So
`σ` is split: `simAuth γt σ L` (the whole state and the trace `L` so far) in the simulation's
invariant, `simNode γt i (a, d, P)` per node (its server `a`, its durable record `d`, its pending
messages `P`) owned by node `i`, `inFlight γt m` per message in `messages`.

`R_i(s, a)` cannot hold at every moment: raft's code updates its fields around the hooks, not at
them (`appendEntry` traces `Replicate` before the append; `maybeCommit`'s `Commit` is deferred to
its end; `becomeFollower` traces after `reset`; `Step` traces the receipt at its entry, before the
handling). It is a relation **at the hook points**, with a phase:

- **idle** (between two calls into raft): `a = α_i(s)`, `P = msgAbs` of the outbox's traced
  messages not yet handed out;
- **handling `m`** (inside `Step(m)`, after its `Receive*` line): the specification has done all of
  the handling at that line (`Receive` and its `UpdateTerm`, conflict truncations, the reply), so
  `a = handle(α_i(s_entry), msgAbs m)` while raft has not; each hook reached during the handling
  is checked against `a` updated by the lines logged since, and at `Step`'s return the phase is
  idle again: `α_i(s_exit) = a`.
- the hooks inside other calls (`Tick` → `campaign`, `Propose` → `appendEntry`, `Ready`,
  `Advance`) are each logged once their changes are made (or, for `Replicate`, *before*: the
  specification's `ClientRequest` appends at the line, raft right after, with nothing traced in
  between), so idle with a known pending change.

The **handling** phase is where the proof is: for each `raft.Step` branch (`StepCD`'s `StepR`
rule), the specification's handling of `msgAbs m` from `α_i(s_entry)` (the receive line's steps:
`UpdateTerm`, then the handler, then, for an append request, one `ConflictAppendEntriesRequest`
per conflicting entry and `NoConflictAppendEntriesRequest`) followed by the specification actions
of the lines raft logs inside the branch equals `α_i(s_exit)`. A pure lemma per `StepR` rule
(`spec_of_higherTerm`, `spec_of_appAccept`, ...), stated on `PState`, proved from the model's
definitions; then each `raft.Step` branch's proof composes them. The lines a branch logs, by rule:

| received | raft's branch | lines it logs after `Receive*` | their specification actions |
|---|---|---|---|
| `MsgVote`, higher term | `becomeFollower`, then vote | `BecomeFollower` (skipped: update term), `SendRequestVoteResponse i→j` (skipped) | none: the receive line did `UpdateTerm` and `HandleRequestVoteRequest` |
| `MsgVoteResp` at a candidate | `poll`: win, lose, wait | win: `BecomeLeader`, `Replicate`, `SendAppendEntriesResponse i→i`, `SendAppendEntriesRequest`×n; lose: `BecomeFollower` | `BecomeLeader`, `ClientRequest`, `AppendEntriesToSelf`, `AppendEntries`/`Heartbeat`; `StepDownToFollower` |
| `MsgApp`/`MsgHeartbeat` at a follower | append or reject, commit | `SendAppendEntriesResponse i→j` (skipped) | none |
| `MsgApp` at a candidate, same term | `becomeFollower`, then as a follower | `BecomeFollower` (skipped: return to follower) | none |
| `MsgAppResp` at a leader | `MaybeUpdate`, `maybeCommit`, sends | `Commit`, `SendAppendEntriesRequest`×k | `AdvanceCommitIndex`, `AppendEntries` |
| `MsgHeartbeatResp` at a leader | sends if behind | `SendAppendEntriesRequest` | `AppendEntries` |
| any, lower term | ignore or reject | maybe a response (skipped) | `DropStaleResponse`/`RejectAppendEntriesRequest` at the receive line |

## Determinism (no branching)

At every line, the specification's successor is unique. By line kind:

1. **Node events** (`BecomeCandidate`, `BecomeLeader`, `Replicate`, `Commit`, `Ready`,
   `BecomeFollower` not skipped): the line names its node, the action is a function of `σ`.
   `BecomeFollower`: exactly one of `SkipUnusedLogline` (update term or return to follower: the
   node's previous line is the receive that caused it) and `StepDownToFollower` applies.
2. **`SendAppendEntriesRequest`, `MsgApp`**: `AppendEntriesIfLogged(i, j, b, e)` with
   `b = index + 1`, `e = b + entries`, so `(i, j, b, e)` is fixed; it needs
   `matchIndex[i][j] + 1 ≤ b` (raft: `pr.Next > pr.Match`, so `prevIndex = Next − 1 ≥ Match`) and
   `e ≤ Len(log[i]) + 1`. Its `ValidatePostStates` and its message's commit need **raft's
   `Commit` equal to `Min(commitIndex, lastEntry)`**: false in general (gap 5 of
   `notes/raft-trace-validation.md`): a premise (P5 below).
3. **`MsgHeartbeat`**: `commit = Min(commitIndex[i], matchIndex[i][j])`: raft's heartbeat commit
   is `min(pr.Match, committed)` (`sendHeartbeat`): equal under `R`.
4. **Sends with `from ≠ to` of responses** (`SendAppendEntriesResponse`,
   `SendRequestVoteResponse`): skipped, and no other action applies (the self actions need
   `from = to`).
5. **Receive lines**: the line fixes the message up to the fields it logs, so it selects one
   message of `messages` provided **any two messages in `messages` agreeing on the logged fields
   are equal** (a `σ` invariant, `MsgsDet`). By type: a vote request logs every field (term,
   from, to, index, logTerm); a vote response logs every field (term, granted); a heartbeat logs
   its commit, and its other fields are constant; an append response logs `success` and, unless a
   rejection or a heartbeat response, `matchIndex`, and the specification sets the other cases'
   `matchIndex` to 0; an append request logs everything but its entries' terms (their number is
   logged), and two append requests of the same term from the same leader with the same
   `prevLogIndex` and number of entries carry the same entries: **the entries a leader of term `T`
   sends are a slice of its log, which is append-only during `T`** (raft: `isLeader_unique`,
   `leadPrefix_agree`, `logRecs_agree`), a second `σ` invariant on the bags (`AppSlices`: every
   append request of term `T` carries a slice of the term-`T` leader's log at its index).
6. **Inside a receive line** (the states with `pl = l`): at each, exactly one of the handlers is
   enabled (`UpdateTerm` needs a higher term, the handlers a term at most the server's;
   `Reject`/`ReturnToFollower`/`Accept` are exclusive; within `Accept`,
   `AppendEntriesAlreadyDone`, `Conflict`, `NoConflict` are exclusive but for
   `NoConflict`-with-everything-present, whose successor is the state itself and so not fresh),
   and the loop ends (`lineFuel`).

## The invariants

`Traceetcdraft.cfg`'s eight, at every state `stepLine` visits (the intermediate states of a
receive line included): `LogInv`, `MoreThanOneLeaderInv`, `ElectionSafetyInv`, `LogMatchingInv`,
`QuorumLogInv`, `MoreUpToDateCorrectInv`, `LeaderCompletenessInv`, `CommittedIsDurableInv`.

They are about `σ`, which during a handling phase is ahead of raft. Two routes:

- (a) **from raft's ghost facts through `R`**: each invariant restated on the nodes' `PState`s and
  proved from `isCommitted_agree` (`LogInv`), `isLeader_unique` (`MoreThanOneLeaderInv`), the
  leader's log records (`ElectionSafetyInv`, `LogMatchingInv`), `lc_core` (`LeaderCompletenessInv`,
  `QuorumLogInv`); the node mid-handling contributes `handle(α_i(s_entry), m)`, which raft reaches
  by `Step`'s end, so its facts are those of the post-state, available only after the handling
  (a ghost prophecy of the branch's outcome, or the facts proved for the specification's handled
  state directly);
- (b) **as inductive invariants of the specification**: each a property of `σ` preserved by every
  specification action, proved once on the Lean transcription, independent of raft.

Recommendation: (b) for the four that are inductive with light strengthening
(`MoreThanOneLeaderInv` and `ElectionSafetyInv` need the vote records: strengthened by "a granted
vote of term `T` is unique", which the bags' `MsgsDet` and `votedFor` give; `CommittedIsDurableInv`
by the `Ready`/`Advance` ordering: the leader counts its own match only from its self-response,
received after the `Ready` that persisted the entries); (a) for `LogInv`, `QuorumLogInv`,
`MoreUpToDateCorrectInv`, `LeaderCompletenessInv`, which are raft's safety theorems and whose
specification-level proofs are a Raft proof of their own. Open: route (a)'s mid-handling case; the
simplest is to check the invariants at the receive line's *final* state only, from raft's
post-state, and at its intermediate states by (b)-style preservation from the line's start.

## Premises (layer B's), discharged by layer D

- **P1** no restart (`InitState` only at bootstrap: gap 1);
- **P2** no compaction, so no snapshot (`MsgSnap` never sent: gap 3);
- **P3** no configuration change after the bootstrap (gaps 2, 4; `FullCConfig`'s changes are not
  in `Main`);
- **P4** the bootstrap first: every node's `StartNode` (its bootstrap lines, `InitState`,
  `BecomeFollower`, `ApplyConfChange`) before any other line (`newTrace`'s `bootstrapOf`), and a
  node's bootstrap log the `C` of `entAbs`;
- **P5** (new, gap 5) every `MsgApp` raft sends carries `Commit ≤ Index + len(Entries)`: raft sends
  `committed`; it holds when no `MsgApp` is throttled (`Inflights.Full()`: `MaxInflightMsgs` more
  than the entries a leader appends in one term, 256 against at most `Proposals` + 1) nor cut by
  `MaxSizePerMsg` (1 MiB against the workload's entries). Witnessed false with
  `MaxInflightMsgs: 1`;
- **P6** no message duplicated by the network (above);
- **P7** pre-vote, check-quorum, read-index and leader transfer off (the harness's `Config` and
  workload): no `MsgPreVote` (whose campaign the specification has no action for), no lease or
  read-index state; every proposal a normal entry. (A `MsgTimeoutNow` campaign would still be
  traced by `campaign`'s `BecomeCandidate`; it does not occur.)

## Increment 2 of the hooks' specs (what S4 decides)

`TraceLoggerOk tl` becomes `isTraceLogger γt tl`: `tl` nil, or a logger whose `TraceEvent(ev)` is a
logically atomic update `simStep γt i ev` over the simulation's invariant: from `simNode γt i
(a, d, P)` (and, at a receive line, `inFlight γt m`), given that `ev` is the event of the node's
state as `R` relates it (`ev = eventOf …`, the hook's computation: term, vote, commit, role, log
size, configuration, the message), it appends `ev` to `L`, steps `σ` to its unique successor, and
returns `simNode γt i (a', d', P')`. Each hook's spec takes the node's `simNode` and the phase
facts its call site holds; raft's invariant (`ownRaftPhys`) carries `simNode γt id …` with `R` in
the idle phase; `Step`'s branches carry the handling phase. Every existing client keeps the nil
case (`isTraceLogger_nil`).

## Open (for the Review)

- The handling phase's statement inside `raft__Step`'s 36 branches (one shape per branch kind,
  `wp_trace_hookC`'s successor) and how much of `StepCD` it reuses.
- Route (a)'s mid-handling invariants.
- Whether `simNode` lives in `ownRaftPhys` (every raft proof sees it) or beside it in
  `ownRawNode` (only the hooks' call sites thread it, as the logger field now).
