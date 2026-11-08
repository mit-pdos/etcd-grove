# Raft's TLA+ trace validation, by TLC and by porcupine (branch `trace-check`, 2026-11-08)

The verified raft (the fork `565c2bd`, `etc/goose.py`'s project `raft`) built with raft's own
`with_tla` tag logs its state-machine events (`state_trace.go`); upstream checks such traces
against its TLA+ specification with TLC (`tla/etcdraft.tla`, the trace specification
`tla/Traceetcdraft.tla`, `tla/validate.sh`). This branch records such traces from an in-process
cluster and checks them three ways: by TLC, as upstream does; by a Go transcription of the two
TLA+ modules, directly; and by porcupine with that transcription as its model. The aim (discussed
2026-11-07/08): a closed result in this repository's porcupine style, "every trace of the verified
raft matches a behavior of etcdraft.tla", whose statement mentions only upstream's specification,
with porcupine the (verified) checker.

Nothing here is translated or proved yet. Plain Go and TLC only.

## What there is

- `examples/raft/tracecheck/sim.go` (`//go:build with_tla`): a seeded, single-threaded driver of a
  cluster of `RawNode`s (bootstrapped as `StartNode` does), recording raft's `TracingEvent`s
  through a `TraceLogger`, and writing them as NDJSON in upstream's format (`validate.sh` reads it).
  Random actions: tick, deliver or drop an in-flight message (reordered, never duplicated: the
  specification's network is a bag whose messages are received at most once), propose, propose a
  configuration change, restart, handle a `Ready`. Always off: pre-vote, check-quorum, read-index,
  leadership transfer, joint configurations (none modelled). `DefaultConfig`: three voters, no
  configuration change, snapshot or restart; `FullConfig`: a fourth node, configuration changes the
  specification models, snapshots (every 5 applied entries and after each configuration change).
- `examples/raft/tracecheck/concurrent.go` (`//go:build with_tla`): the concurrent harness, the
  one to prove. Each replica is a `raft.Node` (node.go's run goroutine; `StartNode`, a member to
  add `RestartNode` on empty storage) with an application goroutine that ticks it, handles its
  Readies and advances it; the network delivers each message from a goroutine of its own after a
  random delay (reordered), through `Node.Step` with a timeout, or drops it; a proposer, a
  proposer of configuration changes (at the leader, those the specification models) and an
  isolator (cuts a random replica off the network for a while: leader changes) run concurrently.
  One locked `SyncRecorder` orders the events. That order is one the trace specification can
  follow: a replica's events are logged from its run goroutine, one at a time; a message is
  logged as sent (in raft's `send`) before the Ready that hands it out, and (since 2026-11-08) the
  application sends a Ready's messages only after `Advance`, which raft takes once that Ready is
  logged, so its receipt is logged after the sender's Ready line (sending before `Advance` let a
  receipt precede it: `nonissues/raft-trace-ready-logged-after-handout.md`). `DefaultCConfig` runs (8 seeds, under `-race`): 1.7k-2.7k events, 4-11
  candidacies, 2-3 leaders, terms to 8, all matched. Raft's `with_tla` build sleeps 1ms in every
  traced receipt (`traceReceiveMessage`, "to reduce time shift impact across node": for ordering
  by timestamps across processes), so the harness ticks every 10ms (at 2ms a leader's run loop
  fell behind and a third of the messages timed out).
- `examples/raft/tracecheck/etcdraft/` (plain Go, no dependency on raft): the transcription,
  definition by definition with the TLA+ names in the comments.
  - `types.go`, `spec.go`, `invariants.go`: all of `etcdraft.tla` -- every variable, `Init`, every
    action (`Restart`, `Timeout`, `RequestVote`, `AppendEntriesInRangeToPeer` and its three uses,
    `AppendEntriesToSelf`, `BecomeLeader`, `ClientRequest`, `AdvanceCommitIndex`, `AddNewServer`,
    `AddLearner`, `DeleteServer`, `ApplySimpleConfChange`, `Ready`, `StepDownToFollower`, every
    message handler, `DuplicateMessage`, `DropMessage`), the next-state relations (`NextAsync`,
    `NextCrash`, `NextUnreliable`, `Next`, `NextDynamic`) and every invariant.
  - `trace.go`: all of `Traceetcdraft.tla` -- the constants it derives from the trace
    (`TraceServer`, `BootstrapLogIndices`, `LastBootstrapLog`, `TraceInit`), every `...IfLogged`
    action with its pre- and post-state validation, `SkipUnusedLogline`, `TraceNext` (a received
    message's line in one or more steps, `StepToNextTraceIfMessageIsProcessed`).
  - `check.go`: `CheckTrace`, TLC's breadth-first search with the view `<<vars, l>>` and the
    invariants `Traceetcdraft.cfg` checks; `Model`/`History`/`CheckPorcupine`, the trace
    specification as a porcupine `NondeterministicModel` (an operation per line, input the line
    number, the lines totally ordered), checked through `ToModel`; `Explain`.
  - Where TLC stops with an evaluation error, the transcription raises one (`EvalError`, reported
    as `Result.EvalError`): `SubSeq` past a sequence's end, `SelectLastInSubSeq` past the log's end
    (`ApplySimpleConfChange`), `log[l][idx]` past a leader's log (`LeaderCompletenessInv`). The
    reader is strict where TLC would fail reading the trace: exact, case-sensitive keys (`prop`'s
    are free but for `cc`), a message line without `msg`, a message type outside `RaftMsgType`, a
    `ChangeConf` without `cc` or with an empty change list, a last bootstrap line without
    `newconf`, ids not in canonical form. Role strings are values of their own (raft's
    `StatePreCandidate` equals none of the three).
  - `CheckTrace`'s `OK` is "some behavior matches", the property `TraceMatched` states; TLC's check
    of it (`TLCGet("queue") = 1`) fails as soon as the breadth-first search branches, even where
    every branch matches. `Result.Branched` records the first line where a state has more than one
    new successor, and `Result.TLCOK()` (OK and never branched) is TLC's verdict, which the tests
    require. No trace recorded so far branches. Invariants are checked at every state reached,
    the intermediate steps of a received message's line included (as TLC checks every new state).
    The porcupine model fails a line on a violation or an evaluation error; its verdict is `OK`'s.
  - Reviewed 2026-11-08 by an independent subagent, definition by definition against the TLA+
    text: `etcdraft.tla`'s transcription faithful; the trace layer faithful on raft's traces; the
    checker's three differences from TLC (the strict `TraceMatched`, the view leaving out `pl`,
    invariants on intermediate states) and five places where TLC errors but the code went on (an
    absent `newconf`, unknown roles merged, `SubSeq` clamped, lenient JSON, and smaller ones) are
    the fixes above, each with a regression test (`etcdraft/strict_test.go`, from the reviewer's
    witnesses). (The view leaving out `pl`: Go keeps a state TLC drops; that needs two states at a
    line, which `Branched` reports.)
- `examples/raft/tracecheck/cmd/checktrace`: checks NDJSON files (`-explain` prints the states
  before a failing line and the messages in transit to its node).

## How it is checked

- `go test ./raft/tracecheck/etcdraft/` (in `examples/`): `TestStateSpaceMatchesTLC` explores
  `Init /\ [][NextDynamic]_vars` of the Go transcription under the bounds of
  `etcdraft/testdata/MCGo.tla` and compares the number of distinct states with TLC's on
  `etcdraft.tla` itself (`MCGo-{b,d,e,h}.cfg`, counts recorded in the test): 17930, 149307, 25569
  (three servers, one joining), 330653 (terms to 2: conflicting logs, truncation). All equal, no
  invariant violated. (TLC leaves a successor violating `CONSTRAINT` out of the count.) Every
  action is in `NextDynamic`, so the two next-state relations agree on what they reach there.
- `go test -tags with_tla ./raft/tracecheck/`: `TestTracesCheck`, the `DefaultConfig` traces of
  seeds 1-20 are matched, by the direct checker and by porcupine (each about 50-100 ms for
  1-2.5k events; TLC takes about 7 s).
- `TestAgainstTLC` (needs `TLA_TOOLS`, a directory with `tla2tools.jar` and
  `CommunityModules-deps.jar`, and `TLA_SPEC`, the fork's `tla/`; skipped otherwise): TLC, the
  direct checker and porcupine on the traces of `TLC_SEEDS` seeds, `TLC_MUTANTS` mutants of each
  (a logged value changed, a line deleted, two lines swapped) and each seed's `FullConfig` trace.
  2026-11-08, 6 seeds and 10 mutants: 72 traces, the verdicts agree on all 72 (31 rejected), and
  where TLC rejects, its error trace stops at the line the direct checker reports. With the
  concurrent harness's traces added (`DefaultCConfig` and `FullCConfig` per seed), 5 seeds and 8
  mutants: 60 traces, all agree (23 rejected).
- `TestConcurrentTraces` (`-race`): the `DefaultCConfig` traces of seeds 1-10 are matched, by the
  direct checker and by porcupine.

Setup used: Java 21 (`apt install default-jre-headless`), upstream's tools as `validate.sh` fetches
them (nightly `tla2tools.jar`, latest `CommunityModules-deps.jar`; not pinned yet).

## Where etcdraft.tla does not fit raft

Found with `FullConfig` and restarts; TLC and the Go transcription reject at the same line in
every case, so these are about the specification (or how raft logs), not the transcription. Raft
is right in each.

1. **Restarts cannot be matched.** `newRaft` logs `InitState` (`traceInitState`) before it restores
   the configuration and loads the hard state, so the line has term 0, commit 0, an empty
   configuration; `RestartIfLogged` checks that line against the restarted state
   (`ValidatePostStates`). Harmless at bootstrap (bootstrap lines are not validated); a restart
   mid-trace never matches. `Config.Restarts` stays in the harness, off in `FullConfig`.
2. **No demotion of a voter to a learner.** `AddLearner(i, j)` requires `j \notin GetConfig(i)
   \union GetLearners(i)`; raft accepts `ConfChangeAddLearnerNode` of a voter. The harness proposes
   only changes the specification models.
3. **A snapshot to a follower that has committed anything is not modelled.** A `MsgSnap` is an
   append request with `mprevLogIndex = 0`, so `index = 1`; when the follower's `commitIndex >= 1`,
   `AppendEntriesAlreadyDone` is the only enabled handler (`ConflictAppendEntriesRequest` and
   `NoConflictAppendEntriesRequest` need `index > commitIndex[i]`), and for a non-heartbeat it
   changes neither the log nor the commit index. Raft either installs the snapshot (log and commit
   to its index) or, when the follower has the snapshot's last entry, fast-forwards its commit index
   to it (`raft.restore`). Either way the follower's next validated line differs. A member that has
   committed nothing (a newcomer) gets the snapshot's entries, but its response cannot be matched
   either (corrected 2026-11-08: the earlier note said the specification follows it):
   `AppendEntriesAlreadyDone` replies with subtype `"snapshot"`, where raft's `MsgAppResp` maps to
   `"app"` (10 below).
4. **A re-added member's `matchIndex` is not reset.** Raft drops a removed member's progress, and a
   member added back starts at `Match` 0, so a heartbeat to it carries commit `min(Match,
   committed) = 0`; the specification keeps `matchIndex[i][j]` from before the removal and
   expects `Min(commitIndex[i], matchIndex[i][j])`.
5. **An append request's commit index is not clamped to what it carries** (found 2026-11-08 by
   Draft S4's case analysis, then witnessed). `AppendEntriesInRangeToPeer` sends
   `mcommitIndex = Min(commitIndex[i], lastEntry)`, `lastEntry` the last index the request carries;
   raft's `maybeSendAppend` sends `Commit: r.raftLog.committed` whatever it carries (the follower
   clamps it, `min(m.Commit, lastnewi)`). They differ when the request stops short of the leader's
   commit index: an empty `MsgApp` of a throttled `StateReplicate` (`Inflights.Full()`) to a
   follower behind the commit index, or a batch cut by `MaxSizePerMsg`. The concurrent harness with
   `MaxInflightMsgs: 1` (a scratch copy, not committed) fails on 2 of 6 seeds, TLC's and the
   transcription's verdicts alike (seed 5, line 1011: `MsgApp` `index` 22, `entries` 0, `commit`
   23). The concurrent harness now sets `MaxSizePerMsg` unlimited (no batch is ever cut: under
   Goose's semantics elections, and so the log, are unbounded), and 256 inflights exceed what a
   leader appends in a term (60 proposals and its empty entry), so it never throttles.
6. **A voter that knows its term's leader refuses a vote the specification grants** (found
   2026-11-08 by the review of Draft S4, witnessed with five voters). Raft's `canVote`
   (`raft.go:1232-1235`) needs `r.Vote == m.From` or `r.Vote == None && r.lead == None`: a follower
   that learned the term-`T` leader from its heartbeat without voting refuses a second term-`T`
   candidate, and also the term-`T` leader's own `MsgVote` when it arrives after the leader's first
   heartbeat (delayed: the network reorders); `HandleRequestVoteRequest` grants (`votedFor = Nil`)
   and has no `lead`. Three voters do not prevent it (round 2 of the review: node 1 wins term 2
   with node 2's vote, node 3 gets node 1's heartbeat, then node 1's delayed `MsgVote`); a network
   delivering each link's messages in order would, with three voters. Witnessed: `gaps_test.go`,
   `TestGap6FiveVoters` (another candidate), `TestGap6ThreeVoters` (the leader's own vote; TLC
   rejects at the same line).
7. **`LeaderCompletenessInv` is not an invariant of raft (nor of `etcdraft.tla`)** (found
   2026-11-08 by round 2 of the S4 review). The invariant (`etcdraft.tla`) asks every current
   leader whose term exceeds an entry's term to hold every committed entry; raft guarantees it
   only of leaders elected after the commit. A stale leader breaks it: node 1 leads term 2, its
   entry at index 4 (term 2) reaches no one; node 2 leads term 3, appends its own entry at 4, and
   stays leader of term 3 (no check-quorum: nothing tells it of a later term); node 1 leads term 4
   and commits index 5, so index 4's term-2 entry, which leader 2 does not hold. Message delays
   alone reach it, so no harness excludes it. TLC: `Invariant LeaderCompletenessInv is violated`;
   `gaps_test.go`, `TestGap7LeaderCompleteness`. A guard on the leader's term relative to the
   committing server's (`currentTerm[l] >= currentTerm[i]`) is the repair both transcriptions now
   check (2026-11-08, the user's decision: `notes/trace-validation-plan.md`, Q4). Upstream:
   etcd-io/raft#549 (open); our report, with a test through upstream's own `with_tla` build and
   `Traceetcdraft`: `issues/raft-tla-leader-completeness-stale-leader.md`. The specification alone
   admits the violation: TLC's counterexample replays against `MCetcdraft` from its `Init`, each
   step a `Next` step (a script extracting the states from TLC's output into a module extending
   `MCetcdraft`, `Init` then `Next \/ UNCHANGED vars` forced onto each recorded state, deadlock
   checking on; one corrupted state deadlocks).
8. **`MoreUpToDateCorrectInv` is not an invariant of raft either** (found 2026-11-08 by round 3 of
   the S4 review). It asks that a server whose log is at least as up to date as `j`'s hold `j`'s
   committed prefix; but a follower can learn its commit index from a heartbeat
   (`min(Match, committed)`) while its log ends at an old-term entry another server's newer-term log
   lacks. Reached with five voters and batches cut to one entry (`MaxSizePerMsg` 1): TLC,
   "Invariant MoreUpToDateCorrectInv is violated"; `gaps_test.go`, `TestGap8MoreUpToDate`. Not
   reached when every `MsgApp` carries the leader's log to its end (unlimited batches, the
   concurrent harness's), where a follower's commit index never passes what it received from a
   leader with its own last term.

9. **`Restart` cannot be evaluated after a conflicting append request** (found 2026-11-08 while
   replaying item 8's counterexample against `MCetcdraft`): `ConflictAppendEntriesRequest` drops
   the last entry without persisting, `Restart` takes `SubSeq(log[i], 1, durableState[i].log)` past
   the shorter log, and TLC stops evaluating `Next`. Model checking with crashes only; trace
   validation is unaffected.

10. **A snapshot's response has the wrong subtype** (found 2026-11-08 while writing up 3): the
    specification answers a snapshot with an append response of subtype `"snapshot"`; raft answers
    with a `MsgAppResp`, which `Traceetcdraft` maps to `"app"`, so even a newcomer's snapshot is not
    followed.

**Written up (2026-11-08)**, each with a test at raft `main` `c51f010` (copied into its module root,
`-tags with_tla`, TLC on upstream's unmodified files): `issues/raft-tla-restart-initstate-unmatched`
(1), `-learner-demotion-unmodelled` (2), `-snapshot-committed-follower` (3),
`-readded-member-matchindex` (4), `-msgapp-commit-unclamped` (5), `-vote-refused-known-leader` (6),
`-leader-completeness-stale-leader` (7), `-more-up-to-date-cut-batches` (8),
`-restart-truncated-log` (9), `-snapshot-response-subtype` (10). For the invariants (7, 8) a second test replays TLC's counterexample
against `MCetcdraft` alone (`Init`, then each recorded state forced as a `NextAsync` step or a
stutter, deadlock checking on), showing the specification itself reaches the violation.

Also met, and avoided by the harness as etcd does: a snapshot without the recipient in its
configuration, which raft drops (`nonissues/raft-snapshot-without-recipient-livelock.md`) while
the specification installs it; `FullConfig` snapshots after applying each configuration change.

None of these is a bug in the verified Go code (items 7 and 8 are bugs in the specification's invariants). Items 1, 3, 4, 5, 6, 7 and 8 make upstream's trace validation
unable to check traces with restarts, snapshots to lagging followers, or members removed and
added back; whether to propose fixes to `etcdraft.tla`/`Traceetcdraft.tla` upstream (3: commit, and
install, on a snapshot whatever the follower's commit; 4: reset `matchIndex` on removal; 5: send `commitIndex[i]` (the follower already clamps, `AppendEntriesAlreadyDone`); 6: add raft's `lead` to the vote condition; 7: guard `LeaderCompletenessInv` by the leader's term; 1: log
`InitState` after `loadState`, or validate a restart's later lines) is open.

## Raft translated with its trace hooks (2026-11-08)

Goose builds with the tag `goose` only (its package loader's `-tags goose`), so the fork commit
`e8f9566` (`etc/fork-patches/raft-trace-tags.patch`, not pushed: no write access to
`upamanyus/etcd` yet) puts the hooks' bodies under `with_tla || goose`: a two-line change of build
constraints, no code. The raft translation on `trace-check` is generated from it
(`etc/fork-patches/README.md`); `etc/goose.py`'s pin stays `565c2bd` until the commit is pushed, so
`--check` fails for raft on this branch and it cannot land. What is verified then is raft's
`with_tla` build, where etcd ships the no-op build: the two differ in the hooks' bodies and
`Config.TraceLogger`'s type, and with no logger (every caller but a trace harness) the hooks return
at once; that equivalence is argued, not proved.

The trial build (`lake build Proof.go_etcd_io.raft.v3.Results`): 2997 of 3010 targets built; only
the eleven hooks' proofs fail (their specs say "a no-op"); every caller, proved against the hooks'
specs, builds. Goose dry runs: the concurrent harness translates as is, the transcription after
two changes (named types for the event's records, function literals for the invariants' table).

## Next

The checker to prove is the direct one (decided 2026-11-08): the traces are totally ordered (one
process, one locked recorder: the setting of upstream's own validation, one machine and one file,
without its reliance on timestamps), so porcupine's search reduces to `CheckTrace`'s loop, which
is shorter to verify than `ToModel` and porcupine's spec, and reports more (the invariant, the
failing line, `Explain`). Porcupine stays a cross-check, and the route for traces without a global
order (separate processes), which no proof here states.

- Translate raft with `with_tla` (`etc/goose.py` has no build tags yet), and strengthen the eleven
  trace hooks' specs (`Spec/go_etcd_io/raft/v3/trace*.lean`, now no-ops) to report the event;
  `traceReceiveMessage`'s `time.Sleep`.
- The concurrent harness, proved to produce a log in a valid order (each replica's events in
  program order, each message's send before its receipt).
- A Lean transcription of the two modules; `StepLine` proved to refine it; `CheckTrace`'s loop
  proved sound and complete; the simulation from `StepR`.
- Pin the TLA+ tools' versions.
