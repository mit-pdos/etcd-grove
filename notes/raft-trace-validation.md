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
  - Deviations from TLC, where TLC would fail evaluating: `SubSeq` past a sequence's end keeps what
    exists; `LeaderCompletenessInv` is false where `log[l][idx]` does not exist; an unknown message
    type in a line matches no message. None is reached by the traces checked.
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
  where TLC rejects, its error trace stops at the line the direct checker reports.

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
   to it (`raft.restore`). Either way the follower's next validated line differs. Only a member
   that has committed nothing (a newcomer) receives a snapshot the specification can follow.
4. **A re-added member's `matchIndex` is not reset.** Raft drops a removed member's progress, and a
   member added back starts at `Match` 0, so a heartbeat to it carries commit `min(Match,
   committed) = 0`; the specification keeps `matchIndex[i][j]` from before the removal and
   expects `Min(commitIndex[i], matchIndex[i][j])`.

Also met, and avoided by the harness as etcd does: a snapshot without the recipient in its
configuration, which raft drops (`nonissues/raft-snapshot-without-recipient-livelock.md`) while
the specification installs it; `FullConfig` snapshots after applying each configuration change.

None of these is a bug in the verified Go code. Items 1, 3 and 4 make upstream's trace validation
unable to check traces with restarts, snapshots to lagging followers, or members removed and
added back; whether to propose fixes to `etcdraft.tla`/`Traceetcdraft.tla` upstream (3: commit, and
install, on a snapshot whatever the follower's commit; 4: reset `matchIndex` on removal; 1: log
`InitState` after `loadState`, or validate a restart's later lines) is open.

## Next

- The proof: translate raft with `with_tla` (`etc/goose.py` has no build tags yet), strengthen the
  eleven trace hooks' specs (`Spec/go_etcd_io/raft/v3/trace*.lean`, now no-ops) to report the
  event, a harness proved to produce the trace, the transcription's Go proved to refine a Lean
  transcription of the two modules, and `NondeterministicModel.ToModel` specified (it is
  translated, `Code/github_com/anishathalye/porcupine.lean`, but no result uses it yet).
- Pin the TLA+ tools' versions.
