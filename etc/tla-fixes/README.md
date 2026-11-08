# A corrected etcdraft.tla

A patch series against etcd-io/raft `c51f010c851e` (main, 2026-10-23; its `tla/` and
`state_trace.go` are v3.7.0's) that fixes the misfits between `tla/etcdraft.tla` and raft found by
the trace-check stage (`issues/raft-tla-*.md`) and adds PreVote and CheckQuorum (etcd's
configuration) behind constants that leave the rest unchanged when off, with the evidence that the fixes are justified
independently of raft's code, that the corrected model still satisfies its invariants, and that it
still rejects traces of buggy rafts. Nothing here is upstream; nothing has been posted.

Why: the trace-check stage's statement (raft's traces conform to `etcdraft.tla`) is false of
upstream's specification (the stage is paused, `notes/trace-validation-plan.md`). Proving it
against a corrected specification is worth something only if the corrections are small, judged
against Raft's design rather than raft's code, re-checked against the model's invariants, and shown
not to make the model accept everything. This directory is that check
(`notes/trace-validation-plan.md`, "Paused", the plan of 2026-11-08).

## The series

`patches/`, `git am` (or `git apply`) in order on `c51f010`:

| # | Change | Finding | Verdict against Raft's design |
|---|---|---|---|
| 0001 | `raft.go`: trace `InitState` once the persisted state is loaded | [restart-initstate-unmatched](../../issues/raft-tla-restart-initstate-unmatched.md) | not a model change (raft's trace logging) |
| 0002 | the durable state keeps the persisted log itself; `Restart` restores it | [restart-truncated-log](../../issues/raft-tla-restart-truncated-log.md) | design: the log is persistent state (thesis §3.8, Fig. 3.1); the original restores entries never persisted |
| 0003 | an append request carries the leader's commit index, the receiver clamps | [msgapp-commit-unclamped](../../issues/raft-tla-msgapp-commit-unclamped.md) | design: paper Fig. 2 / thesis Fig. 3.1 verbatim ("leaderCommit: leader's commitIndex"; receiver `min(leaderCommit, index of last new entry)`) |
| 0004 | a server dropped from the configuration loses its `matchIndex` | [readded-member-matchindex](../../issues/raft-tla-readded-member-matchindex.md) | implementation choice (volatile leader state; `design.md`: "match is set to zero"); raft's is the safer one |
| 0005 | a follower installs a snapshot as `raft.restore` does, answering `MsgAppResp` | [snapshot-committed-follower](../../issues/raft-tla-snapshot-committed-follower.md), [snapshot-response-subtype](../../issues/raft-tla-snapshot-response-subtype.md) | design: InstallSnapshot's receiver rules (thesis §5.1, paper Fig. 13 steps 6-7); the original ignores every snapshot at a follower that committed anything |
| 0006 | raft's `lead`: a voter that knows its term's leader refuses votes; `NoConflictAppendEntriesRequest` only when an entry is new (else, with `lead`, a second successor beside `AppendEntriesAlreadyDone`'s, which `TraceMatched` rejects) | [vote-refused-known-leader](../../issues/raft-tla-vote-refused-known-leader.md) | implementation choice (refusing a vote is always safe; cf. thesis §4.2.3); the original is the thesis's first-come-first-served rule |
| 0007 | `LeaderCompletenessInv` for leaders of a term at least the server's | [leader-completeness-stale-leader](../../issues/raft-tla-leader-completeness-stale-leader.md) | design: the thesis's own state invariant (App. B, Theorem 1, with `>=`); the original guards on the entry's term, not its commit term |
| 0008 | `AddLearner` may demote a voter | [learner-demotion-unmodelled](../../issues/raft-tla-learner-demotion-unmodelled.md) | design for the change (a single-server removal from the voters, thesis §4.3, plus a non-voting member, §4.2.1); see "Caveats" for a demoted leader |
| 0009 | `MoreUpToDateCorrectInv` is not checked (both configurations) | [more-up-to-date-cut-batches](../../issues/raft-tla-more-up-to-date-cut-batches.md) | not a Raft property: the thesis never states it, and it is false of the thesis's own `raft.tla` (by hand, not model-checked) |
| 0010 | `Traceetcdraft`: bootstrap entry `j` carries the configuration it adds (the first `j` peers) | [bootstrap-entries-full-config](../../issues/raft-tla-bootstrap-entries-full-config.md) | design: one configuration change per entry (`RawNode.Bootstrap`; `MCetcdraft`'s own `BootstrapLog`); the trace specification's initial log only |
| 0011 | `raft.go`, `state_trace.go`: trace `becomePreCandidate`, `MsgPreVote`/`MsgPreVoteResp`, and a vote request ignored within the leader lease (`IgnoreRequestVoteRequest`, in place of its receipt) | ("PreVote and CheckQuorum" below) | not a model change (raft's trace logging; raft's behaviour unchanged) |
| 0012 | `PreVote` and `CheckQuorum` constants, `FALSE` by default: a pre-candidate state, pre-vote requests and answers, campaigning only after a won pre-vote; the lease (`IgnoreInLease`); the bare `MsgAppResp` answering an older leader | ("PreVote and CheckQuorum" below) | design: Pre-Vote (thesis §9.6), the lease (§4.2.3), a leader stepping down without a quorum (§6.2, the existing `StepDownToFollower`) |

The verdicts are from a reading of Ongaro's thesis (*Consensus: Bridging Theory and Practice*,
2014), the Raft paper, the thesis's `raft.tla` and raft's documentation, item by item, asking
whether each fixed behaviour is an instance of the design, a choice the design leaves free, or only
what raft's code does, and whether the fix could mask a raft bug (none could). The report is
`notes/tla-fixes-justification.md`.

`LeaderCompletenessInv`'s repair is the guard the user chose in `notes/trace-validation-plan.md`'s
Q4 (b) (the thesis reading recommends etcd-io/raft#549's slightly stronger form, also true).
`MoreUpToDateCorrectInv` is dropped, not repaired, by this series' choice (a repair needs the term
each entry was committed in, a history variable; the thesis's equal-last-term half needs none, and
is model-checked below but not added).

## Not fixed

- [restart-config-from-storage](../../issues/raft-tla-restart-config-from-storage.md): raft
  restarts with its storage's configuration and the application re-applies the later
  configuration entries; the model restores the configuration of the last `Ready` and applies only
  the last committed configuration entry. Fixing it needs application snapshots in the model.
- Joint configuration changes, `AsyncStorageWrites`, read-only requests and leadership transfer
  are not modelled (as upstream).

## The checks

### 1. The findings' own tests

Every trace test of `issues/raft-tla-*` passes with the series applied (`check.sh`), but
`TestTLATraceRestartWithoutSnapshot` (not fixed, above); the model-replay tests of the two
invariants fail for want of a counterexample (TLC finds none to replay). raft's own tests pass.

### 2. Random runs (`raft/tla_random_test.go`)

`TestTLARandom`, a test in package `raft` (copy it into the raft checkout), runs five `RawNode`s
(three bootstrapped, two empty) for 600 random steps per seed: delivering a message in flight (in
any order, 10% lost), handling a node's `Ready` (persist, send, apply, `ApplyConfChange`), ticking
every node, proposing at the leader, configuration changes (add, remove, add learner, demote),
snapshot and compaction at a node's applied index, restarts (a new `RawNode` on the same storage),
early campaigns; `MaxSizePerMsg` 1 on even seeds and `MaxInflightMsgs` 2 on every third. Each
trace is validated with `Traceetcdraft.tla` as `validate.sh` does.

The driver keeps three rules, each where raft and the model disagree in a way the series does not
change, each named in the code:

- no `ConfChangeAddNode` of a voter and no `ConfChangeAddLearnerNode` of a learner (no-ops in
  raft; the model's `AddNewServer`/`AddLearner` exclude them);
- a snapshot whose configuration does not include its receiver is lost in transit (raft ignores
  it, "should never happen", `raft.restore`; etcd does not send one,
  `nonissues/raft-snapshot-without-recipient-livelock.md`);
- before a restart the application snapshots what it applied, with its configuration, and it does
  not restart a node that applied a configuration change since its last `Ready` (the unfixed
  finding above).

Results (2026-11-08):

- 60 seeds without campaigns, 600 steps each: every trace accepted (27,360 lines; 58 traces with
  a restart, 14 with a snapshot installed, 31 with `AddLearner`, 26 `AddNewServer`, 22
  `RemoveServer`, 28 with a refused vote, 83 elections). The same 60 traces against upstream's
  `tla/` (raft with 0001 only): 30 rejected.
- 60 seeds with campaigns (the final driver), the whole series: every trace accepted.
- Twice the runs found a gap in the corrected model itself, each then fixed or written up: the
  overlap 0006 now excludes, and the bootstrap configurations of 0010. They also found
  [restart-config-from-storage](../../issues/raft-tla-restart-config-from-storage.md) (not fixed).

`raft/tla_targeted_test.go`: three fixed schedules for rules random runs rarely reach (a vote
request of a term whose leader the voter knows, from a heartbeat, or from an append request after
a restart; a resent one-entry append request with a later commit index); all accepted.

### 3. Model checking

`MCetcdraft` with `MCetcdraft.cfg` as upstream configures it (four servers, three initial, two
reconfigurations, terms below 10, five requests, crashes and the unreliable network of
`NextDynamic`), with every invariant but `MoreUpToDateCorrectInv` (0009), `LeaderCompletenessInv`
repaired (0007):

- simulation (`-simulate -depth 100`, 4 workers), 40 minutes: 225 million states, 2.1 million
  behaviours (mean length 81), no violation; a second 30-minute run: 193 million states, none;
- breadth-first search, 40 minutes: depth 16, 45 million distinct states (32 million left on the
  queue), no violation;
- with the thesis's equal-last-term invariant added (two logs with the same last term: the shorter
  is a prefix of the longer; Lemma 8, step 9; `EqualLastTermPrefixInv`, defined in the run's
  `MCetcdraft.tla`, not in the series): simulation, 30 minutes, 163 million states, 1.55 million
  behaviours, no violation.

These ran on 0001-0009; 0010 changes only `Traceetcdraft.tla`, which model checking does not use.
Bounded runs, so evidence, not proof.

### 4. Mutation testing (`mutants/`)

Each mutant (`mutants/mutants.py`) is one change to raft's Go code: a "bug" breaks a rule of Raft
the corrected model states, a "benign" one (a control) does not. `mutants/run.py` runs
`TestTLARandom` against each and counts the seeds whose trace TLC rejects (or that make raft
panic). A model that accepted everything would reject nothing; one that is too strict would reject
the controls.

| Mutant | Kind | Random runs, no campaigns (20 seeds: rejected/panicked; 0001-0009) | Random runs with campaigns (30 seeds; 0001-0009) | Targeted schedules (0001-0010) |
|---|---|---|---|---|
| `commit-minority`: commit on a minority | bug | 20/0 | 30/0 | rejected |
| `elect-minority`: win with a minority of votes | bug | 20/0 | 30/0 | rejected |
| `campaign-same-term`: campaign without a new term | bug | 20/0 | 30/0 | rejected |
| `vote-not-reset`: keep the vote across terms | bug | 10/0 | 30/0 | accepted |
| `vote-ignores-log`: grant without the up-to-date check | bug | 3/0 | 25/0 | accepted |
| `heartbeat-commit-unclamped` | bug | 9/11 | 12/18 | rejected |
| `commit-old-term`: commit by counting an older term's entry (Raft Fig. 8) | bug | 0/0 | 4/0 | accepted |
| `snapshot-discards-matching-log` | bug | 0/0 | 1/0 | accepted |
| `vote-ignores-lead`: grant though the term's leader is known | bug | 0/0 | 0/0 | rejected |
| `follower-commit-past-new`: commit past the entries verified | bug | 0/0 | 0/0 | rejected |
| `lead-not-set-on-app`: no leader recorded from an append request | bug | 0/0 | 0/0 | accepted |
| `no-empty-entry`: no empty entry at election | benign | 0/0 | 1/0; 0/0 with 0010 | accepted |
| `reject-hint-unclamped` | benign | 0/0 | 0/0; 0/0 with 0010 | accepted |

Ten of the eleven bug mutants are caught; both controls survive. `heartbeat-commit-unclamped`
mostly makes raft itself panic (the follower's `commitTo` past its log). The survivor,
`lead-not-set-on-app`, matters only for a follower in a term whose leader it learned from an
append request it did not accept, receiving the vote request of a candidate whose log is as up to
date as its own: no schedule here reaches it (in the targeted one the follower holds the leader's
newer entry and refuses on the log). The `no-empty-entry` control's one rejection was 0010's gap,
not the mutant (with 0010, 30 seeds: none).

## PreVote and CheckQuorum (0011, 0012)

etcd runs raft with both (`CheckQuorum: true` in `server/etcdserver/bootstrap.go`, `PreVote`
defaulting to true in `embed/config.go`); upstream's specification models neither, and without
0011-0012 random runs with either on are rejected (20 of 20 seeds with PreVote, 19 of 20 with
CheckQuorum). raft's own trace logging omitted the pre-vote phase (`becomePreCandidate` untraced,
`MsgPreVote`/`MsgPreVoteResp` dropped by the hooks), and logs a vote request it then ignores
within its lease as a receipt, which a specification without time cannot follow without
branching. So:

- **0011** (raft's trace logging only): logs `BecomePreCandidate`, the pre-vote messages under the
  vote events (their `type` tells them apart), and `IgnoreRequestVoteRequest` in place of the
  receipt of a vote or pre-vote request `Step` ignores for the lease (the condition factored into
  `ignoresInLease`, which `Step` itself uses).
- **0012** (the specification): constants `PreVote` and `CheckQuorum`; everything they add is a
  disjunct guarded by them or a condition vacuous without them, so with both `FALSE` the
  specification takes exactly the steps it took before (checked below). `Traceetcdraft` reads them
  from the environment variables `PREVOTE` and `CHECKQUORUM` (the trace does not record raft's
  configuration). Pre-Vote: `PreTimeout` (pre-candidate, term and vote unchanged, no known
  leader), `RequestPreVote` (for the next term), `HandlePreVoteRequest` (granted for a later term,
  or as a vote in the same term, if the log is up to date; no state change; the answer carries the
  request's term if granted), `HandlePreVoteResponse` (tallied by a pre-candidate), `Timeout` only
  after a won pre-vote, `UpdateTerm` not for a pre-vote request or a granted pre-vote. The lease:
  `IgnoreInLease` (a vote or pre-vote request of a later term discarded by a node that knows a
  leader; the specification has no time, so model checking may take it whenever the node knows a
  leader, and trace validation takes it only at `IgnoreRequestVoteRequest`). An append request of
  an older term is answered with a bare `MsgAppResp` (success, index 0) of the receiver's term.
  A leader's step-down without a quorum is the existing `StepDownToFollower`.

Checks:

- with both flags off: every check above unchanged (the findings' tests, the targeted schedules,
  30 random seeds), and TLC's refinement check, `MCetcdraft` with the flags off satisfying
  `[][C!NextDynamic]_vars` for `C` the specification at 0010 (`C == INSTANCE etcdraftC`, a copy of
  it renamed, added to `MCetcdraft.tla`; `RefinesC` under `PROPERTIES`): breadth-first search, 40
  minutes, depth 15, 9.8 million distinct states, no violation; with the flags `TRUE` the same
  check fails at the first step, a `PreTimeout` (the check is not vacuous);
- random runs with PreVote, with CheckQuorum, with both (20 seeds each): every trace accepted. In
  40 traces with both: 313 pre-candidacies, pre-votes granted and refused in most, a lost pre-vote
  in 37, 159 lease-ignored requests (pre-votes and votes), the bare `MsgAppResp` in 2, a quorum
  step-down in 1; the targeted `TestTLATargetedCheckQuorumStepDown` and
  `TestTLATargetedStaleLeaderBareResponse` cover the last two (accepted);
- model checking with both `TRUE` (simulation, 40 minutes, invariants as above): 243 million
  states, 2.3 million behaviours, no violation;
- mutants, random runs with both flags (20 seeds, rejected/panicked/accepted):

  | Mutant | Kind | Result |
  |---|---|---|
  | `prevote-changes-term`: a pre-vote request's term adopted | bug | 20/0/0 |
  | `prevote-records-vote`: granting a pre-vote records a vote | bug | 20/0/0 |
  | `precandidate-wins-early`: campaign after one pre-vote | bug | 20/0/0 |
  | `lease-without-leader`: lease without a known leader | bug | 20/0/0 |
  | `prevote-ignores-log`: pre-votes without the up-to-date check | bug | 11/0/9 |
  | `stale-app-unanswered`: no bare `MsgAppResp` to an older leader | bug | 0/0/20 |
  | `election-timeout-wider`: timing only | benign | 0/0/20 |

  `stale-app-unanswered` survives as trace validation must: it checks what raft does, and a
  message raft does not send is never required (the specification's answer stays unsent).

## Caveats

- A leader demoted or removed from the voters keeps leading unless `StepDownOnRemoval` is set; the
  thesis (§4.2.2) has it step down, and `StepDownOnRemoval`'s comment says raft will make that
  unconditional. The corrected model, like upstream's for `DeleteServer`, lets it keep leading; no
  property should rely on that.
- raft makes a configuration take effect when applied, the thesis when appended (`doc.go` calls
  them equivalent for safety; `raft.go`'s vote comment points at etcd-io/etcd#7625). The model
  follows raft; a conformance proof inherits the assumption.
- `0006` makes the model raft-specific (a deterministic refusal where the thesis allows a grant):
  right for a conformance statement about raft, narrower than Raft.

## Reproducing

```
TLA_TOOLS=<dir with tla2tools.jar and CommunityModules-deps.jar> \
  etc/tla-fixes/check.sh <etcd-io/raft checkout at c51f010> <new work dir>
TLA_TOOLS=... SEEDS=30 python3 etc/tla-fixes/mutants/run.py <the work dir>
```

Model checking: `java -cp tla2tools.jar:CommunityModules-deps.jar tlc2.TLC -config MCetcdraft.cfg
MCetcdraft.tla` in the work dir's `tla/` (`-simulate -depth 100` for simulation).
