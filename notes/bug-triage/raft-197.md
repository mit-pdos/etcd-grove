# etcd-io/raft#197: Discussion: follower panics due to a regression in the commit index

<https://github.com/etcd-io/raft/issues/197>. Open, filed 2024-04-23, no comments, no labels, no fix.
It follows the closed draft PR etcd-io/raft#25 (2023, "prevent follower panic on commit index
regression"). On that PR, tbg said that hitting this panic "usually means that a follower has not
upheld its durability guarantees". He proposed event-based logging, so that a user could make such
assertions recoverable, and filed that as etcd-io/raft#29. No version is named. The code is the same
on `main` and at the raft pin `509271dac`.

**The report.** A follower loses its persisted state, for example to a disk failure, or because the
application runs raft purely in memory. It restarts under the same ID with an empty log. The
leader's `Progress` for that follower still says `Match = 10`. `sendHeartbeat` (`raft.go:694`) sends
`Commit = min(pr.Match, r.raftLog.committed)` = 10. The follower runs `handleHeartbeat`
(`raft.go:1827`), which calls `raftLog.commitTo(10)`. Since `lastIndex() = 0 < 10`, it panics:
`log.go:326`, "tocommit(10) is out of range [lastIndex(0)]. Was the raft log corrupted, truncated,
or lost?". The issue proposes that the follower reject the heartbeat with a hint, as it already does
for a `MsgApp`, so the leader lowers its `Progress` and the follower catches up.

## Classification

**A-model** (secondary: **N**, works as intended upstream). The decisive fact: the proof has no
crashes and no stable-versus-volatile state. A node's ghost state, `ownRaftGhost γ id`, is allocated
once, with the cluster (`ownRaftGhost_alloc_gen`, `Protocol/Facts.lean:1499`). The only way to start
a node from an empty storage is `RestartNode`'s premise `rnInit γ md id V`
(`Spec/go_etcd_io/raft/v3/RestartNode.lean:90`), which needs that node's ghost at the protocol's
initial state. A node that lost its disk and rejoins `γ` under its old ID therefore cannot be
expressed: its old acknowledgements (`isAcked γ id t i`) persist in the logic, and its log does not.
Upstream regards the panic as the intended assertion of a violated contract. `doc.go:75-82` requires
the `HardState` and entries to be persisted before messages are sent, and the panic message itself
asks whether the log was lost. So this is not a defect in the code, and not a gap in the spec of
`handleHeartbeat`. It shows a limit of the execution model.

## The code path and its verification state

Source: the proof files and `Proof/go_etcd_io/raft/v3/Link.lean`, read directly, because
`verified.txt` was not yet written. `.lake/tcb.json` was absent, so the axioms were found by reading
the proofs. Each proof listed is a `theorem` linked in `Link.lean` with no `sorry` in its file.

| Go function | State | Spec |
|---|---|---|
| `raft.sendHeartbeat` (leader) | verified | `Spec/go_etcd_io/raft/v3/raft__sendHeartbeat.lean` |
| `raft.Step`, `stepFollower`/`stepCandidate` (`MsgHeartbeat`) | verified | `Spec/go_etcd_io/raft/v3/raft__Step.lean`, `stepFollower.lean` |
| `raft.handleHeartbeat` | verified (`Link.lean:1087`) | `Spec/go_etcd_io/raft/v3/raft__handleHeartbeat.lean` |
| `raftLog.commitTo` | verified (`Link.lean:711`) | `Spec/go_etcd_io/raft/v3/raftLog__commitTo.lean` |
| `NewRawNode`, `RestartNode` (starting the follower on an empty storage) | verified | `Spec/go_etcd_io/raft/v3/NewRawNode.lean`, `RestartNode.lean` |
| the application's storage after a disk loss | not modeled | none |

## The argument (step 4)

1. **The panic is excluded by a premise, which is discharged by the protocol.**
   `raftLog.commitTo.spec` (`raftLog__commitTo.lean:33-39`) has the premise
   `uint.Z tocommit ≤ plogLastIndexZ ls.prev (ls.sents ++ ls.uents)`, "exactly what makes the
   `Panicf` dead". `raft.handleHeartbeat.spec` (`raft__handleHeartbeat.lean:73`) carries the same
   premise on `m.Commit'`. `Step` discharges it with `heartbeat_commit_le_last`
   (`Protocol/Facts.lean:66`; used at `Proof/.../raft__Step.lean:204`).
2. **Why the protocol fact holds.** A heartbeat's `isMessage` (`Protocol/GhostState.lean:232`)
   carries `∃ i, Commit ≤ i ∗ isAcked γ m.dst m.term i`: the receiver itself acknowledged index `i`
   in this term. `ownRaftGhost` ties the receiver's acks to its current log (`acksOk`/`LogOk`), so
   `Commit ≤ lastIndex`. In the report, the follower acknowledged index 10 before the disk loss,
   and that persistent `isAcked` fragment is still there. Its log, however, is now empty.
3. **What the scenario violates.** In the logic, the restarted follower would need
   `ownRaftGhost γ id` at the state of the empty storage. `NewRawNode` gives a node that is not
   yet attached to any cluster ghost (`rawNodeFresh`). `RestartNode` attaches it only through
   `rnInit γ md id V` (`RestartNode.lean:90`; `NewRawNode.lean`, `def rnInit`), which is
   `ownRaftGhost γ id initPState`, or `rinit c0` in dynamic mode. That ghost state comes only
   from `ownRaftGhost_alloc*`, at the creation of `γ`, once per ID. It is exclusive, and the
   old incarnation's ghost already holds it, so no proof can produce `rnInit` for an existing
   cluster. The setting therefore violates `RestartNode`'s premise. The deeper reason it cannot
   be stated otherwise is the model. `notes/STATUS.md` ("Out of scope for now", line ~1123)
   records that Perennial's Lean port has no crash semantics, that nothing models stable versus
   volatile state, and that raft's votes and acks are justified by volatile state
   (`isVote`, `isAcked`), "so persist-before-send is neither stated nor checked". Losing the
   disk is a crash that loses durable state. That is A-model.
4. **Not X, not C.** Under the premises, the spec excludes the panic, and the report's setting
   does not meet the premises. The issue's real request is that raft tolerate a lost state, so
   that it can run without durability. That is a change of the contract, not a gap in the spec
   of the current contract.
5. **The etcd server.** `notes/STATUS.md` (stage R8a, D11) notes that a restart from a WAL is crash
   recovery and is not among the verified start paths. etcd's own response to a lost member
   (remove it, then add it under a new ID) is likewise outside the model.

No `issues/` file. The behavior is documented: `doc.go:75-82` (persist before sending) and
`doc.go:105-108` (all persisted entries must be available through `Storage`, and a `MemoryStorage`
must be repopulated on restart). The panic message names the cause. Upstream treats it as an
assertion. The issue is a feature request (in-memory raft) phrased as a regression.

## Proposal

**`raft-durable-acks`** (A-model): make the acks and votes durable facts, and state restart.

- **Without crashes (feasible now).** Justify `isAcked γ id t i` and `isVote` by the storage's
  *persisted* state (`ownStorage σ`, its `σ.ents`/hard state) rather than by the in-memory
  `raftLog`. In other words, state persist-before-send: a `MsgAppResp`/`MsgVoteResp` in the
  outbox handed out by `Ready` is backed by entries the application has already `Append`ed to
  `Storage`. A sketch: in `ownRaftGhost`, replace `acksOk` over `ps.log` with
  `acksOk` over `stableLog σ`, plus an invariant of `RawNode.Ready`/`Advance` that every
  outbound ack is at most `stableIndex`. Cost: the `isAcked`/`isVote` producers (`stepFollower`'s
  append path, `handleAppendEntries`, `handleSnapshot`, vote granting), plus `Ready`/`Advance`'s
  sync contract (`MustSync`, already specified). This is a medium-sized change to `InvRawnode` and
  `Protocol/GhostState`.
- **With crashes.** Add a restart theorem: `RestartNode` from a storage `σ` that holds what the old
  incarnation persisted returns `ownRaftGhost γ id ps` with `ps.log = σ`, given a crash-invariant
  form of the ghost. A storage holding less than the old incarnation persisted, which is this
  bug, is then exactly what fails the premise, and a lost member must rejoin under a fresh ID
  (`ConfChange` remove/add). This needs crash semantics, which Perennial's Lean port does not have
  (`notes/STATUS.md`, `notes/bbolt-unsafe.md`). It is a Perennial model extension, to be
  proposed there, not patched in here (CLAUDE.md, "Changes to Perennial").

The issue's proposal (reject the heartbeat with a hint) would drop the `commitTo` premise from
`handleHeartbeat.spec` for out-of-range commits. Even so, safety under amnesia stays false in
general (a forgetful voter can let two leaders win, or lose committed entries), so no spec here
should adopt it as a guarantee.

## Files

None in `issues/` or `notes/` besides this report.
