# etcd-io/raft#140: send up-to-date commit index in heartbeats

- PR: https://github.com/etcd-io/raft/pull/140, "raft: send up-to-date commit index in
  heartbeats", by pav-kv. Open, a draft ("needs rebase"), head
  `ffbd5f78545ac5f26ad23f1071c1133cd2d99251`, base `026484c68` (main, January 2024). It has three
  commits:
  - `eb6bfc696`: #139, "advance commit index safely". This is the follower side, `logSynced`.
  - `9bffaa4e4`: the `lagging_commit` test.
  - `ffbd5f785`: the leader side. Its commit message is still "TODO: describe why it is now
    safe".

  It fixes etcd-io/raft#138. The issue says the leader side must wait until every node runs the
  follower side.
- Verified at: fork branch `pr-raft-140-goose-lean`, commit `726078878` (worktree
  `~/etcd-pr/raft-140`). That is the pinned `raft37-goose-lean` `509271dac` plus the PR.
- Proof branch: `pr-verify/raft-140` (worktree `/shared/etcd-grove-pr/raft-140`). The fork
  commit is not pushed, so `etc/goose.py --check` fails on this branch.

## Verdict

**The PR is not safe as written.** Its follower-side claim is false: "from now on, the log is
a prefix of the leader's log", set when the first `MsgApp` of the term is accepted. Once that
claim fails, a heartbeat with the leader's full commit index commits entries that differ from
the leader's. That breaks State Machine Safety, and it is reachable with this package's own
leader:

- Node 2 is leader at term 4. A delayed `MsgApp` that node 2 sent as leader of term 2 reaches
  a follower that has CheckQuorum or PreVote on (etcd enables both).
- The follower's step-down reply looks to node 2 like an acknowledgement of index 0. Node 2
  resets its `Next` for that follower to 1 (an existing quirk:
  `issues/raft-stale-term-appresp-ack.md`).
- Node 2 then sends the log from index 1, cut by `MaxSizePerMsg`. The follower accepts a batch
  that agrees with its log but ends before its uncommitted older-term tail. `maybeAppend`
  truncates only at a conflict, so the tail stays and `logSynced` becomes true.
- The next heartbeat commits the stale tail (`TestLogSyncedBogusAckStaleTail`; it fails both at
  the PR head and on the verified v3.7 code).

Two more findings:
- **Mixed versions.** A follower running code from before #139 commits `m.Commit` from a
  #140 leader unconditionally. The issue warns that this crashes the follower. It can also
  silently commit stale entries, which is worse.
- **Liveness regression.** A follower that restarts holding all entries but an old commit index
  never learns the commit from heartbeats while the cluster is idle.

The physical-level specs of every changed function are proved, with no new axiom:
`handleHeartbeat`, `sendHeartbeat`, `handleAppendEntries`, `reset` and `becomeLeader`, with the
new field tracked in `ownRaftPhys`. The callers up to `raft.Step` were re-proved:
`bcastHeartbeatWithCtx`, `stepFollower`, `stepCandidate` and the `MsgHeartbeat` branches of
`Step`.

The protocol model was changed to the PR's heartbeat:
- `HeartbeatOk` no longer bounds `Commit` by `Match`.
- `Step.heartbeat` commits some `cm ≤ min(Commit, lastIndex)`.

Its ghost refinement rests on one new `sorry`, `heartbeat_commit_acked`
(`Proof/go_etcd_io/raft/v3/Protocol/Refinement.lean`). It says that a follower advancing its
commit on a heartbeat has acknowledged that far in the term. That is exactly the PR's claim,
and the counterexample above shows it is false. **So the end-to-end Raft results on this
branch are no evidence for #140's heartbeat path.**

A fix that is safe and provable with the existing invariants: track `syncedIndex`, the highest
index acknowledged by an accepted `MsgApp` this term, reset to 0, and commit
`min(m.Commit, syncedIndex)`. The model's acknowledgement invariant (`acksOk`/`ackAgree`) gives
the agreement up to it. A smaller fix also passes all tests and the fuzzer: set `logSynced`
only when `mlastIndex == lastIndex()`. Neither is applied or proved here.

## Applying the PR

The PR is against upstream main of January 2024 (gogoproto messages). The pin is raft v3.7
(protobuf-go v2, pointers and getters). `git apply -3` conflicted in three hunks of `raft.go`,
resolved in the base's style:

- `sendHeartbeat`: v3.7 has `pr := r.trk.Progress[to]` and, after the send,
  `pr.SentCommit(commit)`, which upstream did not have in January 2024. Kept, with
  `commit := r.raftLog.committed`, the PR's value. **This is a place where the verified code may
  differ from what the PR would become after a rebase.** `SentCommit(committed)` sets
  `sentCommit` past `Next-1` for a lagging peer, which turns off `CanBumpCommit`'s eager
  `MsgApp` (see the liveness finding). `SentCommit(min(Match, committed))` would keep the old
  bookkeeping.
- `handleAppendEntries` and `handleHeartbeat`: the PR's lines in the base's form (`a :=
  logSliceFromMsgApp(m)`, `maybeAppend(a, m.GetCommit())`, `m.GetCommit()`).
- Tests: the PR's test changes in the base's `require`/pointer style. `testdata/lagging_commit.txt`
  exists on the base (from #137); the PR's expected output applies.

`go build ./...` and `go test ./...` pass in the fork worktree. No non-test code differs from the
PR beyond the `SentCommit` line.

## Changed functions, types and fields

All were verified (sorry-free) on `lean`.

| Item | Kind | After | Outcome |
|---|---|---|---|
| `raft.handleHeartbeat` | behavior change | verified | new spec, incompatible: commits only if `logSynced`, at `min(Commit, lastIndex)`; no premise on `Commit` |
| `raft.sendHeartbeat` | behavior change | verified | new spec, incompatible: `Commit = committed` exactly (the `Commit ≤ Match` bound is dropped) |
| `raft.handleAppendEntries` | behavior change (new field write) | verified | old spec, accept branch: also `logSynced := true` |
| `raft.reset` | behavior change (new field write) | verified | old spec via `resetTo`, which now clears `logSynced` |
| `raft.becomeLeader` | behavior change (new field write) | verified | old spec via `becomeLeaderPre`, which now sets `logSynced` |
| type `raft`, field `logSynced` | new | n/a | `NState.logSynced` (invisible to `toPState`); `ownRaftPhys` conjunct `rv.logSynced' = s.logSynced`; `raftOwn` owns the field; `raft.wp_load_logSyncedC`/`wp_store_logSyncedC` |

### The two behavior changes

`handleHeartbeat` (`Spec/go_etcd_io/raft/v3/raft__handleHeartbeat.lean`):
- **Old:** under the premise `m.Commit ≤ lastIndex()`, `committed := max(committed, m.Commit)`
  (`heartbeatResultOld`). The premise was the protocol fact `heartbeat_commit_le_last`, from
  the leader's `Commit ≤ Match`.
- **New:** no premise on `m.Commit`. `committed := max(committed, min(m.Commit, lastIndex()))`
  if `logSynced`, and unchanged otherwise (`heartbeatResult`). `commitTo`'s `Panicf` is dead for
  every message: the PR's "defence in depth" holds, and is proved.
- `heartbeatResult_synced`: on a synced follower, at a `Commit` within the log, the new result
  is the old one. `heartbeatResult_unsynced`: an unsynced follower does not commit.
- The change is not compatible: an unsynced follower no longer commits. So the callers were
  re-checked.

`sendHeartbeat` (`Spec/go_etcd_io/raft/v3/raft__sendHeartbeat.lean`):
- **Old:** `cm ≤ committed` and `cm ≤ Match(to)`.
- **New:** `cm = committed`.
- The change is not compatible: the `Match` bound is gone, and the model's `HeartbeatOk` and
  the ghost `isMessage` relied on it.

## Callers (step 6)

| Caller | Outcome |
|---|---|
| `bcastHeartbeatWithCtx` (exported to `bcastHeartbeat`, `tickHeartbeat`, `stepLeader` `MsgBeat`, read-index) | spec unchanged in text (`HeartbeatOk`), since `HeartbeatOk` changed with the model; re-proved |
| `releasePendingReadIndexMessages`, `stepLeader`'s `MsgReadIndex` and response lemmas (`HeartbeatOk` transfers) | re-proved (proof edits only) |
| `stepFollower`, `stepCandidate` | `MsgHeartbeat` premise `m.Commit ≤ lastIndex ∧ m.From ≠ id` reduced to `m.From ≠ id`; re-proved; result `heartbeatResult` (new definition) |
| `raft.Step`, `MsgHeartbeat` branches (`_eq`, `_gt`, `_lt`) and dispatch | commit premise and `heartbeat_commit_le_last` removed; refine the new `StepC.heartbeat` at `cm = min(Commit, logLast)` if `logSynced` and `cm = 0` otherwise (`step_handle_heartbeat`, `raft__Step/repl_lemmas.lean`); re-proved |
| `raft.Step`, `MsgApp` branches | `HandleAppResult`'s accept now sets `logSynced`; refinement re-proved (`toPState` ignores the field) |
| `newRaft` | struct literal and `ownRaftPhys` intro with the new field (`false`); re-proved |
| `raft.Step`, `MsgVote_gt` | unchanged; `rframe` hit the recursion limit on the larger record, replaced by the explicit `RFrame` proof |
| protocol model `Step`/`StepC`/`StepCF`/`StepR` `.heartbeat`, `HeartbeatOk` | changed as above; `RInv_heartbeat`, `StepR.pci_keep`, the conversions and the ghost dispatchers re-proved |
| ghost `ownRaftGhost_step_beat` | re-proved without the acknowledgement (the leader cannot produce it any more) |
| ghost `ownRaftGhost_step_heartbeat` | split: `_acked` is the old proof, given an acknowledgement of `Commit`. The new lemma takes `cm`. Where the commit does not move, it uses `_acked` at `Commit := 0`, which needs no acknowledgement. Where it moves, it takes the acknowledgement from **`heartbeat_commit_acked` (`sorry`)** |

`RawNode`, `node` and the server rebuilt unchanged against the new `raft.Step` spec, whose text
is unchanged; they now reach the new `sorry` through it.

The API is unchanged. The behavior is not:
- A follower ignores the commit index of a heartbeat until it accepts a `MsgApp` in the term.
- It commits up to `min(m.Commit, lastIndex)` on heartbeats.

Neither is in a CHANGELOG. raft has no CHANGELOG entry for this PR.

## Trust base

The new `sorry` is `heartbeat_commit_acked` (`Protocol/Refinement.lean`). It is reached by
every result through `raft.Step`, and so by the `node`/`RawNode` results and the server's.

**It is not believed.** Its statement is the PR's claim. The model's `AppOk` refutes it, and so
does the code (the counterexample above). It is there only so that the rest of the proof could
be rebuilt around the PR, and so that the gap sits in one named place.

No axiom was added or removed. The rest of the trust base is as on `lean`
(`etc/tcb-report.py --collection etc/tcb-collections/pr-raft-140.txt`; see the TCB note at the
end).

## Findings

All tests are in `notes/pr-verify/raft-140-tests/`. They are copied into a checkout of the named
revision and run with `go test -run <Name> .`. Each one fails on the code it names, showing the
problem.

1. **The PR's safety bug: a stale tail is committed** (high). The follower-side claim "after
   the first accepted `MsgApp`, the log is a prefix of the leader's" is false. `maybeAppend`
   keeps an older-term tail that the accepted batch did not conflict with.
   - Locally, with a handcrafted `MsgApp`: `upstream-pr-head/logsynced_repro_test.go`
     (`TestLogSyncedStaleTail`).
   - With this package's own leader (found by the reviewer): a delayed `MsgApp` of the leader's
     earlier term draws a step-down reply (CheckQuorum/PreVote) that the leader of the current
     term takes for an acknowledgement of 0. That resets `Next` to 1 (the existing quirk), and
     the `MaxSizePerMsg`-cut batches from index 1 end below the tail.
     `upstream-pr-head/logsynced_bogusack_repro_test.go` and `fork-v3.7/bogusack_repro_test.go`
     (`TestLogSyncedBogusAckStaleTail`) end with "follower committed entry 4 of term 3; the
     leader's entry 4 has term 4". The leader committed 4/4.
   - `upstream-pr-head/logsynced_fuzz_test.go` (`TestLogSyncedFuzz`, `FZ_SEEDS=N`; not seed
     reproducible, because raft uses the global random source) is a randomized cluster with
     drops, duplicates, reordering, crashes, snapshots and unreachable reports. It finds a
     violation within about 3000 seeds at the PR head.
   - **Fixes:**
     - commit at most `min(m.Commit, syncedIndex)`, with `syncedIndex` the highest `mlastIndex`
       accepted in the term; or
     - set `logSynced` only when `mlastIndex == lastIndex()`. The reviewer checked this one:
       existing tests pass, the fuzzer finds nothing in 3000 seeds, and both repros stop at
       "logSynced = false".
2. **Mixed versions: silent divergence, not only a crash** (high for the rollout). Suppose the
   leader has #140 and a follower does not have #139. The follower commits `m.Commit`
   unconditionally. When its uncommitted older-term tail reaches past `Commit`, `commitTo` does
   not panic and commits the stale entries.
   - `upstream-base/mixedversion_repro_test.go` (`TestOldFollowerUnmatchedHeartbeatCommit`) runs
     the old follower code.
   - `upstream-pr-head/leaderhb_repro_test.go` (`TestLeaderHeartbeatCommitUnmatched`) shows that
     the leader sends `Commit > Match`.
   - etcd-io/raft#138 plans the migration around a crash. A crash-only analysis understates it.
3. **Liveness regression: a restarted follower can stay behind** (medium). The follower
   restarts with every entry but an older commit index, while the leader is idle and has the
   peer at `StateReplicate`, `Match = lastIndex`.
   - The follower's `logSynced` is false, so it ignores the heartbeats' commit.
   - The leader sends no `MsgApp`: a heartbeat response triggers one only if `Match <
     lastIndex` or in `StateProbe`, and `sentCommit = committed` turns off `CanBumpCommit`.
   - Before the PR, the heartbeat carried `min(Match, committed) = committed`.
   - `upstream-pr-head/restart_repro_test.go` and `fork-v3.7/restart_repro_test.go`
     (`TestRestartedFollowerLearnsCommitFromHeartbeat`) fail with the PR and pass on both bases.
   - The PR's own `TestRawNodeCommitPaginationAfterRestart` needed
     `rawNode.raft.logSynced = true` to pass, which is the same symptom.
   - etcd mostly hides this: rafthttp reports a peer unreachable on stream errors, which puts it
     in `StateProbe`. A quick restart with no failed send stays behind, and so do ReadIndex reads
     on it, until the next write.
4. **Existing code, recorded in `issues/raft-stale-term-appresp-ack.md`** (low on the pinned
   code). With CheckQuorum or PreVote, the reply to a stale-term `MsgApp` is an empty
   `MsgAppResp`, which `send` stamps with the current term. A leader that is the same node in a
   later term reads it as an acceptance of 0 and resets a probing peer to `Next = 1`.
   `fork-v3.7/staleack_repro_test.go` (`TestStaleTermAppRespRegressesNext`) fails on the pin.
   This is harmless to safety before #140 (the proof treats an acknowledgement of 0 as
   vacuous), and it is the enabler of finding 1.
5. Minor: the field comment "Always false for a candidate" does not hold for a pre-candidate,
   because `becomePreCandidate` does not `reset`. This is harmless: `stepCandidate`'s
   `becomeFollower` clears it before a heartbeat is handled.

The reviewer's other points were checked and found to be no problem:
- snapshot restore (full or fast-forward) with `logSynced`;
- `ForgetLeader`;
- `becomeFollower` at the same term;
- the async storage writes crash path.

There are no open review points.

## Draft review comment (for the user to edit and post)

> Thanks for this. I think the follower-side condition needs to be stronger before the leader
> can send its full commit index.
>
> `logSynced` is set on the first accepted `MsgApp` of the term, but `maybeAppend` only truncates
> at a conflict. If the follower has an uncommitted tail from an older term and accepts an
> append whose entries end before that tail, the tail stays, `logSynced` is true, and the next
> heartbeat commits `min(Commit, lastIndex())`, which reaches into the tail.
>
> This is reachable with raft's own leader. With CheckQuorum or PreVote, a follower answers a
> `MsgApp` of an older term with an empty `MsgAppResp`, stamped with its current term. If the old
> sender is the leader of that term, it takes the reply as an acceptance of index 0 and moves a
> probing peer to `StateReplicate` with `Next = 1`. It then sends `MaxSizePerMsg`-sized appends
> from index 1, the first of which the follower accepts without truncating. Here is a test on
> this branch that ends with a follower committing entry 4 of term 3 while the leader committed
> entry 4 of term 4: <attach `TestLogSyncedBogusAckStaleTail`>.
>
> Committing only up to the highest index acknowledged in this term (`min(m.Commit,
> syncedIndex)`), or setting `logSynced` only when the accepted append reaches `lastIndex()`,
> avoids it.
>
> Two smaller points:
> - During a rolling upgrade, an old follower that receives `Commit > Match` can also commit a
>   stale tail silently, not only crash, if its log is long enough. That seems worth stating in
>   the migration plan.
> - A follower that restarts with all entries but an old commit index no longer catches up from
>   heartbeats while the cluster is idle: it is unsynced and the leader has nothing to append.
>   `TestRawNodeCommitPaginationAfterRestart` needing `logSynced = true` looks like the same
>   thing. Maybe the heartbeat response could say the follower is unsynced, so the leader sends
>   an empty append.

## TCB note

The full `lake build` of the branch passes (5105 jobs). `etc/tcb-report.py --check` against
`lean`'s baseline reports exactly one difference, `NEW in the trust base: sorry
heartbeat_commit_acked`; `etc/tcb-baseline.txt` was updated on the branch with `--check
--update`.

- The new collection `etc/tcb-collections/pr-raft-140.txt` rests on the 10 axioms already in
  `raft.txt` plus that `sorry`.
- The collections `raft.txt`, `register.txt` and `server.txt` gain the `sorry` (updated on the
  branch). Every other collection is unchanged.

`etc/verified-code.py --package go.etcd.io/raft/v3` on the branch: 258 of 327 functions are
verified. The five changed functions are verified, and `handleHeartbeat`, `sendHeartbeat`,
`handleAppendEntries`, `reset` and `becomeLeader` are sorry-free. Only 242 of the 258 are
sorry-free: `raft.Step` and everything above it reach `heartbeat_commit_acked`. The script
counts lines against the pinned Go source.
