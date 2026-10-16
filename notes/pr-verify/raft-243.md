# Verifying etcd-io/raft#243

- PR: etcd-io/raft#243, "feat: Delete `Progress.PendingSnapshot` and improve snapshot handling",
  https://github.com/etcd-io/raft/pull/243, head `800cd610d5b1bccae9350b950e8638689a14e664` (one
  commit, open, "needs rebase"; base upstream `main` at `d155efc81`, Nov 2024). It addresses
  etcd-io/raft#124.
- Verified at fork commit `119f42a00` (branch `pr-raft-243-goose-lean` of `~/etcd`, worktree
  `~/etcd-pr/raft-243`). The PR's non-test diff was applied with `git apply -3` onto the pinned
  `raft37-goose-lean` (`509271dac`: raft v3.7.0 plus the read-index fix). The PR's base is an
  ancestor of the pin, so no upstream commits were needed.
- Every `.go` file conflicted, because the pin's raftpb is protobuf-go v2 (pointer messages read
  through getters) and the PR is gogoproto. The conflicts were resolved in the base's style, with
  no change of behavior:
  - `pb.Message{Type: pb.MsgSnapStatus, From: id, Reject: rej, AppliedSnapshotIndex: i}` became
    `&pb.Message{Type: pb.MsgSnapStatus.Enum(), From: new(id), Reject: new(rej),
    AppliedSnapshotIndex: new(i)}` (`node.go`, `rawnode.go`).
  - `m.Index`, `m.From`, `m.Reject` and `m.AppliedSnapshotIndex` became the getters (`raft.go`).
  - `raft.proto`'s new field lost its gogoproto option: `optional uint64 applied_snapshot_index = 15`.
- `raftpb/raft.pb.go` was regenerated rather than merged, with `scripts/genproto.sh`'s pipeline
  (protoc 3.20.3, protoc-gen-go v1.36.11). The same pipeline reproduces the base's `raft.pb.go`
  byte for byte.
- The PR's tests and testdata were applied as well, with their conflicts resolved the same way.
  `raftpb/raft_test.go`'s `Message` size is 208/104 here, not the PR's gogoproto 168/112.
  `go build ./...` and `go test ./...` pass in the fork worktree.
- This repository's branch is `pr-verify/raft-243` (worktree `/shared/etcd-grove-pr/raft-243`).
  Raft was re-translated from the fork worktree (`etc/goose.py --project raft --src
  raft=~/etcd-pr/raft-243`). The pin in `etc/goose.py` is unchanged, so `etc/goose.py --check`
  fails on this branch, as expected.

## Verdict

The cleanup half of the PR is sound. Removing `PendingSnapshot` from `ResetState`,
`BecomeSnapshot` and `BecomeProbe` meets the existing specs, re-proved on the new code. The
model of `Progress` simply loses the field.

The other half is not safe as written. On a successful `MsgSnapStatus`,
`pr.OnSnapshotApplied(m.AppliedSnapshotIndex)` sets the follower's `Match` to the
application-reported index. Until now only an acknowledgment from the follower itself could
raise `Match`, and the leader's safety argument rests on that. With this change the leader can:

- commit entries that no follower holds;
- send a heartbeat whose commit index is past the follower's log, which makes the follower
  panic. This happens on etcd's normal path: etcd reports `SnapshotFinish` once the snapshot's
  HTTP POST returns, before the follower has persisted the snapshot.

That arm of `stepLeader` is a `sorry` here, and every result over `raft.Step` (18 of them) now
reaches it.

The PR also changes when the leader leaves `StateSnapshot` on an `MsgAppResp`, from
`Match+1 >= firstIndex` to `Next >= firstIndex`. That is safe, since `Match` is untouched there,
but it sends redundant snapshots. Not covered at all: liveness (redundant snapshots) and etcd's
callers, which no longer compile.

## Changed functions

States are from `etc/verified-code.py --functions --package go.etcd.io/raft/v3` on `lean`.

| Package | Function | Kind | Before | After | Outcome |
|---|---|---|---|---|---|
| `tracker` | `Progress.ResetState` | refactor (no `PendingSnapshot = 0`) | verified | verified | old spec re-proved (the record lost the field) |
| `tracker` | `Progress.BecomeSnapshot` | refactor (no `PendingSnapshot = snapshoti`) | verified | verified | old spec re-proved |
| `tracker` | `Progress.BecomeProbe` | behavior change: `Next = Match+1` in every state; from `StateSnapshot` it was `max(Match+1, PendingSnapshot+1)` | verified | verified | same statement, `progressBecomeProbeNext` now `Match + 1`, re-proved; compatible for callers (their proofs rebuilt) |
| `tracker` | `Progress.OnSnapshotApplied` | new | - | verified | new exact spec: `Match = i`, `Next = i+1` |
| `tracker` | `Progress.String` | output only (no `pendingSnap=`) | translated | translated | not specified (no spec reads it) |
| `raft` | `stepLeader` | behavior change: `MsgSnapStatus` success arm; `MsgAppResp` in `StateSnapshot` condition; a new log line | verified | **unfinished** | old spec kept; `MsgAppResp` and `MsgSnapStatus`-reject arms re-proved; success arm `sorry` (not provable, below) |
| `raft` | `RawNode.ReportSnapshot` | signature: `+ appliedSnapshotIndex` | verified | verified (rests on the `sorry`) | old statement for every index, proof unchanged but through `raft.Step` |
| `raft` | `node.ReportSnapshot` | signature: `+ appliedSnapshotIndex` | verified | verified, sorry-free | old statement; proof unchanged (it only sends on `recvc`) |
| `raft` | `Node` interface | signature | - | - | n/a (exported API: breaking change) |
| `raftpb` | `Message.GetAppliedSnapshotIndex` | new (generated) | - | translated | not specified: only the `sorry`'d arm calls it |

Changed types:

- `tracker.Progress` loses `PendingSnapshot`. The Lean record `Progress` and its abstraction
  `progressAbs` lose `pendingSnapshot` (`Defs.lean`), and so do the leader's bound `PrOk`,
  `ResetPr`, `PrKeptAt` and `FreshPr`.
- `raftpb.Message` gains `AppliedSnapshotIndex *uint64`. It is not in the message model
  (`MessageM`, `msgPtsC`): the struct split of `msgPtsC_of_struct` drops its cell, and every
  message raft builds has it `nil`.

## Specs

- `Progress.BecomeProbe` (`Spec/go_etcd_io/raft/v3/tracker/Progress__BecomeProbe.lean`): the
  statement is unchanged, `ownProgress pr (progressBecomeProbe p)`. What changed is the record
  function (`Defs.lean`): `Next` was `max(Match+1, PendingSnapshot+1)` from `StateSnapshot` and is
  now `Match+1`. This is "compatible" in the sense of step 5: no caller's proof depended on the
  difference. All of them were rebuilt, including `stepLeader`'s `MsgUnreachable`, `MsgAppResp`
  and `MsgSnapStatus`-reject arms, and `raft__maybeSendAppend`.
- `Progress.OnSnapshotApplied` (`Spec/go_etcd_io/raft/v3/tracker/Progress__OnSnapshotApplied.lean`,
  new): `ownProgress pr (progressOnSnapshotApplied p i)`, with
  `progressOnSnapshotApplied p i = {p with matched := i, next := i + 1}`. Nothing relates `i` to
  the old `Match`, the log or the follower.
- `stepLeader` (`Spec/go_etcd_io/raft/v3/stepLeader.lean`): unchanged. Its postcondition says the
  step refines a protocol step (`Protocol/Model.lean`). In the protocol a leader's `matched` map
  rises only on a follower's `MsgAppResp` (`Step.appResp`), and can otherwise only be reset to 0
  or kept (`Step.reMatch`). Each entry must carry the follower's acknowledgment (`matchedOk`,
  `isAcked`, `Protocol/GhostState.lean:396`, `Protocol/Ghost.lean:967`).
- `RawNode.ReportSnapshot`, `node.ReportSnapshot`: the old statements, for every value of the
  new argument.

### The success arm

`Proof/go_etcd_io/raft/v3/stepLeader/Rest.lean`, `wp_stepLeader_report`, the `sorry` in the
`m.Reject' = false` case.

After `OnSnapshotApplied(asi)`, the follower's `Match` is `asi`. The arm cannot refine any
protocol step unless `asi` is `0` (`reMatch`) or the old `Match` (no change), or the leader holds
`isAcked` for the follower at `asi`, which a local `MsgSnapStatus` cannot carry. The arm also
breaks `PrOk` (`Match ≤ lastIndex`) when `asi > lastIndex`.

Two premises were considered. Neither makes it provable, and neither is one etcd can meet:

- **"`asi` ≤ the leader's commit index".** This would rule out false commits, but not false
  heartbeats. `HeartbeatOk` (`Model.lean:1525`) needs `m.commit ≤ matchOf s dst`, because
  `sendHeartbeat` sends `min(pr.Match, committed)` and the follower `commitTo`s it, which panics
  past its last index (`log.go`).
- **"The follower has durably applied a snapshot at `asi`".** This is what the PR's doc comment
  asks for, and it would be provable with a ghost acknowledgment from the follower's storage.
  etcd's sender cannot supply one: `rafthttp/snapshot_sender.go` reports `SnapshotFinish` when the
  POST returns 204, and the receiver's handler returns 204 after `Process`, which only enqueues
  the `MsgSnap` on the follower's `recvc`, before the snapshot is persisted.

A sound variant uses the report only as a hint for `Next`, as `PendingSnapshot` did, and leaves
`Match` to the follower's `MsgAppResp`.

## Callers (step 6)

`OnSnapshotApplied` is called only from `stepLeader`. Its `Match` write goes up through
`raft.Step` to every result over it; each one rebuilt and now reaches the `sorry`:

- `RawNode.Step`, `Tick`, `Campaign`, `Propose`, `ProposeConfChange`, `ReadIndex`,
  `ReportSnapshot`, `ReportUnreachable`, `TransferLeader`, `ForgetLeader`, `Advance`;
- `raft.tickElection`, `raft.tickHeartbeat`;
- `node.run`, `StartNode`, `RestartNode`.

`BecomeProbe`'s callers (`stepLeader`, `raft.maybeSendAppend`'s reject path through `stepLeader`)
were rebuilt with no proof change.

At the exported API, `ReportSnapshot` gains an argument on `Node` and `RawNode`. The PR
description says it is breaking ("targeted for v4.0.0"); the CHANGELOG and the module path
(`/v3`) do not. etcd's callers no longer compile: `server/etcdserver/server.go:730` calls
`s.r.ReportSnapshot(id, status)`, and its `rafthttp.Raft` interface (`transport.go`) and
`snapshot_sender.go`/`pipeline.go`/`peer.go` would need the index threaded through. This
repository's etcd server translation does not include those callers, and the server's proofs
were not rebuilt here. Since they rest on raft's specs, they reach the same `sorry`.

The register example (`Proof/github_com/mit_pdos/etcd_grove/examples/register/`) builds a
`pb.Message` copy literal, which gained the new field (`deliver.lean`). It was rebuilt
(`...register.Results`) and goes through; 3 of its 15 results reach a `sorry` (2 on `lean`), the third through this one.

## Trust base

`#print axioms` of `Proof/go_etcd_io/raft/v3/Results.lean`, on this branch against `lean` (from
the two builds' `Results.trace`), over 330 results plus the new `tracker.Progress.wp_OnSnapshotApplied`:

- No new axiom anywhere.
- No result lost an axiom.
- 18 results gained `sorryAx`, all through the `stepLeader` `sorry` above (the list in "Callers").
- `node.wp_ReportSnapshot`, every `tracker.Progress.wp_*` and `wp_OnSnapshotApplied` rest on the
  same 294 axioms as before: Lean's three plus the opaque Go types' instances.

`etc/tcb-report.py` was not run, because it needs every root of the worktree built and only raft's
modules were rebuilt. For the same reason `etc/verified-code.py` was not run on the branch; the
table's "After" column is read off the proofs. `etc/tcb-collections/pr-raft-243.txt` names the
roots, without a baseline.

## Findings (step 8)

The reproductions are Go tests against the PR's head (gogoproto API), in the scratch worktree
`~/etcd-pr/raft-243-upstream`: `pr243_repro_test.go` and `pr243_review_test.go` (the latter from
the reviewer). Run them with `GOTOOLCHAIN=go1.27.1 go test -run 'TestPR243|TestReview' -v .`. Each
test passes by asserting the bad behavior.

1. **A follower panics on a heartbeat after an unapplied snapshot report**
   (`TestReviewReportUnappliedPanicsFollower`). This is realistic, and the most serious finding.
   - The leader sends a snapshot at 11 and the `MsgSnap` is lost.
   - The application reports `SnapshotFinish` with index 11, as etcd's sender would, so
     `Match = 11`.
   - The next heartbeat carries `Commit = min(11, committed) = 11`, and a follower whose log ends
     before 11 panics in `commitTo`.
   - On the base, `Match` stays 0 and the heartbeat carries 0.
2. **The leader commits entries no follower holds** (`TestPR243SnapStatusRaisesMatchUnacked`,
   `TestPR243SnapStatusPastLastIndex`). The input is misuse, a reported index above what any
   snapshot could hold, but the library does not check it: one report of `lastIndex` plus any
   later `MsgAppResp` commits the leader's unreplicated tail in a 3-node group. With an index past
   `lastIndex`, `Match` and `Next` end up past the log. The proof's `PrOk` is exactly the bound
   that is lost.
3. **A zero report lowers `Match` to 0 and `Next` to 1** (`TestPR243SnapStatusZeroLowersMatch`).
   The PR calls this the "backward compatible" case, and its own `TestSnapshotSucceedWithoutIndex`
   asserts the same. On a compacted log the leader then sends a second snapshot
   (`TestReviewZeroReportResendsSnapshot`). The base probed from `PendingSnapshot+1`.
4. **A stale report lowers `Match`** (`TestReviewStaleReportLowersMatch`). Reports carry no
   snapshot identity, so a `SnapshotFinish` for an earlier snapshot, arriving after the peer
   re-entered `StateSnapshot`, sets `Match` below what the follower acknowledged. This is safe
   (the protocol only allows 0 there, but lowering acknowledges less) and costs a resend.
5. **`MsgAppResp` in `StateSnapshot` now leaves it almost always**
   (`TestPR243AppRespInSnapshotResendsSnapshot`; on the base the same test sends no snapshot).
   `BecomeSnapshot(S)` sets `Next = S+1 ≥ firstIndex`, so the new condition `Next >= firstIndex`
   holds for any ack that raises `Match`. A delayed ack below `firstIndex` then sends a second
   snapshot while the first is in flight. This is safe (proved: `Match` comes from the ack) but
   wasteful.
6. Nits:
   - After `OnSnapshotApplied(i)` with `i < S`, `BecomeReplicate` leaves `sentCommit = S > Next-1`,
     against the field's documented invariant (`TestReviewSentCommitAboveNext`).
   - `asi = 2^64-1` makes `Next = 0` (`TestReviewWrap`).
   - `tracker/progress_test.go` is not gofmt'd.

No bug was found in the pinned (existing) code, so nothing was added to `issues/`. The findings
above are about the PR's code and stay here, per the skill.

The reviewer subagent's other points are resolved: the refactors' specs were confirmed exact, and
the `RawNode.ReportSnapshot` spec's comment was corrected (it is stated for every index, but false
for most). The reviewer noted that `try rw` in `stepLeader`'s `MsgAppResp`/`StateSnapshot` arm
hides whether the rewrite fires; that remains open.

## Draft review comment (for the user to edit and post)

> Thanks for picking up #124. The `PendingSnapshot` removal looks good to me. I have concerns
> about using `appliedSnapshotIndex` to set `Match`:
>
> - Until now `Match` only moved on an `MsgAppResp` from the follower. With
>   `OnSnapshotApplied`, a `SnapshotFinish` report sets it directly, and the leader trusts it for
>   commit and for heartbeats (`sendHeartbeat` sends `min(pr.Match, committed)`). If the reported
>   snapshot was not actually persisted by the follower, the next heartbeat carries a commit
>   index past the follower's log, and the follower panics in `commitTo`. etcd's rafthttp reports
>   `SnapshotFinish` when the POST returns, before the follower persists the snapshot, so this
>   is reachable there. An index above what the follower has (or above `lastIndex`) also lets the
>   leader commit entries the follower does not hold. I have tests for both if useful.
> - A report of 0 (the "backward compatible" case) resets `Match` to 0 and `Next` to 1, so on a
>   compacted log the leader sends another snapshot. A stale report for an earlier snapshot
>   lowers `Match` the same way.
> - In the `MsgAppResp` case, `pr.Next >= firstIndex` is true right after `BecomeSnapshot`, so any
>   ack that raises `Match` leaves `StateSnapshot`, even one still below `firstIndex`, and a second
>   snapshot is sent. The old `pr.Match+1 >= firstIndex` avoided that.
>
> Would it work to use the reported index only as a hint for `Next` (as `PendingSnapshot` did),
> and keep `Match` for the follower's `MsgAppResp`, which it sends after applying the snapshot?
> Also, since `ReportSnapshot` changes signature, etcd's `server.go` and rafthttp callers need
> updating; a CHANGELOG entry would help.
