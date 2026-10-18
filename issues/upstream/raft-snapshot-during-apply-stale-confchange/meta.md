# raft-snapshot-during-apply-stale-confchange

## Security

Not a security report. In etcd it needs a membership change (`MemberAdd`/`MemberRemove`, root when auth is on) and a
follower behind the leader's compacted log at that moment; a client with ordinary access cannot cause it. etcd
uses v1 conf changes only, so there the outcome is a wrong configuration on one member, not the joint panic.

## Candidate

- **Finding**: `issues/raft-snapshot-during-apply-stale-confchange.md`
- **Target**: etcd-io/raft, `main` (also in v3.7.0, which etcd `main` uses: `raft.go` is identical)
- **Branch**: `fix/raft-snapshot-during-apply-stale-confchange` in `~/etcd-fixes/raft-snapshot-during-apply-stale-confchange`,
  three commits: ca5cc04 adds the test, which fails there; 5acb532 is the fix; 7982f54 adds the changelog entry.
  Rebuilt 2026-10-18, **not pushed**: the fork still has the earlier single commit c65d182 (test and fix together,
  pushed 2026-10-18). The links in `issue.md` (`rawnode_test.go#L718-L764`, the test from its doc comment to its
  closing brace) are right only after a force-push the user approves:
  `git -C ~/etcd-fixes/raft-snapshot-during-apply-stale-confchange push --force-with-lease=fix/raft-snapshot-during-apply-stale-confchange:c65d182b85525f63906e442bcb5d2eae42c6f07b origin fix/raft-snapshot-during-apply-stale-confchange`;
  then check the line link on GitHub.
- **Base**: upstream `main` 638f42739b77572b5708eb0d8a776a272ade71ed (2026-10-16)
- **State**: draft, revised to the 2026-10-18 standard (2026-10-18); open design question below ("The leader's
  resend needs `ReportSnapshot`")
- **Upstream issue**: —
- **PR**: — (then replace `pull/TODO` in the changelog commit's `CHANGELOG/CHANGELOG-3.8.md` entry with its number)

etcd-io/raft has no issue template: the issue uses etcd's bug-report sections, with "Raft version" for etcd's
version and configuration sections. The fix is a design choice: the issue asks the maintainers which they prefer.

Commit messages (drafts for the user to rewrite):

- `raft: test snapshot received while applying a conf change` (no body)
- `raft: do not restore a snapshot while applying committed entries` — "Otherwise ApplyConfChange for one of those
  entries applies its conf change again, on top of the snapshot's configuration."
- `changelog: add entry for snapshot received while applying a conf change` (no body): Bug Fixes, "Fix wrong
  configuration or panic when a follower receives a snapshot while applying a conf change".

## Duplicates checked (2026-10-16, again 2026-10-18)

2026-10-16, `repo:etcd-io/raft`: `snapshot ApplyConfChange` (one hit, #8, closed PR "support asynchronous storage
writes", unrelated), `restore snapshot conf change applying` (none), `ApplyConfChange stale` (none).
2026-10-18: `repo:etcd-io/raft ApplyConfChange snapshot` (#8 again), `"already joint" snapshot` (0),
`restore snapshot confchange applying` (0), `ApplyConfChange twice` (0); `repo:etcd-io/etcd ApplyConfChange
snapshot restore configuration` (10, none about a snapshot stepped between a `Ready` and `ApplyConfChange`). No
duplicate, no open PR. Related findings in this repository, not reported here: `raft-advance-before-applyconfchange`,
`raft-track-confchange-application`, `raft-document-confchange-before-advance`.

## Other candidates

Independent of every other candidate; no conflict in code (`raft.go` and `rawnode_test.go` merge cleanly with
`fix/raft-joint-empty-transition-panic`, checked with `git merge-tree` against its 4ea35f1, 2026-10-18). Both add
a Bug Fixes bullet to `CHANGELOG/CHANGELOG-3.8.md` (as do the read-index candidates), so their changelog commits
conflict there: whichever merges second needs a one-line rebase. Not mentioned in the PR (not a split).

## Why the fix works

At the base, in the test's first case: node 2 steps `MsgApp` committing "add 4" at index 1; `Ready` hands it out
(`applying` 1, `applied` 0). The `MsgSnap` at index 2 is above the commit index, so `restore` restores it:
configuration `{1,2,3}`, commit 2. `ApplyConfChange("add 4")` then applies "add 4" to `{1,2,3}`: `{1,2,3,4}`. The
resent `MsgSnap` is at or below the commit index, so it is ignored, and node 2 keeps `{1,2,3,4}`. In the joint
case the restored configuration is already joint, and `EnterJoint` panics.

With the fix, `restore` returns false while `applying > applied` (after the fast-forward path, which only moves
the commit index); `handleSnapshot` answers as for any ignored snapshot (`MsgAppResp` at the commit index, 1).
`ApplyConfChange` applies "add 4" to `{1,2,3}`, which is right at index 1; `Advance` sets `applied` to 1. The
resent snapshot is above the commit index and nothing is being applied, so it is restored: `{1,2,3}` (or the
snapshot's joint configuration).

## Why the test shows the bug, not a misuse

doc.go's protocol: the application persists the `Ready`'s entries, applies its committed entries, calling
`ApplyConfChange` for each conf change, then calls `Advance`; it passes received messages to `Step` with no
condition. `node.run` steps `recvc` messages while it waits for `Advance` (`node.go:394-399`, `advancec` set at
`node.go:435-446`), and `RawNode` has no rule against `Step` between `Ready` and `Advance`. The test does exactly
that: `Ready`, persist the entries, `Step(MsgSnap)`, `ApplyConfChange`, `Advance`. The gap (a snapshot stepped
while the application applies) is the bug's trigger, not an avoidable one: it is the time the application takes
to persist and apply. `ApplyConfChange` is called before `Advance`, right after the entry is handed out.

The leader's messages are built by hand (a `MsgApp` committing index 1, then a `MsgSnap` at index 2, each of a
kind a leader sends); `newNetwork`'s peers are bare `raft`s with no `Ready`/apply cycle, so the test drives a
`RawNode`, as `rawnode_test.go`'s tests do. In a cluster the snapshot needs a follower behind the leader's
compaction point while it is still applying an older batch.

## Verification (go1.26.9 linux/amd64)

`TestRawNodeSnapshotDuringConfChangeApply` (`rawnode_test.go`, after `TestRawNodeRestartFromSnapshot`), two cases
in one table: v1 "add 4" with a snapshot of voters `{1,2,3}`; a `ConfChangeV2` "add 4" entering a joint
configuration (`JointExplicit`) with a snapshot in `(1 2 3 4)&&(1 2 3)`. Asserts only the guarantee: both halves of
node 2's voters equal the snapshot's. The second `Step(snap)` stands for the leader resending an ignored snapshot;
at the base it is ignored (index 2 is already committed), so the base behaviour is the issue's.

- At the tests commit ca5cc04 (`go test . -run 'TestRawNodeSnapshotDuringConfChangeApply$'`): fails, case 0
  expected `[1 2 3]`, actual `[1 2 3 4]`; case 1 `panic: config is already joint`.
- At the fix commit 5acb532: passes; `go test -count=1 ./...` (raft, confchange, quorum, raftpb, rafttest,
  tracker) ok; `gofmt -l .` empty; `go vet ./...` clean. Re-run at 7982f54 (same code): same.
- With a real leader, a temporary test not on the branch (`go test -overlay`, 2026-10-18): a leader `raft` whose
  log is compacted at index 2 (`{1,2,3}`), driven with `MsgBeat`, `MsgSnapStatus` (what `ReportSnapshot` sends) and
  the replies, against a `RawNode` follower holding a `Ready` with "add 4": with the fix the follower ignores two
  snapshots while applying; after `ApplyConfChange` and `Advance` the leader sends a third, which is restored, and
  the follower ends with `[1 2 3]`. With the base `raft.go` overlaid, the first snapshot is restored, the follower
  ends with `[1 2 3 4]`, and the leader sends no other.

Not run: etcd's tests, `make verify`. Not reproduced on a cluster or on etcd.

## etcd

etcd's raft loop (`server/etcdserver/raft.go:297-331` at etcd `main` 22cc5d9ac, raft v3.7.0) makes a follower
whose `Ready` has a conf change wait for the apply goroutine before `Advance`; meanwhile `node.run` keeps stepping
messages from the transport, `MsgSnap` included, and the apply goroutine calls `ApplyConfChange`
(`server/etcdserver/server.go:2007`, `2023`) with etcd's membership not yet replaced by the snapshot (which comes in
the next `Ready`). So etcd can reach it: a follower applying a membership change while the leader snapshots it.
etcd's membership store is then right (it restores the snapshot) while raft's configuration is not. Reasoning
from code only. With the fix, etcd's snapshot receiver has already saved the snapshot's database file when raft
ignores it; the leader's `ReportSnapshot(SnapshotFinish)` after the upload leads to a second transfer.

## The leader's resend needs `ReportSnapshot` (open question for the user)

Found in the review (2026-10-18). With the fix, a delivered snapshot that the follower ignores while applying is
sent again only after the leader's application calls `ReportSnapshot` (either status). The follower's answer, a
`MsgAppResp` at its commit index, leaves the leader's `Match` below its first index, so the leader's progress stays
in `StateSnapshot` (paused) until `MsgSnapStatus` arrives. A temporary test (the real-leader test above with
`ReportSnapshot` replaced by 30 leader ticks of heartbeats, 2026-10-18): the leader sends one snapshot and never
another; the follower stays at commit 1. At the base this dependency does not arise for a delivered snapshot: it is
restored, or ignored as obsolete or fast-forwarded, and the follower's answer then reaches the leader's first index.

doc.go's step 2 requires `ReportSnapshot` after sending a `MsgSnap`, and etcd calls `ReportSnapshot(SnapshotFinish)`
after each upload; but `Node.ReportSnapshot`'s comment (`node.go:230-238`) says "Calling ReportSnapshot with
SnapshotFinish is a no-op", so an application that trusts it and reports only failures would leave such a
follower without a snapshot until the leader changes. Options, not taken (the design stays as the task asked):

- add to this PR a change to that comment, saying that `SnapshotFinish` must be reported too (a follower may ignore
  a snapshot it receives while applying, and the leader sends it again only after `ReportSnapshot`);
- or defer instead of ignoring: raft keeps the `MsgSnap` and handles it when the apply finishes (in `Advance`, or
  on the `MsgStorageApplyResp` with `AsyncStorageWrites`), with no second transfer and no dependency on
  `ReportSnapshot`; a larger change (a stashed message to drop on a term change, the response sent later);
- or the `ApplyConfChange`-tracking alternative below, which restores the snapshot at once.

## If a reviewer asks

- Liveness: the snapshot is ignored only while `applying > applied`, which lasts from a `Ready` handing out
  committed entries to its `Advance` (with `AsyncStorageWrites`, to the `MsgStorageApplyResp`). A follower the
  leader snapshots is behind the leader's first index, so the leader sends it no entries, and its commit index can
  only grow to the end of its own log (heartbeats carry `min(Match, committed)`). So it has finitely many entries
  left to apply; once applied, nothing is being applied until the snapshot is restored, and the next resend
  succeeds. A follower that is always applying needs an endless supply of newly committed entries, which a
  follower that needs a snapshot does not get. The resend relies on the application calling `ReportSnapshot`
  (doc.go step 2): `MsgSnapStatus` moves the leader's progress to probe, the probe at the snapshot's index is
  rejected, and the leader sends a snapshot again. Checked with the temporary real-leader test above. Without
  `ReportSnapshot`, see the next section.
- Cost: one more snapshot transfer when a snapshot arrives during an apply (in etcd, a second database transfer).
  Rare: only a follower behind the leader's compaction point that is applying at that moment.
- Narrower: ignore the snapshot only when `(applied, applying]` holds a conf change. raft does not track that for
  followers; `restore` would have to read those entries (possibly from storage) or raft would have to note conf
  entries as it hands them out. Not tried: the broad check costs little more (above).
- Alternative: let `ApplyConfChange` skip a change a restored snapshot covers. `ApplyConfChange` has no index, and
  counting the conf changes in the window fails when the application already called it before the snapshot
  arrived; raft would have to track which entry each call is for (an API change, or tracking the conf entries it
  hands out, as this repository's prototype `issues/raft-conf-lag-model/guard-fix.patch` does behind a `Config`
  flag). That approach also covers an application that calls `Advance` before `ApplyConfChange`.
- Alternative: document that `Step` must not be called between a `Ready` and its `ApplyConfChange` calls. `Node`
  does it itself (`node.run`), and doc.go puts no condition on `Node.Step`. Buffering `MsgSnap` in `node.run` while
  `advancec` is set would cover `Node` without `AsyncStorageWrites` only.
- Not covered: an application that calls `Advance` before `ApplyConfChange`, which doc.go's step 4 ("at any time
  after step 1") and `Node.Advance`'s comment allow. `applied` then moves at `Advance`, a snapshot is restored, and
  the later `ApplyConfChange` is applied on top of it as before. That ordering breaks raft's other conf-change
  guards too (`issues/raft-advance-before-applyconfchange.md`); this fix assumes conf changes are applied before
  `Advance`, as doc.go's example loop does.
- `restore`'s doc comment now lists the new reason for returning false. The new comment in `restore` says why (the
  pending `ApplyConfChange` calls) and that the leader retries, neither of which the condition shows. The log line
  is at Info, as the fast-forward path's; `handleSnapshot` then logs "ignored snapshot" as for any ignored one.
- Backports: v3.7.0 has the same `restore`; not tried on a release branch. The changelog entry is in
  `CHANGELOG-3.8.md` (v3.8.0, Bug Fixes): `main` is the 3.8 line, and raft keeps its changelogs on `main` only.
  etcd uses v3.7.0, so the fix reaches etcd only with v3.8.0 or a v3.7.1 patch release, which raft has never made:
  the maintainers' call; if wanted, cherry-pick the fix commit to `release-3.7` in a separate PR and add a v3.7.1
  section to `CHANGELOG-3.7.md` on `main`.

## check.py (2026-10-18)

No FAIL. WARNs, decided:

- The comments added in `restore`: kept. The doc comment's new reason for returning false is what callers read; the
  inline comment says why the snapshot is ignored and that the leader retries, neither of which the condition shows.
- The issue's 296 words (aim 250): kept; it shows two cases (wrong configuration and panic) and asks which fix the
  maintainers prefer. The approved siblings are 194-215 words with one case and no question.
- The PR's 99 words (aim 90): kept; the approved raft example has 136.
