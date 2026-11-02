---
upstream: none
checked: 2026-10-26
links:
  - etcd-io/raft#8 pr merged: added AsyncStorageWrites; its review (and etcd-io/etcd#14627's, where it started) does not discuss a snapshot handed out while committed entries are being applied
blocks-proof: no
---

# raft: with `AsyncStorageWrites`, entries applied after a snapshot that includes them diverge the state machine

With `AsyncStorageWrites`, a follower's append thread can install a leader's snapshot before the
follower's apply thread has applied committed entries the snapshot already includes; the apply
thread then applies them again on top of it, and the state machine diverges from every other
node's. With voters 1, 2, 3 and node 1 leading: node 2 hands "a" (index 1) to its apply thread;
before it is applied, node 2 steps node 1's snapshot at index 2 (state "ab") and hands it to its
append thread; the append thread installs "ab", then the apply thread applies index 1: "aba".

**Expected:** node 2's state should be "ab", the state at index 2: the [`Config.AsyncStorageWrites`](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/raft.go#L153-L187)
thread model lets the two threads process their messages "in any order", so raft should not hand
out a snapshot while entries handed out before it are still being applied (or should document that
the append thread must wait for the apply thread).

**Impact:** applications that enable `AsyncStorageWrites` and install snapshots in the append
thread ("snapshots to apply", as the option's documentation says), when a follower behind the
leader's compacted log receives a snapshot while it is applying older entries. etcd does not
enable `AsyncStorageWrites` and is not affected. Same code in v3.7.0.

**Reproduction:** `TestRawNodeAsyncSnapshotDuringApply` in
[`issues/raft-async-snapshot-during-apply-divergence/async_snapshot_during_apply_test.go`](raft-async-snapshot-during-apply-divergence/async_snapshot_during_apply_test.go)
(node 2 as a `RawNode` with `AsyncStorageWrites`, its append thread running ahead of its apply
thread; node 1's `MsgApp` and `MsgSnap` built by hand), copied into the module root at
etcd-io/raft@c51f010c851e (2026-10-23), go1.27.3 linux/amd64:

```
$ go test . -run '^TestRawNodeAsyncSnapshotDuringApply$' -count=1
--- FAIL: TestRawNodeAsyncSnapshotDuringApply (0.00s)
    async_snapshot_during_apply_test.go:102:
        	Error:      	Not equal:
        	            	expected: "ab"
        	            	actual  : "aba"
FAIL
```

**Cause:** while a snapshot is pending, [raft hands out no new committed entries](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/log.go#L253-L258)
("Doing so raises questions about what should be applied first"), but nothing holds a snapshot
back for the entries already handed out: [`restore`](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/raft.go#L1852-L1855)
accepts any snapshot above the commit index, and the [next `Ready`](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/rawnode.go#L155-L169)
puts it in a `MsgStorageAppend` at once.

## Proof

no: the raft proof requires `asyncStorageWrites = false` (`Proof/go_etcd_io/raft/v3/InvRawnodeC.lean`,
`InvBoot.lean`), which etcd meets.

## Fix

**Branch**: `fix/raft-async-snapshot-during-apply-divergence` in `~/etcd-fixes/raft-async-snapshot-during-apply-divergence` (upamanyus/etcd-raft, pushed): 831199f test, b60b90c fix
**Base**: etcd-io/raft@1931ff5beacc1e2539003c0c70f096285f04c425

**PR draft**:

Title: raft: apply a snapshot after earlier entries with async writes

With `AsyncStorageWrites`, [`restore`](https://github.com/etcd-io/raft/blob/1931ff5beacc1e2539003c0c70f096285f04c425/raft.go#L1852-L1856) accepts a snapshot while committed entries handed out earlier in a `MsgStorageApply` are still being applied, and the [next `Ready`](https://github.com/etcd-io/raft/blob/1931ff5beacc1e2539003c0c70f096285f04c425/rawnode.go#L155-L169) hands the snapshot to the append thread. The two threads [may process their messages in any order](https://github.com/etcd-io/raft/blob/1931ff5beacc1e2539003c0c70f096285f04c425/raft.go#L162-L179), so the older entries can be applied on top of the snapshot. Raft [holds back committed entries while a snapshot is pending](https://github.com/etcd-io/raft/blob/1931ff5beacc1e2539003c0c70f096285f04c425/log.go#L253-L258), but not a snapshot while committed entries are being applied. This PR makes `RawNode` hand nothing to the append thread while a snapshot waits for those entries to be applied.

The first commit adds a test of the issue's example, which fails on `main`; the second, the fix, makes it pass.

The PR for `raft-snapshot-during-apply-stale-confchange` (a conf change applied again after a snapshot) needs this PR's change with `AsyncStorageWrites`; the two merge cleanly in either order. I can combine both fixes in one PR if you prefer.

The fix (`storageAppendHeld` in `rawnode.go`) holds back everything bound for the append thread
(the snapshot, later entries, the `HardState`, `msgsAfterAppend`) only while an unstable snapshot
waits and `applying > applied`; without `AsyncStorageWrites` it never holds. Alternatives: refuse
the snapshot in `restore` (the leader then waits for `ReportSnapshot` and sends it again); document
the order (contradicts "processed in any order"); send the snapshot to the apply thread too (an
interface change).

## Notes

Its synchronous sibling, a conf change applied again on top of a snapshot, is
[`raft-snapshot-during-apply-stale-confchange`](raft-snapshot-during-apply-stale-confchange.md);
with `AsyncStorageWrites` that fix needs this one. doc.go's example append thread only saves the
snapshot to storage and never installs it in the state machine, a separate documentation gap.
