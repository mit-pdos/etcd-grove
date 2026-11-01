---
upstream: none
checked: 2026-10-23
links:
blocks-proof: yes
---

# raft: a snapshot received while a conf change is being applied leaves a follower with the wrong configuration, or panics

A follower that steps a leader's snapshot while its application is still applying a committed
conf change applies that conf change a second time, on top of the snapshot's configuration, which
already includes it, and keeps the wrong configuration until it restarts. With voters 1, 2, 3 and
node 1 leading: node 2's `Ready` hands out "add 4" (index 1); before node 2's application calls
`ApplyConfChange`, node 2 steps a snapshot at index 2 taken after "remove 4" (voters 1, 2, 3); the
application then applies "add 4" and node 2 ends with voters 1, 2, 3, 4. When the conf change
enters a joint configuration and the snapshot was taken in it, `ApplyConfChange` panics ("config is
already joint").

**Expected:** node 2 should end with the snapshot's configuration: stepping messages between
`Ready` and `ApplyConfChange` is allowed ([`Node` does it itself](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/node.go#L394-L399)
while the application applies the last `Ready`; doc.go puts no condition on `Node.Step`), and an
application applying each `Ready` in order before `Advance` does what doc.go asks.

**Impact:** a follower behind the leader's compacted log that receives a snapshot during the short
window in which it applies a membership change. etcd is plausibly exposed (not demonstrated): its
followers wait for the apply loop before `Advance` when a `Ready` has a conf change, while
`node.run` keeps stepping messages from the transport, `MsgSnap` included; the leader snapshots a
follower more than `SnapshotCatchUpEntries` (5000) entries behind. etcd uses v1 conf changes only,
so there the outcome is a wrong voter set on one member (used for its vote tally if it campaigns),
not the panic. Same code in v3.7.0.

**Reproduction:** `TestRawNodeSnapshotDuringConfChangeApply` in
[`issues/raft-snapshot-during-apply-stale-confchange/snapshot_during_confchange_apply_test.go`](raft-snapshot-during-apply-stale-confchange/snapshot_during_confchange_apply_test.go)
(node 2 as a `RawNode` applying each `Ready` before `Advance`; node 1's `MsgApp` and `MsgSnap`
built by hand), copied into the module root at etcd-io/raft@c51f010c851e (2026-10-23), go1.27.3
linux/amd64:

```
$ go test . -run '^TestRawNodeSnapshotDuringConfChangeApply$' -count=1
--- FAIL: TestRawNodeSnapshotDuringConfChangeApply (0.00s)
    --- FAIL: TestRawNodeSnapshotDuringConfChangeApply/0 (0.00s)
        snapshot_during_confchange_apply_test.go:93:
            	Error:      	Not equal:
            	            	expected: []uint64{0x1, 0x2, 0x3}
            	            	actual  : []uint64{0x1, 0x2, 0x3, 0x4}
    --- FAIL: TestRawNodeSnapshotDuringConfChangeApply/1 (0.00s)
panic: config is already joint [recovered, repanicked]
FAIL
```

**Cause:** [`restore`](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/raft.go#L1915-L1928)
switches the follower to the snapshot's configuration as soon as it steps the snapshot, whether or
not committed entries handed out in the last `Ready` are still being applied.
[`applyConfChange`](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/raft.go#L1943-L1963)
applies the change to the current configuration, assuming it is the one just before the change.
Nothing corrects it afterwards: [`restore` ignores the resent snapshot](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/raft.go#L1853-L1855),
no longer above the commit index.

## Proof

yes: not reached yet (the reconfiguration model does not model snapshots,
`notes/reconfiguration-model-check.md`), but raft's intended `ApplyConfChange` spec (the
configuration is the log's at the applied index) is false when a snapshot is stepped in this
window, which etcd's `node.run` allows; no premise etcd meets excludes it.

## Fix

**Branch**: `fix/raft-snapshot-during-apply-stale-confchange` in `~/etcd-fixes/raft-snapshot-during-apply-stale-confchange` (upamanyus/etcd-raft, not pushed; the fork has an older revision, da0e9bf, to be force-pushed over): de03c18 test, 2425490 fix
**Base**: etcd-io/raft@c51f010c851edd0dada5af41bafbf68e54617767

**PR draft**:

Title: raft: switch to a snapshot's configuration when it is applied

[`applyConfChange`](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/raft.go#L1943-L1963) applies the given change to the current configuration, assuming that configuration is the one just before the change. [`restore`](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/raft.go#L1915-L1928) switches to a snapshot's configuration as soon as a follower steps the snapshot, even while the application is still applying a `Ready`'s committed entries ([`Node` steps messages meanwhile](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/node.go#L394-L399)), so a conf change among those entries is applied again on top of a snapshot that includes it. This PR switches to the snapshot's configuration in [`appliedSnap`](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/raft.go#L766-L770), once the application has applied the snapshot, so that the configuration changes in log order.

The first commit adds a test of the issue's example, which fails on `main`; the second, the fix, makes it pass.

With `AsyncStorageWrites`, the snapshot can still be applied before the older entries; the PR for `raft-async-snapshot-during-apply-divergence` fixes that, and the two PRs merge cleanly in either order. I can combine both fixes in one PR if you prefer.

The fix also updates the tests that relied on `restore` switching the configuration (`raft_test.go`,
`raft_snap_test.go`, eight `testdata/` files). Earlier fixes, kept as `backup/...-v1`..`-v5`
branches, were replaced: ignoring the snapshot made the leader's resend depend on `ReportSnapshot`
([`raft-reportsnapshot-finish-not-noop`](../nonissues/raft-reportsnapshot-finish-not-noop.md));
deferring it could make the leader send it twice; keeping the pre-snapshot configuration aside was
more code.

## Notes

The `AsyncStorageWrites` half is [`raft-async-snapshot-during-apply-divergence`](raft-async-snapshot-during-apply-divergence.md),
split off 2026-10-23. Older reproductions (asserting the violation, at raft `40f8be7`) are in
`notes/raft-conf-lag-model/snapshot_during_apply_test.go`.
