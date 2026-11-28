---
upstream: none
checked: 2026-11-28
links:
  - hashicorp/raft#728 issue open: related (NewRaft's configuration scan on restart), a different bug
  - hashicorp/raft#741 issue open: related (appendEntries and the snapshot boundary), a different bug
  - hashicorp/raft#697 issue open, hashicorp/raft#721 issue open: related (installSnapshot keeping the log), different bugs
blocks-proof: yes
---
# raft: after a restart whose log ends below the snapshot, a delayed AppendEntries rolls the latest configuration back

`appendEntries` decides which of a request's entries are new by comparing each index with the raw
last log index, `lastLogIdx, _ := r.getLastLog()`, not with the last index the server holds, which
includes its snapshot (`getLastEntry`). Every entry past that raw index is stored again, and
`processConfigurationLogEntry` is run on it: `setCommittedConfiguration(latest)`, then
`setLatestConfiguration(entry)`. A running server keeps `lastLog` at or above its snapshot, because
`installSnapshot` sets it to the snapshot's last entry. A restarted server does not: `NewRaft` sets
`lastLog` from the log store and only restores the snapshot. After an `InstallSnapshot` that
discarded the log, followed by a restart, the raw last index is below the snapshot's. A reordered
`AppendEntries` of the same term that carries entries the snapshot covers (prev = 0 is not
checked) is then accepted. Its configuration entries are re-applied, and the server's latest
configuration rolls back to an older one, below its snapshot's configuration.

**Expected:** entries at or below the server's last index (its snapshot's included) are not new, so
they should not be stored or applied as configuration changes again. Equivalently, `NewRaft` should
set `lastLog` to the snapshot's last entry when the log store's last index is below it, as
`installSnapshot` does.

**Impact:** the server's latest configuration (what `GetConfiguration` returns, and what its
elections and replication use) becomes an older configuration than the committed one in its
snapshot. In the test, it becomes `{F, A}` while the committed configuration is `{F, A, B, D}`: as a
candidate it would count a quorum of the wrong configuration. Present in v1.8.0 and `main`.

**Reproduction:** `TestRestartOverSnapshotWithEmptyLogRollsBackConfiguration` in
[`issues/hraft-restart-empty-log-config-rollback/rollback_test.go`](hraft-restart-empty-log-config-rollback/rollback_test.go).
It runs one real server F; the test plays the leader A, delivering RPCs through F's transport
consumer, and the schedule is deterministic:
1. F is bootstrapped with `{F, A, B}`.
2. A sends F a snapshot at (4, 2) with the configuration `{F, A, B, D}` at index 3; A's log is
   1: `{F, A, B}`, 2: `{F, A}`, 3: `{F, A, B, D}`, 4: a command.
3. F shuts down and restarts from its stores.
4. A's earlier `AppendEntries` of term 2 arrives: prev = 0, entries 1-2.

Run by [`issues/hraft-harness/run.sh`](hraft-harness/README.md) against hashicorp/raft v1.8.0
(`0f543c0`), `main` (`dd4346dbb127`, 2026-11-23) and the verification fork with R0's fixes
(`examples/dsverify/hraft`), go1.26.0 linux/amd64. All three fail, 3 of 3 runs:

```
$ issues/hraft-harness/run.sh <raft> 3 hraft-restart-empty-log-config-rollback
hraft-restart-empty-log-config-rollback: 3 failed, 0 passed
    rollback_test.go:156: F (snapshot at (4, 2) with the committed C2 = {F, A, B, D}) took A's delayed
      entries 1-2 (success true) and rolled its latest configuration back to [{Voter F F} {Voter A A}]
```

**Cause:** [`appendEntries`](https://github.com/hashicorp/raft/blob/dd4346dbb127604c840301273c1441db09728bad/raft.go#L1527-L1533)
uses `getLastLog`'s raw index to find the new entries.
[`NewRaft`](https://github.com/hashicorp/raft/blob/dd4346dbb127604c840301273c1441db09728bad/api.go#L599-L602)
sets `lastLog` from the log store before restoring the snapshot, and never raises it to the
snapshot's.

## Proof

yes: the proof of `appendEntries` needs the raw last index to be at least the snapshot's (otherwise the
re-processed configuration entries break `cfgFacts`, the configurations' invariant against the
protocol log). The proposed fork fix (R5's Q1 option (ii), pending coordinator-E's approval): `NewRaft`
sets `lastLog` to `(snapIdx, snapTerm)` when `lastLog.Index < snapIdx` after the restore, which makes
`lastLogIndex ≥ lastSnapshotIndex` an invariant.

## Upstream status

Searched hashicorp/raft's issues and PRs on 2026-11-28 ("snapshot restart", "lastLog", "NewRaft lastLog
snapshot index", "configuration rollback restart snapshot", "getLastLog appendEntries snapshot"): no report
of this bug. The nearest are #741 (a matching predecessor at the snapshot boundary rejected), #728, #697 and
#721, each a different bug.

## Fix (the verification fork, fix 4; approved by coordinator-E, #48)

`NewRaft`, after the snapshot restore and fix 2: if `lastLog.Index` is below the restored snapshot's index,
set `lastLog` (and `setLastLog`) to the snapshot's last entry, as `installSnapshot` does
(`examples/dsverify/hraft/api.go`). With it the test passes (3/3), and so do the other three R0 issue tests
on the fork; the fork's own `go test .` passes.

