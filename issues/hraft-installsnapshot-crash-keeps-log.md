---
upstream: known
checked: 2026-11-28
links:
  - hashicorp/raft#721 issue open: the bug at upstream (InstallSnapshot keeps divergent entries below the snapshot); this file is what a fix of it must also cover
blocks-proof: yes
---
# raft: a crash inside `InstallSnapshot` keeps the log the install was to discard, and a restarted leader replicates conflicting entries

A follower installing a snapshot that its log does not match must discard its log (Raft, Fig. 13,
steps 6-7; upstream #721 is that it does not). `installSnapshot` makes the snapshot durable (the
sink's `Close`) first and touches the log only after the state machine's restore. A server that
crashes in between restarts with the snapshot at `(S, T)` and its old log, whose entries below `S`
may conflict with the committed entries the snapshot stands for, and `NewRaft` keeps that log as it
is. Elected (its last entry is the snapshot's, so it can be), it repairs a lagging follower from its
own log and sends it those stale entries with a commit index past them: the follower applies
entries that conflict with committed ones.

**Expected:** a restart should not bring back a log an install was discarding: `NewRaft` should
finish the discard when the latest snapshot's last entry is not in the log but entries it covers are.

**Impact:** at upstream, every install over a conflicting log (#721), crash or not; with #721 fixed
the way the fork does (discard after the restore), only a crash between the snapshot's `Close` and
the discard. Present in v1.8.0 and `main`.

**Reproduction:** `TestCrashInInstallSnapshotKeepsConflictingLog` in
[`issues/hraft-installsnapshot-crash-keeps-log/install_test.go`](hraft-installsnapshot-crash-keeps-log/install_test.go)
(dsverify-lab's `repro-installcrash`, unchanged: the crash image taken as the sink closes), run by
[`issues/hraft-harness/run.sh`](hraft-harness/README.md) against hashicorp/raft@dd4346dbb127
(`main`, 2026-11-23) and v1.8.0 (`0f543c0`), and the verification fork without this fix (its #721
fix, `5c0b97e`), go1.26.0 linux/amd64; all three fail:

```
$ issues/hraft-harness/run.sh ../raft 3 hraft-installsnapshot-crash-keeps-log
hraft-installsnapshot-crash-keeps-log: 3 failed, 0 passed
    install_test.go:269: F, restarted with its snapshot at (8, 3) and leader of term 4, sent entries
      below its snapshot from the log the install was to discard: [G: entry (2, term 2) G: entry (3, term 2) ...]
```

**Cause:** [`installSnapshot`](https://github.com/hashicorp/raft/blob/dd4346dbb127604c840301273c1441db09728bad/raft.go#L1928-L1972) closes the sink before it restores and
compacts; `NewRaft` restores the latest snapshot and keeps the log whatever it holds.

## Proof

yes: the verification fork's `NewRaft`, after restoring a snapshot at `(S, T)`, deletes the log if it
holds entries at or below `S` but not `(S, T)` itself (dsverify-lab's reference fix `0002`,
`examples/dsverify/hraft/api.go`; branch `hraft-r0-fixes/2026-11-28`, pending approval, #48), as
`installSnapshot` would have. The test passes on the fork with it (10 of 10).
