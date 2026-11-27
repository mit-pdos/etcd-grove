---
upstream: none
checked: 2026-11-27
links:
  - hashicorp/raft#721 issue open: related, not this bug: InstallSnapshot keeps divergent entries below the snapshot
  - hashicorp/raft#728 issue open: related, not this bug: configuration entries lost on restart (RestoreCommittedLogs)
blocks-proof: yes
---
# raft: `InstallSnapshot` that keeps the log forgets a newer configuration entry in it, and two leaders commit different entries at one index

A follower that installs a snapshot and keeps its log entries after the snapshot sets its latest
configuration to the snapshot's, even when a kept entry holds a newer configuration (an uncommitted
`AddVoter`). It then counts votes and commitment in the older configuration: with `{L, A, F}` in the
snapshot and `{L, A, F, X}` in its log, it leads with two votes of four and commits entries only `A`
acknowledges, while `L` and `X`, after one more change, commit different entries at the same indexes.

**Expected:** a server should use the latest configuration in its log (Raft, §4.1), after a snapshot
install as after a restart (`NewRaft` rescans the entries after the snapshot).

**Impact:** a cluster changing its membership while a follower falls behind the leader's compacted log
and receives a snapshot although it already holds entries after the snapshot's index (a lost
AppendEntries response); the follower's later elections and commits use a stale configuration, and
two leaders can commit different entries at one index. Present in v1.8.0 and `main`.

**Reproduction:** `TestSnapshotInstallKeepsOlderConfiguration` in
[`issues/hraft-installsnapshot-drops-newer-configuration/config_test.go`](hraft-installsnapshot-drops-newer-configuration/config_test.go),
run by [`issues/hraft-harness/run.sh`](hraft-harness/README.md) against hashicorp/raft@dd4346dbb127
(`main`, 2026-11-23) and v1.8.0 (`0f543c0`), go1.27.3 linux/amd64:

```
$ issues/hraft-harness/run.sh ../raft 5 hraft-installsnapshot-drops-newer-configuration
hraft-installsnapshot-drops-newer-configuration: 5 failed, 0 passed
    config_test.go:589: state-machine safety violated: at index 9 S3 applied "b" but S1 applied "c"
```

**Cause:** [`installSnapshot`](https://github.com/hashicorp/raft/blob/dd4346dbb127604c840301273c1441db09728bad/raft.go#L1959-L1961) sets the latest and the committed configuration
to the snapshot's and then only compacts the log; the kept entries' configurations are never
processed again (`appendEntries` skips entries it already holds).

## Proof

yes: the verification fork, when it keeps the log, takes the latest configuration from the entries
after the snapshot (fork `cc3148d`, `examples/dsverify/hraft/raft.go`'s `installSnapshot`; it keeps the
log only if it holds the snapshot's last entry, fork `5c0b97e`, #721).
