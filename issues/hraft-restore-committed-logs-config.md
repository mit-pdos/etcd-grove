---
upstream: known
checked: 2026-11-28
links:
  - hashicorp/raft#728 issue open: this bug
  - hashicorp/raft#731 pr open: a fix (the configuration scan from the snapshot's index)
blocks-proof: yes
---
# raft: a server restarting with `RestoreCommittedLogs` loses the configurations in the entries it replays, and counts votes and commitment in an older one

With `RestoreCommittedLogs`, `NewRaft` replays the committed entries after the latest snapshot into
the state machine, and then looks for configuration entries only after the last entry replayed: the
configurations among the replayed entries are never taken. The server's latest and committed
configuration fall back to the snapshot's (or none), though its log holds newer, committed ones, and
it elects itself and commits entries in that older configuration: with `{F, A, B}` in its snapshot
and `{F, A, B, X, Y}` committed in its log, F leads with A's vote alone and commits an entry only F
and A hold.

**Expected:** a server should use the latest configuration in its log (Raft, §4.1; `NewRaft`'s
configuration scan after the snapshot), with `RestoreCommittedLogs` as without it.

**Impact:** deployments that enable `RestoreCommittedLogs` (opt-in, with a `CommitTrackingLogStore`)
and change their membership: after a restart a server may lead and commit in a stale configuration,
and two leaders may commit different entries at one index. Present in v1.8.0 and `main`.

**Reproduction:** `TestRestoreCommittedLogsDropsConfigurations` in
[`issues/hraft-restore-committed-logs-config/restore_test.go`](hraft-restore-committed-logs-config/restore_test.go)
(dsverify-lab's `repro-restorecommitted`, unchanged), run by
[`issues/hraft-harness/run.sh`](hraft-harness/README.md) against hashicorp/raft@dd4346dbb127
(`main`, 2026-11-23) and v1.8.0 (`0f543c0`), go1.26.0 linux/amd64:

```
$ issues/hraft-harness/run.sh ../raft 3 hraft-restore-committed-logs-config
hraft-restore-committed-logs-config: 3 failed, 0 passed
    restore_test.go:207: after the restart F's log holds the configuration {F, A, B, X, Y} at index 4
      (committed), but F's configuration is {[{Voter F F} {Voter A A} {Voter B B}]}
    restore_test.go:221: F, leader of term 3, committed its no-op and a barrier acknowledged by F and A
      only; the latest configuration in its log, {F, A, B, X, Y}, needs three
```

**Cause:** [`restoreFromCommittedLogs`](https://github.com/hashicorp/raft/blob/dd4346dbb127604c840301273c1441db09728bad/api.go#L724-L755) applies the entries up to the stored
commit index (`processLogs`, which sets `lastApplied`) without processing their configurations, and
[`NewRaft`'s scan](https://github.com/hashicorp/raft/blob/dd4346dbb127604c840301273c1441db09728bad/api.go#L611-L623) starts at `max(snapshot index, lastApplied) + 1`.

## Proof

yes: the verification fork scans every entry after the snapshot and takes the latest configuration
as committed when the restored commit index reaches it (dsverify-lab's reference fix `0001`,
`examples/dsverify/hraft/api.go`'s `NewRaft`; branch `hraft-r0-fixes/2026-11-28`, pending approval,
#48). The kit's restartable servers draw `RestoreCommittedLogs` at random. The test passes on the fork
(10 of 10).
