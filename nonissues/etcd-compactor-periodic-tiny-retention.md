---
upstream: none
checked: 2026-11-01
links:
  - etcd-io/etcd#22396 pr open: related, not this bug (bounds parseCompactionRetention: rejects negative and overflowing retentions); still accepts a positive retention below 10ns such as `5ns`
  - etcd-io/etcd#9485 pr merged: introduced the retry interval min(period, 1h)/10 and `int(period/retryInterval)+1` retentions (2018), the division that is by zero here
blocks-proof: no
---

# v3compactor: a periodic auto-compaction retention below 10ns crashes etcd at startup

`etcd --auto-compaction-mode=periodic --auto-compaction-retention=5ns` (any retention strictly
between 0 and 10ns) is accepted by the flag parsing and then panics while the server is created:
`runtime error: integer divide by zero`.

**Why not an issue:** an absurd configuration (a periodic retention below 10ns): the proof takes a precondition on it rather than a fix (the user's call, 2026-11-02).

**Expected:** the retention should be rejected with an error, as an unknown
`--auto-compaction-mode` is
([config.go#L999-L1005](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/server/embed/config.go#L999-L1005)).

**Impact:** only a meaningless configuration (a retention needs an explicit `ns` unit, or a fraction
of an hour, to get there); the member fails loudly at startup, with a stack trace instead of an
error message. No running member is affected.

**Reproduction:** `TestPeriodicTinyRetention` in
[`nonissues/etcd-compactor-periodic-tiny-retention/periodic_tiny_retention_test.go`](etcd-compactor-periodic-tiny-retention/periodic_tiny_retention_test.go),
copied (as `zz_periodic_tiny_retention_test.go`) into `server/embed` at
etcd-io/etcd@1573d59416efa220421c451f5266b24a5d8374ef (2026-10-28), go1.27.3; it follows the flag
through `parseCompactionRetention` to the `v3compactor.New` call `NewServer` makes:

```
$ (cd server && go test ./embed -run '^TestPeriodicTinyRetention$' -count=1)
--- FAIL: TestPeriodicTinyRetention (0.00s)
    zz_periodic_tiny_retention_test.go:36: retention 5ns accepted, then v3compactor.New panicked: runtime error: integer divide by zero
FAIL
```

**Cause:** `parseCompactionRetention` accepts any `time.ParseDuration` string in periodic mode
([etcd.go#L928-L947](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/server/embed/etcd.go#L928-L947)),
and `NewServer` creates the compactor for any non-zero retention
([server.go#L384](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/server/etcdserver/server.go#L384)).
`newPeriodic` sizes its revision list with `period / retryInterval`, where the retry interval is
`min(period, 1h) / 10`, zero below 10ns
([periodic.go#L177-L189](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/server/etcdserver/api/v3compactor/periodic.go#L177-L189)).

## Proof

no: a precondition on the configuration, which the top-level adequacy proof takes, not a fix on the goosed fork; `NewServer`'s statement needs the premise that a periodic retention is at least 10ns in absolute
value, which etcd's flag handling does not ensure (`Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3compactor/New.lean`).

## Fix

Make #22396's bound in `parseCompactionRetention` also reject `0 < retention < 10ns` (or a periodic
retention below a sensible minimum, such as a second); a comment on #22396 is likely enough.
