---
upstream: unchecked
checked: 2026-10-17
links:
  - etcd-io/etcd#22396 pr open: rejects a negative or overflowing --auto-compaction-retention (covers the negative duration, and its busy loop in the periodic mode); does not cover a duration in the revision mode
---

# A duration `--auto-compaction-retention` is misread in the revision mode; a negative or tiny one is accepted

- **Status**: open: a validation gap (an option value the documentation allows is silently
  misread), and a negative duration that is accepted and makes the periodic compactor spin and
  compact away all history; and a periodic retention of 1 to 9 ns (`5ns`), accepted, which panics
  the server at startup. Found while verifying etcd#22095 (the auto-periodic mode, which
  reads the retention as the revision mode does).
- **Where**: `server/embed/etcd.go` at the pinned revision (`upamanyus/etcd` `09669450f`, the
  same code as upstream `main`): `parseCompactionRetention` (lines 928–948): an integer is
  hours in the periodic mode and a revision count in the revision mode; anything else goes to
  `time.ParseDuration`, whatever the mode, and a negative result is not rejected. The option's
  documentation (`server/embed/config.go:273–277`, `Config.AutoCompactionRetention`): "either
  duration string with time unit (e.g. '5m' for 5-minute), or revision unit (e.g. '5000')".
  `server/etcdserver/server.go:383` starts the compactor whenever the retention is non-zero;
  `server/etcdserver/api/v3compactor/revision.go:81` (`rev := rc.rg.Rev() - rc.retention`) and
  `periodic.go:171–189` (`getCompactInterval`, `getRetentions`: `period / getRetryInterval()`, `getRetryInterval`: `period / retryDivisor`) use it as is.
- **What happens**:
  - `--auto-compaction-mode=revision --auto-compaction-retention=5m` gives a retention of
    300,000,000,000 revisions (the duration's nanoseconds, `int64(retention)` in
    `v3compactor.New`): the compactor never compacts (`rev <= 0` at every interval), and
    nothing says so.
  - `--auto-compaction-retention=-1h` is accepted in every mode. In the revision mode the
    retention is negative and every compaction is asked at a revision above the current one
    (`mvcc.ErrFutureRev`), failing every 5 minutes. In the periodic mode the retry interval is
    negative, `clock.After` fires at once, and the compactor's goroutine spins without sleeping;
    its first compaction is at the store's current revision, keeping no history.
  - `--auto-compaction-mode=periodic --auto-compaction-retention=5ns` (any retention of 1 to
    9 ns, either sign) is accepted, and `v3compactor.New` panics with "integer divide by zero"
    (`getRetryInterval` is `period / 10 = 0` and `getRetentions` divides by it) in
    `NewServer`: the server does not start, with a runtime panic rather than an error.

  Reproductions, in `notes/pr-verify/etcd-22095/pin/` of branch `pr-verify/etcd-22095`
  (`compaction_retention_unit_test.go` for `server/embed`; `periodic_negative_retention_test.go`
  and `periodic_tiny_retention_test.go`, which uses the former's fakes, for
  `server/etcdserver/api/v3compactor`; all pass at `09669450f`, i.e. the behaviours happen;
  `pin/probes.log`):

  ```
  mode revision, retention "5m": revisions to keep = 300000000000 (no error)
  mode revision, retention "-1h": revisions to keep = -3600000000000 (no error)
  mode periodic, retention "-1h": -1h0m0s (no error)
  in 100ms: 56029 calls to Rev() (the loop does not sleep); compactions at [1000] (store at revision 1000)
  New(periodic, 5ns): recovered panic: runtime error: integer divide by zero
  ```
- **Expected**: in the revision mode a duration is not a revision count: reject it at startup
  (or document that only an integer is allowed there); reject a negative retention in every
  mode (etcd#22396 does the latter); reject a periodic retention below `retryDivisor` ns.
- **How the proof handles it**: the compactors' constructors and loops are not verified on
  `lean` (v3compactor is names-only). On branch `pr-verify/etcd-22095`, the spec of the
  auto-periodic compactor's `Run` (`Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3compactor/AutoPeriodic__Run.lean`)
  has the premise `0 ≤ sint.Z P.retention`: with a negative retention its compaction would not
  keep `retention` revisions; the postulate of the periodic compactor's constructor
  (`Spec/.../v3compactor/newPeriodic.lean`) and `New`'s spec have the premise that a periodic
  retention is at least 10 ns in absolute value (found by the review of that verification: the
  postulate first said it always returns); `embed` is not translated.
- **Possible fixes**: in `parseCompactionRetention`, return an error for a negative result or a
  periodic one below 10 ns, and,
  for the revision (and auto-periodic) modes, for a value that is not an integer.
- **Found**: 2026-10-17, while specifying `v3compactor.AutoPeriodic.Run` for etcd#22095 (the
  retention premise), then checked against the revision and periodic compactors by the tests
  above.
