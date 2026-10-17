# etcd-io/etcd#22095: tests and probes

Go tests written for the findings of `notes/pr-verify/etcd-22095.md`, named as they would be in
etcd's tree, with the logs of their runs. Go toolchain `go1.27.1`; run from etcd's `server/`
directory of the named checkout (`GOTOOLCHAIN=go1.27.1`).

| File | Shows | Runs against | Command |
|---|---|---|---|
| `pr-head/autoperiodic_probe_test.go` | once `Size()` is above the high-water mark, the auto-periodic mode compacts at every cooldown (10 compactions in 10 minutes) with a growth rate of 0 and one write per sample: `Size()` is the file size, which compaction does not lower | the PR head `b67f4119a` (etcd-io/etcd, `pull/22095/head`) | `cp pr-head/autoperiodic_probe_test.go <checkout>/server/etcdserver/api/v3compactor/ && go test -run TestAutoPeriodicCompactsEveryCooldownOnceAboveHighWater -v ./etcdserver/api/v3compactor/` |
| `pr-head/compaction_retention_probe_test.go` | `parseCompactionRetention` accepts a duration (`5m` → 300,000,000,000 revisions) and a negative duration (`-1h`) in the new `auto-periodic` mode, as it does in the revision mode | the PR head `b67f4119a` | `cp pr-head/compaction_retention_probe_test.go <checkout>/server/embed/ && go test -run TestParseCompactionRetentionDurationInRevisionMode -v ./embed/` |
| `pr-head/probes.log` | the output of the two tests above | | |
| `pin/compaction_retention_unit_test.go` | the same in the existing revision mode, and a negative duration accepted in the periodic mode (`issues/etcd-compaction-retention-duration.md`) | the etcd pin, `upamanyus/etcd` `09669450f` (= upstream `main` for these files) | `cp pin/compaction_retention_unit_test.go <checkout>/server/embed/ && go test -run TestParseCompactionRetentionRevisionModeDuration -v ./embed/` |
| `pin/periodic_negative_retention_test.go` | the periodic compactor with retention `-1h` spins without sleeping and compacts at the current revision (no history kept) (`issues/etcd-compaction-retention-duration.md`) | the etcd pin `09669450f` | `cp pin/periodic_negative_retention_test.go <checkout>/server/etcdserver/api/v3compactor/ && go test -run TestPeriodicNegativeRetention -v ./etcdserver/api/v3compactor/` |
| `pin/periodic_tiny_retention_test.go` | `New` in the periodic mode panics (integer divide by zero) for a retention of 1 to 9 ns, which the flag parser accepts (`issues/etcd-compaction-retention-duration.md`); uses the fakes of `periodic_negative_retention_test.go` (copy both) | the etcd pin `09669450f` | `cp pin/periodic_*_test.go <checkout>/server/etcdserver/api/v3compactor/ && go test -run TestPeriodicTinyRetentionPanics -v ./etcdserver/api/v3compactor/` |
| `pin/probes.log` | the output of the three tests above | | |
| `reviewer/reviewer_v3compactor_test.go` | the reviewer's: `TestReviewerNewPeriodicTinyRetentionPanics` (the same panic through the PR's `New`), `TestReviewerEtaOverflow` (the logged `projected-time-to-high-water` wraps and then reads `0s` once the size is above the high-water mark and the rate decays), `TestReviewerStopThenWriteTuningRace` (under `-race`: `Stop` does not wait for the goroutine, which keeps reading `AutoPeriodicSampleInterval`; a write after `Stop`, as the PR's `embed` test's deferred `restore`s do after `e.Close()`, is a data race) | the PR head `b67f4119a` | `cp reviewer/reviewer_v3compactor_test.go <checkout>/server/etcdserver/api/v3compactor/ && go test -run 'TestReviewer(NewPeriodic|Eta)' -v ./etcdserver/api/v3compactor/ && go test -race -run TestReviewerStopThenWriteTuningRace ./etcdserver/api/v3compactor/` (the last fails: the race) |
| `reviewer/reviewer_embed_test.go` | `TestReviewerAutoPeriodicQuotaDisabled` (with `QuotaBackendBytes = -1`, quota disabled, the auto-periodic compactor gets `maxBytes` = 2 GiB), `TestReviewerParseTinyPeriodic` (`5ns` accepted) | the PR head `b67f4119a` | `cp reviewer/reviewer_embed_test.go <checkout>/server/embed/ && go test -run TestReviewer -v ./embed/` |
| `reviewer/probes.log` | the output of the reviewer's tests | | |

The verified code is the PR applied to the Goose fork: `mit-pdos/etcd-grove` branch
`pr-etcd-22095-goose-lean` (commit `9062c42a4`, onto the fork's `goose-lean` `09669450f`).
