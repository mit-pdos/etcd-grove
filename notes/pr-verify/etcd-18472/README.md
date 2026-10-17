# etcd-io/etcd#18472: tests and probes

Every file here backs a finding in `../etcd-18472.md`. Each Go test passes when the behaviour it
names happens. The PR head is etcd-io/etcd `7842e283ce2e591e78e9c59f5ed287722782ab08`
(`git fetch https://github.com/etcd-io/etcd pull/18472/head`); run upstream checkouts with the
toolchain their `go.mod` names (`GOTOOLCHAIN=go1.26.4` works).

| File | What it shows | Runs against | Command |
|---|---|---|---|
| `pr-head/interval_probe_test.go` | A negative (`-1s`) or tiny (`1ns`) interval makes the revision compactor loop without sleeping (thousands of `Rev()` calls and compactions per 100 ms); in the periodic mode an interval below the sampling period (`min(retention, 1h)/10`) has no effect (retention 1h, interval 1m: one compaction per 6 minutes, 20 in 3 h); a negative periodic interval behaves the same | PR head, `server/etcdserver/api/v3compactor` | `cp pr-head/interval_probe_test.go <checkout>/server/etcdserver/api/v3compactor/ && cd <checkout>/server && go test -v -run TestProbe ./etcdserver/api/v3compactor/` |
| `pr-head/interval_parse_probe_test.go` | `parseCompactionInterval` accepts `-1s`, `-5m`, `1ns` | PR head, `server/embed` | `cp pr-head/interval_parse_probe_test.go <checkout>/server/embed/ && cd <checkout>/server && go test -v -run TestProbe ./embed/` |
| `pr-head/probes.log` | The output of the two above | PR head | |
| `reviewer/reviewer_interval_yaml_test.go` | The config file carries `auto-compaction-interval`; `-1s` and `1ns` pass `Validate()`; a YAML number fails to unmarshal | PR head, `server/embed` | `cp reviewer/reviewer_interval_yaml_test.go <checkout>/server/embed/ && cd <checkout>/server && go test -v -run TestReviewerIntervalYAML ./embed/` |
| `reviewer/probes.log` | Its output (zap's warnings removed) | PR head | |

The verified code is the PR on the Goose fork: `mit-pdos/etcd-grove` branch
`pr-etcd-18472-goose-lean` (commit `f5de5f9c1`); the PR's own unit tests (`v3compactor`, with
`-race`, and `embed`'s `TestAutoCompaction*`) pass there with `GOTOOLCHAIN=go1.27.1`.
