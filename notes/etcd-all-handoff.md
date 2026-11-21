# etcd_safe (examples/etcd/all): handoff

## START HERE (2026-11-21, stage E0 done, waiting for decisions)

- Plan: `/shared/tmp/coord-03/etcd-unified-plan.md` (D1-D6 approved 2026-11-21). Scope: `notes/etcd-unified-scope.md`.
- Branch `etcd-all`, worktree `/shared/etcd-grove-etcdall`. Not landed. No Lean touched, nothing built.
- Committed: `examples/etcd/all/{all.go,all_test.go}` (package `etcdall`, examples' Go module): `Main` runs
  the parts `KV`, `Auth`, `Lease`, `Restart` at once, each running its drivers at once (`spawn`).
- At lean, `TestAddrs` FAILS (authN and restartN both on peers 29000+i) and `TestMemberIDs` checks only
  k ≤ 70 (`uniformK`). In a scratch copy with restartN at 14000/15000 everything passes: `TestMainRun` k = 3 in
  30 s, also under `-race` (38 s). Logs and scratch-only tests: `/shared/tmp/etcdall-e0/`.
- Open decisions (scope §7): N1 `lease.leasesNoExpiry` is process-wide, false with leaseexpiryN beside
  authlease/leasecatchup (rec.: leaseexpiryN out now, per-cluster premise later); N2 bounds under the
  cross-cluster `Hlow` (rec.: new tokens, k1 ≤ 1000, others ≤ 300, measured); N3 restartN ports 14000/15000.
- Next (after decisions): E1 Go changes to existing drivers (STOP), then E2 statements (STOP), E3a-e, E4.
- Run Go as: `GOWORK=off PATH=/usr/local/go/bin:$HOME/go/bin:$PATH systemd-run --scope -q -p MemoryMax=32G
  go test -count=1 -run TestMainRun -v ./etcd/all` from `examples/`; never beside the drivers' own tests.
