# restart3: handoff (2026-11-15)

Worktree `/shared/etcd-grove-auth3`, branch `restart3` (off `lean` `c3da59fa29`, `restart3-scope` merged).
Plan: `notes/restart3-scope.md` (route (A), decided by the user 2026-11-15). Decisions: `questions.md`.

## Done
- **A0 (stopped at the go/no-go checkpoint)**: `notes/restart3-a0-draft.md`. R2s-A as recorded is blocked
  (a backward install the KV store invariant cannot follow, §2.2); variant A-g (a fork guard deferring a
  merged snapshot in the sender's replay window) recommended (§3).
- Probes (unlinked; checked with `lake env lean`; copies in `notes/restart3-a0/`, working copies in
  `Scratch/`, untracked): `R3A0ProbeKV.lean` (P1), `R3A0ProbeGuard.lean` (P2, P3).
- Go probe of A-g: `notes/restart3-a0/ag-guard.patch` against the fork's `server/v3` (module cache copy at
  `/shared/tmp/restart3-a0/server`), restart3probe setting A, 6/6 (`/shared/tmp/restart3-a0/ag2-run-*.txt`).
- `nonissues/etcd-backward-snapshot-install-panics-watcher.md` (index regenerated).

## Next, in order (after etcd-grove-81's answer)
1. If A-g: g0 the fork commit (guard + `ReportSnapshot`), Go tests, pin bump, `etc/goose.py --project etcd`
   (GOWORK unset); g1 the merge branch (`wp_ci_get`, `probe_P2_guard`); g2 the deletions (Draft §2.3);
   g3 Freeze package (Draft §3.3). Sequenced after auth-lease's `specSnapM` restatement lands.
2. C1-C4 of the Scope (restart3's Go and proofs), the handler swap (D-R3-4).

## Pitfalls
- The probes import server modules: build `EtcdServer__run`/`EtcdServer__applyAll` first (targeted build,
  64G cap); `lake env --packages=/shared/tmp/manifest-ddc.json lean Scratch/<file>`.
- Go probe against a patched fork: `go test -modfile=/shared/tmp/restart3-a0/alt.mod` (a copy of
  `examples/go.mod` with `server/v3` replaced by the local copy), `GOWORK=off`, 32G cap; one run per process.
- `notes/status-history.md` is append-only (check `wc -l` against lean before a commit).

## 2026-11-15 after the checkpoint
- Decisions D-A0-1..5 recorded (`questions.md`). Step 1 (integration test) done: in-window merge reached on a
  graceful path, backward install not reached (Draft §7, the nonissue). Harness: `/shared/tmp/restart3-a0/etcd`
  (etcd at `2eaeb872bc`, `gofail enable`d, the test in `tests/integration/zz_backward_install_test.go`), run with
  `cd tests && GOWORK=off GOPROXY=off GOFLAGS=-mod=mod go test ./integration/ -run TestZZBackwardInstall -v`
  under the 32G cap; `ZZ_EXPECT_DEFER=1` for the A-g run (step 2).
- The fork clone for A1: `/shared/tmp/restart3-a0/etcd-fork` (branch `restart3-ag` off `goose-lean` `2eaeb872b`),
  the A-g change applied, not committed (after step 2).
