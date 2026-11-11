# WAL W3: handoff

Branch `wal-w3`, worktree `/shared/etcd-grove-walw3`, off lean `47d7b2f2cd`. The WAL crash spec's
stage W3 (`/shared/tmp/wal-spec/scope.md`, its Decisions and "Added" sections; W0/W1.5 reports
beside it). Scratch: `/shared/tmp/wal-spec/w3/`.

## Build command

```
export TMPDIR=/shared/tmp LAKE_OPTS=--packages=/shared/tmp/manifest-ddc.json
flock /shared/tmp/etcd-grove-build.lock systemd-run --scope -q -p MemoryMax=64G lake --packages=/shared/tmp/manifest-ddc.json build
```

## The fork commits (local, never pushed: the user pushes them)

`/shared/tmp/wal-spec/w3/etcd` (a clone of upamanyus/etcd), branch `goose-lean-walsync` on
`a4d2bb172` (= `origin/goose-lean`, so a fast-forward of it):
- 41fddbc2d F-Z: `ReadAll` fdatasyncs the tail it zeroed;
- 161796636 F-N1: `Create` fsyncs `<dir>.tmp` before the rename;
- 71f99a4bf F-N2: `TouchDirAll` fsyncs the parent of each directory it creates (+ `TestTouchDirAllNested`).

`etc/goose.py` pins 71f99a4bf; examples/go.mod, k8s/etcd3, k8s/compactor (GO_MOD_PINS) and their
go.sum name `v3.0.0-20261111181426-71f99a4bf417` (hashes from the local commits, through the local
bare repo `/shared/tmp/wal-spec/w3/etcd-bare.git` with `GIT_CONFIG_*` insteadOf, as premise-fixes-2;
the same once pushed). The other go.mods still at a4d2bb172 (premisefix/*, sweeprepairs/*,
k8s7e2attack) are standalone attack tests, not GO_MOD_PINS: left as they were.

Upstream candidates (not pushed): `/shared/tmp/wal-spec/w3/upstream-etcd`, branches
`fix/etcd-wal-readall-zero-unsynced`, `fix/etcd-wal-create-dir-entry-unsynced`,
`fix/etcd-fileutil-touchdirall-parent-unsynced` off etcd main 6974f522338b (wal and fileutil tests
pass on each). Need a `Signed-off-by` before filing.

## Done

- Task 1 (targeted purge + dormant runs): `/shared/tmp/wal-spec/w3/runs/target.sh`, logs `t-*.log`;
  tester copy with `-target` in `/shared/tmp/wal-spec/w3/tester` (and the garbage model changed to
  the user's sector assumption: garbled sectors keep the bytes no write since the sync changed;
  `-weakp4` for the old one).
- Task 2: fork commits; regression tests `TestW3FZ`/`TestW3FN` (W0 harness; copies in
  `nonissues/etcd-wal-readall-zero-unsynced/`, `nonissues/etcd-fileutil-touchdirall-parent-unsynced/`):
  pin fails (C-P5' 4 unsound images; C-P3 131 and 66 acked-Save losses), fixed 0. Tester against the
  fixed fork: `runs/fixed.sh`, logs `f-*.log`.
- Task 3: pin bump + regeneration (one name added, `wal.syncDir`), go.mod/go.sum; nonissues
  (F-Z, F-N1, F-N2, C-W2, C-P6, the Save doc, the sector-write dependence); decisions entry
  "WAL W3".

## Next, in order

See the checkpoint report / STATUS entry; if interrupted: finish the checks (tcb --check,
collections, interfaces, gen-init --check, goose --check with
`--src etcd=/shared/tmp/wal-spec/w3/etcd --perennial /shared/perennial-ddc0f0acc`,
`etc/issues-status.py --index` then `--check`), then STOP before land.sh: the user pushes
`goose-lean-walsync` (and fast-forwards `goose-lean`) first.

## Pitfalls

- `goose.py --check` with `--src` needs the checkout at the pinned HEAD, clean.
- Without the push, CI's goose check and `go mod download` fail; the module cache here has the
  new pseudo-version (downloaded from the bare repo).
- `notes/status-history.md` is append-only.
