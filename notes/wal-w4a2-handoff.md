# WAL W4a.2: handoff

Branch `wal-w4a2`, worktree `/shared/etcd-grove-wal4a1` (the W4a.1 build merged with lean), cut from
lean `9b00c0c988`. Coordinator: etcd-grove-81. Scratch: `/shared/tmp/wal-spec/w4a2/`.

Task: R1/R2 (the purge model's completeness, freeze-w4a1.md §R1b) and the W4c gate (`Open`, `ReadAll`,
`Repair`, `Exist` logically atomic, §R1.4).

## State (2026-11-12): hard stop after step 1 (design)

- Design: `/shared/tmp/wal-spec/w4a2/design.md`.
- Soundness findings in landed text (§1 there), each with a passing Go test
  (`/shared/tmp/wal-spec/w4a2/tests/w4a2_wrap_test.go`, copied into
  `/shared/tmp/wal-spec/w4/rev-tests/etcd-c90b03b56/server/storage/wal/`; log `tests/wrap.log`):
  - F-W4a2-1: the cut's name `enti+1` wraps at 2^64-1; the `walRelGuard` branch of `walReleasePos`
    (Open, ReleaseLockTo, ReadAll) is unsound.
  - F-W4a2-2: an unmatched restart (masked `ErrSnapshotNotFound`) leaves `enti` low; the guard branch
    is unsound, and `ReadAll`'s result is wrong (model reads an entry Go does not return).
  - R2's relaxation of clause 1 (drop j = p+1) is unsound.
- Waiting for etcd-grove-81: fix F-W4a2-2 by (A) the fork fix (ReadAll reports ErrSnapshotNotFound;
  recommended) or (B) a history premise on ReadAll.

## Next (after the decision)

1. Probes (design §6): fork copy with (A); tester copy re-pointed; `r4a2.go` with file positions per
   candidate across restarts; 3 models x 150 chains + target.
2. Implement through `/shared/tmp/wal-spec/w4a2/gen/genspecs.py` (copy of W4a.1's), `WalDisk.lean`
   (`walLastEntIdx`, `walHasMaxIdx`, `walCutPos`, `walNameBound`, `walGuardPos`, `walReleasePos`,
   `walOpenPos`, guard clause 4), `WalBodies.lean`; checks; Freeze package `freeze-w4a2.md`.

## Pitfalls

- Go tests: `GOWORK=off`, `PATH=/usr/local/go/bin:$HOME/go/bin:$PATH`, `systemd-run --scope -q -p MemoryMax=32G`.
  Never export GOWORK=off in a shell that runs etc/land.sh, gates.sh or goose.py.
- `notes/status-history.md` is append-only.

## Build command

```
export TMPDIR=/shared/tmp
systemd-run --scope -q -p MemoryMax=64G lake --packages=/shared/tmp/manifest-ddc.json build Proof.go_etcd_io.etcd.server.v3.storage.WalBodies
# full: flock /shared/tmp/etcd-grove-build.lock systemd-run --scope -q -p MemoryMax=64G lake --packages=/shared/tmp/manifest-ddc.json build
```
