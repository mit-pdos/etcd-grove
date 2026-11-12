# WAL W4a.1: handoff

Branch `wal-w4a1`, worktree `/shared/etcd-grove-walw3`, cut from lean `491baacae1`. Coordinator:
etcd-grove-81. Scratch: `/shared/tmp/wal-spec/w4a1/`.

## State (2026-11-12)

- `91e927b08f`: `walDiskM` (WalDisk.lean); `Save`/`SaveSnapshot`/`Close` over it (F-W4b-1); VSE's
  second conjunct with `walUnlockedTok` (F-W4b-2). Axiom files from `/shared/tmp/wal-spec/w4a1/gen/genspecs.py`
  (the only source: rerun it with the worktree as argument; round 3's is `genspecs-rev3.py`).
- Go tests `/shared/tmp/wal-spec/w4a1/tests/` (all pass; run in `/shared/tmp/wal-spec/w4/rev-tests/etcd-c90b03b56/server`).
- Full build passes (17335 jobs, `/shared/tmp/wal-spec/w4a1/build.log`); checks `/shared/tmp/wal-spec/w4a1/checks.log`.
- Freeze package: `/shared/tmp/wal-spec/w4a1/freeze-w4a1.md`. **Waiting for the delta review; STOP
  before `etc/land.sh`** (merge lean first, rerun the checks).

## Next

After it lands: W4b (branch `wal-w4b`, `notes/wal-w4b-handoff.md` there) merges lean; Part B's
`walDiskM` views (B1) then proceed.
