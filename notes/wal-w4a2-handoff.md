# WAL W4a.2: handoff

Branch `wal-w4a2`, worktree `/shared/etcd-grove-wal4a1` (the W4a.1 build merged with lean), cut from
lean `9b00c0c988`. Coordinator: etcd-grove-81. Scratch: `/shared/tmp/wal-spec/w4a2/`.

Task: R1/R2 (the purge model's completeness, freeze-w4a1.md §R1b) and the W4c gate (`Open`, `ReadAll`,
`Repair`, `Exist` logically atomic, §R1.4).

## State (2026-11-12)

- Step 1 (design, `/shared/tmp/wal-spec/w4a2/design.md`) done; hard stop answered by etcd-grove-81
  (questions.md, "W4a.2"): fork fix approved by the user; ReleaseLockTo atomic too; findings folded
  into the Freeze package and decisions.md.
- Fork: `1aaca041c` on `goose-lean-exist` (worktree `/shared/tmp/wal-spec/w4/etcd-exist`), LOCAL,
  not pushed. Pin bump committed (`b6c8c037f8`): `etc/goose.py`, examples' go.mod (go.sum needs the
  push), nonissue corrected. Go tests at the new pin: `/shared/tmp/wal-spec/w4a2/etcd` (a worktree at
  1aaca041c with the W4a/W4a.1/W4a.2 tests; log `tests/gotests-pin.log`).
- Probes: `/shared/tmp/wal-spec/w4a2/r2/run.sh` (kill, ordered, posix, target; 150 chains each);
  analysis: `grep '^EV' *.r2log`, `EVBAD`, `C2FAIL`, `UNMATCHED`, `ADOPT`.
- Lean: `WalDisk.lean` (walLastEntIdx, walHasMaxIdx, walCutPos, walRelGuard clause 4, walGuardPos,
  walNameBound, walReleasePos, walOpenPos); five axiom files from
  `/shared/tmp/wal-spec/w4a2/gen/genspecs.py`; `WalBodies.lean` (walOpen_commit,
  walReleaseLockTo_commit, walReadAll_commit); docstrings in Impl/Specs; decisions.md entry.

## HARD STOP (2026-11-12, second): the fork fix costs etcd a restart

The probe hit one unmatched restart in a raft-like history (posix.r2log, `UNMATCHED restart at (41,3)`),
reproduced in `/shared/tmp/wal-spec/w4a2/tests/w4a2_forgotsnap_test.go` (old pin: masked read right;
new pin: restart fails). Proposed: a fork naming fix (cut names `max(enti, highest snapshot index
saved/decoded)+1`); awaiting etcd-grove-81. The Lean below is consistent with the approved fix
(1aaca041c) and builds; with the naming fix, `walLastEntIdx` could count snapshot records.

## Next

1. Probe results into the Freeze package; full build (`build.log`), tcb --check, api-check,
   gen-interface (absdisk), all Go tests.
2. `/shared/tmp/wal-spec/w4a2/freeze-w4a2.md`; STATUS entry; STOP for review.

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
