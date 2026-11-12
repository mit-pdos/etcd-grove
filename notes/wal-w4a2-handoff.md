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

## Done (2026-11-12, the second agent)

1. Fork commit `0b50f0426` on `goose-lean-exist` (`/shared/tmp/wal-spec/w4/etcd-exist`, local, never
   pushed): `w.snapi`, a cut names its file `max(w.enti, w.snapi)+1`; tests
   `segment_name_snapshot_test.go` (`TestRestartAtSnapshotSavedBeforeReSentEntries`, fails at
   `1aaca041c` at the name 39) and `TestReadAllStartRecordBeforeOpenedFile` adjusted (matched now).
2. Pin bump `316ae9997b` (goose.py, examples' go.mod pseudo-version `v3.0.0-20261112123031-0b50f04262d9`;
   go.sum needs the push; translation: 0 files); nonissue updated, its tests directory holds the
   fork's two test files. Go tests at the pin: `/shared/tmp/wal-spec/w4a2/etcd` moved to `0b50f0426`,
   77 pass (`tests/gotests-pin2.log`); `w4a2_wrap_test.go`'s unmatched and relaxed-clause-1 tests
   updated for the naming fix (copy `tests/w4a2_wrap_pin2_test.go`).
3. `walLastIdx` (max of the last entry's index and the highest snapshot index) replaces
   `walLastEntIdx` (`2fdfc123fd`); generator regenerated (`gen/genspecs.py`, backup
   `genspecs.py.pre-naming`); probe's `mkBounds` mirrored (`r2/r4a2.go.pre-naming` the old one).
4. Probes rerun on the new binary (old runs killed and moved to `r2/old-1aaca041c/`); full build,
   checks: see the Freeze package §3.2/§6.
5. Freeze package `/shared/tmp/wal-spec/w4a2/freeze-w4a2.md`.

## Revision 1 (2026-11-12, after the Freeze review: NOT READY, B1)

Done: `acee5acbed` (Save/SaveSnapshot index premises, walGuardPos wrap first, wording, nonissue
`etcd-wal-segment-name-wraps`, decisions.md "Revision 1"); Go tests incl. the reviewers' at the pin
(`tests/gotests-rev1.log`); kill-then-power probe `r2/run5.sh` (`r2/kpl-*`); freeze-w4a2.md
"Revision 1". Generator backup before it: `gen/genspecs.py.pre-rev1`.

## Next

6. STOP for the coordinator's review. Do not land. Before landing: merge lean (it moved a lot:
   fs-merge), then move the oldest STATUS "Last updated" entry (WAL W3, 2026-11-11) to
   `notes/status-history.md`'s list (not done here: this branch's status-history is shorter than
   lean's until the merge, and the file is append-only).

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
