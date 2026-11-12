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

## Decision (2026-11-12): naming fix approved

The user approved the naming fix via etcd-grove-81 (questions.md): a second fork commit after
`1aaca041c` (which stays), a cut naming its segment `max(w.enti, highest snapshot index saved or
decoded) + 1`. Why: the probe hit an unmatched restart in a raft-like history (posix.r2log,
`UNMATCHED restart at (41,3)`; `/shared/tmp/wal-spec/w4a2/tests/w4a2_forgotsnap_test.go`: old pin
masked read right, `1aaca041c` restart fails). Prototype: `/shared/tmp/wal-spec/w4a2/naming-fix-prototype.diff`
(scratch worktree `/shared/tmp/wal-spec/w4a2/etcd-naming`, uncommitted): the forgotten-snapshot
restart succeeds; all wal tests pass except the name assertions of `TestReadAllStartRecordBeforeOpenedFile`
and `TestW4a2ForgottenSnapshotRestart`, whose scenarios are no longer unmatched.

**Probes still running** (started on the `1aaca041c` build): `/shared/tmp/wal-spec/w4a2/r2/run.sh`, output
`/shared/tmp/wal-spec/w4a2/r2/{kill,ordered,posix,target}.log` (summary line at the end) and `.r2log`
(`EV`, `EVBAD`, `C2FAIL`, `UNMATCHED`, `ADOPT` lines). Interim: 0 EVBAD; C2FAIL with inp=true in all
runs (a higher snapshot in a purged prefix: the entries-only lower bound is too weak; step 3 fixes
it). Their results are superseded by step 4's rerun.

## Next, in order

1. **Naming-fix fork commit, with tests**: in `/shared/tmp/wal-spec/w4/etcd-exist` (branch
   `goose-lean-exist`, at `1aaca041c`) apply the prototype; adjust `TestReadAllStartRecordBeforeOpenedFile`
   (now matched: expect success, the segment named above 5) and add a test that fails before
   (the forgotten-snapshot restart, `w4a2_forgotsnap_test.go`, asserting success and Open selecting
   the file holding the record). Commit as Frans Kaashoek with the Co-Authored-By line; never push.
2. **Pin bump**: `etc/goose.py` rev + comment; examples' go.mod (examples, k8s/etcd3, k8s/compactor)
   pseudo-version from the commit's UTC time; `etc/goose.py --project etcd --src etcd=<checkout>`
   (do not export GOWORK=off there); go.sum needs the push (note it). Update the nonissue's Proof
   section (both fork commits; etcd's restart kept) and run `etc/issues-status.py --index/--check`.
   Re-run the wal Go tests at the new pin (`/shared/tmp/wal-spec/w4a2/etcd`: move it to the new
   commit; update the W4a.2 tests whose scenarios changed).
3. **Model**: `walLastEntIdx` → a lower bound that also counts snapshot records
   (max of the last entry index and the highest snapshot index of the prefix), in `WalDisk.lean`;
   the argument in docstrings (name > every snapshot record before it, so every restart at a
   snapshot of the history matched); regenerate through the generator (docstrings mentioning the
   bound and `1aaca041c` → both commits); mirror in the probe (`r4a2.go` `mkBounds`).
4. **Rerun the probes** (rebuild `wal-r4a2.test` against the new fork worktree; `run.sh`): expect 0
   EVBAD, 0 UNMATCHED, and C2FAIL only outside `k ≤ p`. Then full build (flock, 64G), tcb --check,
   api-check, gen-interface --check (absdisk), all Go tests.
5. **Freeze package** `/shared/tmp/wal-spec/w4a2/freeze-w4a2.md`: old → new texts (five axioms,
   `walReleasePos`/`walOpenPos`/`walGuardPos`/`walNameBound`, guard clause 4), the argument, the
   findings F-W4a2-1/2 and the forgotten-snapshot case, the evidence (probes, tests), the review
   checklist applied to each axiom. STATUS entry.
6. **STOP** for the coordinator's review. Do not land.

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
