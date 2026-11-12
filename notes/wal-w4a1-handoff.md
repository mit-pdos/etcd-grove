# WAL W4a.1: handoff

Branch `wal-w4a1`, worktree `/shared/etcd-grove-wal4a1` (round 0 was in `/shared/etcd-grove-walw3`), cut
from lean `491baacae1`. Coordinator: etcd-grove-81. Scratch: `/shared/tmp/wal-spec/w4a1/` (revision 1:
`rev1/`).

## State (2026-11-12, revision 1)

- Round 0 (`91e927b08f`, `58817cfeaa`): `walDiskM`, Save/SaveSnapshot/Close over it, VSE's token
  conjunct. The delta review was NOT READY (B1, M1, M2, minors).
- Revision 1 (`73965dc1a8` + the notes commit): `walDiskAt`'s mark and `named` are lower bounds
  (`Specs.lean`: `walDurLe`/`walMapLe`, `absDiskCtx`, `walDirIs`), handle-only `wp_WalSyncLen`/
  `wp_WalNamedLen`, `walDiskM` dropped, Close's first conjunct and VSE logically atomic, VSE's
  token-free conjunct dropped, `WalBodies.lean` (the bodies of every past-state post, proved).
  The axiom files come from `/shared/tmp/wal-spec/w4a1/gen/genspecs.py` (the only source: rerun it
  with the worktree as its argument; round 0's is `genspecs-w4a1-r0.py`).
- Checks: full build passes (`rev1/build.log`); tcb baseline unchanged; api-check clean; interfaces
  checked, absdisk `Specs.txt` regenerated (`rev1/checks.log`); Go tests 20/20 plus the reviewers'
  counterexample (`rev1/gotests.log`).
- Freeze package: `/shared/tmp/wal-spec/w4a1/freeze-w4a1.md`, section "Revision 1". **Waiting for the
  re-review; STOP before `etc/land.sh`** (merge lean first, rerun the checks, then add a STATUS.md entry).
- R1/R2 (purge-model completeness): deferred, proposed as W4a.2 (freeze "Revision 1b": `Open` needs
  `≤ a` and `ReleaseLockTo` needs `< a`; the model's `enti` must lower-bound Go's across restarts).

## Next

After it lands: W4b (`wal-w4b`) merges lean and replaces its `walDiskM` uses with `walDiskAt` (now the
lower-bound view). Then W4a.2 (R1/R2).

## Build command

```
export TMPDIR=/shared/tmp
systemd-run --scope -q -p MemoryMax=64G lake --packages=/shared/tmp/manifest-ddc.json build Proof.go_etcd_io.etcd.server.v3.storage.WalBodies
# full: flock /shared/tmp/etcd-grove-build.lock systemd-run --scope -q -p MemoryMax=64G lake --packages=/shared/tmp/manifest-ddc.json build
```
