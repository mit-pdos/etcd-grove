# lease-mono3 step 2: handoff

Branch `lease-mono3-s2` (off `lean` `89ef103d5b`), worktree `/shared/etcd-grove-auth3`.

- Done: the Scope, `notes/lease-mono3-plan.md`, "Step 2 Scope" (hard stop 1, at etcd-grove-81).
- Next, in order (after the Scope's approval): the Go tests (S2.2's "Go test"); the server core
  (`InvRequest.lean`, `NewServerAlloc.lean`, `ApplyCmpArm.lean`, `Restart.lean`); `leaseIdsApart`;
  `Alloc3.lean`/`Alloc.lean`; `StartCluster` spec and proof; callers; interfaces; Freeze package
  (hard stop 2); land via `etc/land.sh` only after 81's go (hard stop 3).
- Build: `flock /shared/tmp/etcd-grove-build.lock systemd-run --scope -q -p MemoryMax=64G lake build
  --packages=/shared/tmp/manifest-ddc.json`; Go tests under `systemd-run --scope -q -p MemoryMax=32G`,
  `GOWORK=off`.
- Pitfalls: `KVNames` positional literals (`NewServerAlloc.lean:371,379`, `Restart.lean:200`) need the
  new field; `kvInv_congr` needs `propext` for the `kvPfxOk` iff.
