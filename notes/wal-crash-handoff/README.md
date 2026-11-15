# WAL and crash-model handoff (2026-11-12)

**Update 2026-11-13 (the user's decision):** one file semantics, `fsExt`, power loss only (no process
kills). `absDiskExt` becomes a ghost layer over `fsExt`, and the WAL's axioms proved specs of the real WAL
(`notes/decisions.md`, "One file semantics, `fsExt`; power loss only"; plan `notes/wal-fsext-plan.md`).
What follows about unifying the crash models and adding process kills is superseded by it.

The user's collaborator takes over etcd's WAL specification with a unified crash model (this
repository's abstract-disk extension `absDiskExt` and the per-byte Linux model in `LinuxFs/`), and with
it the crash ladder (rung 1 `etcd_wal_safe` through rung 5). The etcd-grove-81 sessions continue the
graceful restart track (S5, S6, S7) against the interface below, and defer S2 and C6.

Start here:
- **`restart-wal-interface.md`**: what a restarted etcd server needs from the WAL, independent of the
  crash model. What the restart proofs consume today (F1-F13), the proposed abstract interface (I1-I11)
  mapped to the WAL spec's lemmas, the recorded C6 gates, and what S5-S7 will and will not assume. Its
  findings for the WAL side: `ReadAll` should return `walSaveEnts d.sized`; the restart's durability
  invariant needs a source (S2a); the server's WAL invariant must be stated over histories.
- **`notes/wal-w4c-handoff.md`**, section "Paused": the WAL tester's proof (W4c), half done, with the
  exact next steps; `etcd_wal_safe` not yet stated.
- **`rung3/`**: crash rung 3 (bbolt/mvcc under crashes), not landed (branch `crash-rung3`, worktree
  `/shared/etcd-grove-rung3`): the handoff, the Scope, the trusted bbolt crash spec's Freeze package and
  its review (open blockers; the comparison with LinuxFs: its restart assumption hides the kill-then-power
  bug, so a process-kill crash is needed in `fsExt` before it can replace the bbolt arm).
- **The landed WAL spec**: `GooseLang/Ext/AbsDisk/`, `Proof/go_etcd_io/etcd/server/v3/storage/Wal*.lean`,
  the WAL axioms under `Spec/go_etcd_io/etcd/server/v3/storage/wal/`; its design and reviews in
  `notes/decisions.md`, entries "WAL W4a" through "WAL W4c" (including the review checklist every crash
  axiom should pass, and every "C6 gate").
- **World assumptions** the WAL spec rests on (approved by the user): `GooseLang/Ext/AbsDisk/Impl.lean`'s
  header (bare fsync(2), arbitrary unsynced bytes, synced bytes survive a sector rewrite, no CRC
  collision, Paths); `storage.walCreateOk` as a premise of `etcd_wal_safe`.
- **Fork fixes** in the WAL (pushed): `c90b03b56` Exist, `1aaca041c` ReadAll's ErrSnapshotNotFound,
  `0b50f0426` segment naming; F-Z/F-N1/F-N2 earlier. bbolt: `c5a6065`, `ea4cab5` (pushed), `4f08974e`
  (local, incomplete; see `rung3/`).
- The restart track's Scope: `notes/restart-scope.md` (copied from scratch, 2026-11-12).

## Restart S6 and the snapshot directory (2026-11-13, etcd-grove-81)

Restart S6 (branch `restart-s56`, worktree `/shared/etcd-grove-rs56`, not yet landed) owns new state over
the old file layer (`osFsExt`), which the fsExt decision retires; whoever retargets bbolt and the
snapshotter onto `fsExt` should carry it over:
- **The member's snapshot-directory invariant** (`snapDirInv`, `Proof/.../rafthttp/Net.lean`) is now
  allocated once, at the first start, and reused at a restart through the image; removed snapshots are
  counted by a member-level counter (`snapRmM`). It holds `fileHolds` of the `<i>.snap.db` files.
- **A first-start token** in `bootOk` (approved by the user, 2026-11-13, as a listed world assumption):
  `snap.snapDirOwn (snap.snapDBPathOf cfg.DataDir')` (at the first start the snapshot directory holds no
  `.snap.db`, and nothing outside the server's snapshotters writes `.snap.db` there), and the path
  equation `snap.snapDBPath bs.ss' = snap.snapDBPathOf cfg.DataDir'` in `bootOk` and `bootOkR`
  (`snapDBPathOf` an opaque). Under `fsExt` these become facts about the directory's real files.
- **Fork fix** `2eaeb872b` (`goose-lean-snaplink`, pushed): `SaveDBFrom` links the temp file into place
  and keeps an existing one, so two concurrent saves of one index (which can hold different data while a
  compaction is half done) no longer overwrite each other; `nonissues/etcd-snap-savedbfrom-concurrent-rename.md`.
- The axioms `snap.Snapshotter.SaveDBFrom`, `Release` and `EtcdServer.purgeFile` keep their statements;
  their file-level facts are the natural targets for proved specs over `fsExt`.
Details: `notes/restart-s56-handoff.md` and `notes/decisions.md` "Restart S6a" on that branch (land with S6).
