# Plan: etcd's proofs over the verified bbolt (2026-11-17)

**Goal (the user's, 2026-11-17):** no `bbolt.*_kv` axiom left; every etcd proof uses the proved bbolt
(`Proof/go_etcd_io/bbolt/`, linked by `etc/gen-link.py --bbolt`); bbolt's axioms gone from the trust
base of the top-level etcd theorems. A top-level theorem may gain a premise that file I/O does not
fail, where one is needed; every such change is reported to the user.

Supersedes the backend table of `notes/bbolt-spec-decisions.md` ("The backend: each `_kv` axiom
against the new specs"), written before begin-tok and the port onto `fsExt`.

## Where it starts (`origin/lean` `d09e1d0ab5`)

* The proved bbolt: its API (`Spec/go_etcd_io/bbolt/Api.lean`, sealed `isBolt`, `boltState`, `boltTx`,
  `txDB`, `txDone`, `boltBkt`, `boltCur`, `txBytes`, `fileHolds`) and one spec per function, over
  `fsExt` (`∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]` at each triple). Its collection
  (`etc/tcb-collections/bbolt.txt`): `optsAt_*_rd` and stdlib axioms, two `sorry`s (the axiomatized
  `Options` type's generated instances).
* The backend (`Proof/go_etcd_io/etcd/server/v3/storage/backend/`) uses only the 20 `_kv` specs
  (`Spec/go_etcd_io/bbolt/*_kv*.lean`, axioms in `Proof/go_etcd_io/bbolt/*_kv*.lean`) over its own
  axiomatized predicates (`InvBbolt.lean`: `ownDB`, `wrTok`, `isDB`, `txLive`, `txBytes`, `rtxSnap`,
  `rtxStats`, `rBkt`, `ownWTxG`, `wBkt`, `ownCur`, `txDone`, `txDB`, `fileHolds`, `dbFile`, laws), and
  its own axioms of bbolt's options (`BboltOptions.lean`, `BboltOptsDefs.lean`).
* `putget3`'s trust base: 18 `bbolt.*_kv` axioms, 41 `backend.*` (most of them the above), and the
  snapshot path's `backend.backend.Snapshot`, `snapshot.WriteTo/Size/Close`.
* The server's file world is abstract (`dataDirFresh`, `walFiles`, `fileHolds`, `pathOwn`, `os.Rename`'s
  axiom, `SaveDBFrom`, `goose_adequacy_start_files`); its first start is the premise
  `bootstrapContract`; `storage.OpenBackend` is a names-only axiom. The closed theorems run over
  `etcdFsExts` (`[idIssueExt, fsExt]`, `fs_semantics`) with `Hfs : FsInit`, and drop the tree.

## Design

**D-I1. The file extension's instances, packed.** `backend.FsCtx` bundles `ExtSemantics fsExt`,
`FsSemOk`, `HasExt fsExt` (with the global `fs_interp`). `HasExt.sem_eq` pins the semantics to the
program's, so `FsCtx` is a subsingleton in any context; `theFs : Option FsCtx` (a classical choice)
names the one value, and every backend predicate over bbolt's API is defined at it (`none`: `False`).
A derivation with the instances in scope rewrites `theFs = some ⟨_, _, _⟩`. So the backend, mvcc,
the server and the examples take no new binders: only the specs that touch files (S3) take the
instances.

**D-I2. The backend's vocabulary over bbolt's** (the old table's layer, adjusted):
`DBNames := bbolt.BoltName`; `ownDB db γ D := isBolt db γ ∗ boltState γ 1 D`; `wrTok γ := emp`;
`isDB db γ := isBolt db γ` (takes `γ`); the read transaction `txLive tx q ∗ rtxSnap tx D` becomes
`boltTx tx γ q (ro D)`; `ownWTxG tx γ D S G := boltTx tx γ 1 {rw, base := D, cur := S, gen := G}`;
`wBkt := boltBkt`; `ownCur` gains the view; `rtxStats` and its token machinery go; `txBytes`, `curAt`
take `γ`. The `_kv` files stay as corollaries (theorems over the proved specs, linked to bbolt's
`Link`), restated only where the proved spec differs (Put's entry bound `bboltEntryMax`, Stats's
`statSlot`, the cursor's view).

**D-I3. `rtxSnap_size`** becomes a law of bbolt's API (`boltTx_size`), proved from the file's size
bound (`fileHolds`: size below `2^62`, distinct page extents, 16-byte leaf headers).

**D-I4. Options.** bbolt's `Options` is translated (no longer axiomatized): `optsAt` a definition,
the `_rd` axioms lemmas, the two `sorry`s gone; the backend's option axioms lemmas over it.

**D-I5. Files.** bbolt's `Open` restated over the shared mode of the tree (a claim on the file's
name, `os.OpenFile.specCreateS`), `Close` giving the file back (`fileHolds i D`) to an owner of
`boltState γ 1 D` (`notes/bbolt-spec-decisions.md`, D9's alternative). The errors: in the model
`open`, `fstat`, `pread`, `pwrite`, `fdatasync`, `close` fail only as `NoIoErr` allows, but
`flock`, `mmap` and `munmap` may fail with any errno; the backend panics on `Open`'s and
`applySnapshot` on `Close`'s error. So the closed theorems that need it take a premise on steps
(no I/O error, `mmap`/`munmap`/`flock` included, on the database files), replacing `dbOpenOk`,
`dbCloseOk` and the `_kv` axioms that tied errors to them. Reported to the user.

**D-I6. Snapshot.** bbolt's `Tx.WriteTo` proved, `boltImage` concrete; `backend.Snapshot`,
`snapshot.WriteTo/Size/Close` proved.

## Stages (tasks)

* **S1** (D-I1, D-I2): the in-memory layer. Removes 16 `bbolt.*_kv` axioms and the backend's
  predicate axioms but `fileHolds`, `dbFile`; `Open_kv`, `Close_kv` stay axioms over the defined
  predicates until S3 (as sound as today's abstract file world: no proof holds `fsExt` resources
  that `isBolt`'s invariants could conflict with).
* **S1a** (D-I3).
* **S2** (D-I4).
* **S3** (D-I5).
* **S4** (D-I6).

## Log

* 2026-11-17: plan written (session bbolt-integrate).
* 2026-11-17: **S3a** (D-I5, bbolt's side; session `bbolt-files`, branch `bbolt-files` off
  `bbolt-integrate`). Done: items 1, 2 (`Close.specNoErr`; not `Close.specOwn`), 3 (`Open.specS`;
  not `Open.specSNoErr`), 4. No new `axiom` or `sorry`, no closed theorem's statement changed.
  - **The premise** (`GooseLang/Ext/Fs/Premises.lean`, trusted, **pending the user's review**;
    `examples/osfs/semantics/premise_no_map_lock_err.go`, indexed in `doc.go`): a separate
    definition beside the approved `NoIoErr` (which stays as approved):
    `NoMapLockErr (S : IoSet) : StepPrem := fun o v st e' _ => MapLockCovers S o v st →
    (∃ e'' st'', IsFsStep o v st e'' st'' ∧ MapLockOk o v e'') → MapLockOk o v e'`, where
    `MapLockCovers` names `flock` and `mmap` on an fd of a covered inode and `munmap` of a mapping of
    one, and `MapLockOk` is errno 0, or `EAGAIN` for a non-blocking lock request
    (`flockReq how = some (some ex, true)`, the conflict bbolt's `flock` retries on), or `ENOMEM` for
    `mmap`. `noMapLockErr_keeps : StepKeeps (NoMapLockErr S)` (`NoMapLockErr.lean`, untrusted);
    `StepPrem.and`, `noIoErr_noMapLockErr_keeps` (the two together keep steps: they name disjoint
    operations), `fsStepSat_and_left/right`: a closed theorem runs over
    `fsSemWithS (StepPrem.and (NoIoErr S) (NoMapLockErr S)) Q`. Error-free specs of the steps
    (`NoMapLockErrSpecs.lean`: `wp_osMunmapNE`, `wp_osFlockNE`, `wp_osCloseNE`, `mmap_noErr`).
    **`mmap`'s `ENOMEM` is not excluded**: the mappings share `(0, maxAddr]` with the Go heap, and a
    premise on steps does not see the heap, so excluding it would leave no step from a state whose
    heap leaves no room (`StepKeeps` fails). For the user: `Open` (its `mmap`) and every remap
    (`Commit`'s `allocate`) may still fail with `ENOMEM` under the premise; excluding it needs a
    premise that sees the heap (a `StepPrem` with the heap: a change to the trusted `fsSemWithS`) or
    a named premise on the closed theorems.
  - **`DB.Close_noErr.spec`** (`Spec/go_etcd_io/bbolt/DB__Close_noErr.lean`; the task's
    `DB.Close.specNoErr`, named by the package's layout rule, as `DB.Begin_err`):
    `∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] (Sio : IoSet) [FsStepSat (NoIoErr Sio)]
    [FsStepSat (NoMapLockErr Sio)], (∀ st i, Sio.ino st i) → ∀ db γ,
    {{ isBolt db γ }} db.Close() {{ err, RET #err; ⌜err = nil⌝ }}`. Proof: `DB.Close`'s proof made
    generic in its `close`'s error (`DB.Close.wp_proofQ`, private in `DB__Close.lean`), over
    `DB.close.spec_ownedNoErr` (`Open/CloseNoErr.lean`: `DB.munmap.specNoErr`,
    `syscall.Flock.specNoErr`, `os.File.Close.specNoErr`, `unix.Munmap.specNoErr`, each proved).
  - **`Open_shared.spec`** (`Spec/go_etcd_io/bbolt/Open_shared.lean`; the task's `Open.specS`):
    `Open.spec` with `osSharedInv R ∗ osPathS R d dq j ∗ osCallPerm qc ∗
    osNames j (.only [b]) (DFrac.own 1) h ∗ nameHolds h b D` (`ApiS.lean`: `(∃ i, ⌜h.cur !! b =
    some (.file i)⌝ ∗ fileHolds i D) ∨ ⌜h.cur !! b = none ∧ D = ∅⌝`) in place of
    `osTree ∗ pathHolds`, `NameOk b`, the path `child d b`; post: `optsAt ∗ osPathS ∗ osCallPerm ∗
    ∃ oc, crOut j b h (DFrac.own 1) oc ∗ ((⌜err = nil⌝ ∗ ∃ γ i, ⌜γ.ns = N ∧ crIno b h oc i⌝ ∗
    isBolt db γ ∗ boltState γ 1 D) ∨ ⌜err ≠ nil⌝)`. Proof: `Open`'s proof made generic in the open
    of the file (`Open.wp_proofG` over `openFileDb.spec`, private in `Open.lean`; the tree's
    instance gives `Open.spec` unchanged), with `os.OpenFile.specCreateS` (the claim's halves, the
    trivial update `os.osAU_triv`; `Proof/os/WriteFile.lean`'s `osAU_triv` and `crOut_join` lose
    their unused `os` assumptions). The option reads were not touched (S2).
  - **Left** (why, and the design): `DB.Close.specOwn` (the file back as `fileHolds i D`) and
    `Open.specSNoErr`. See `notes/bbolt-spec-decisions.md`, "S3a".
