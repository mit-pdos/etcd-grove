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

### S2 (D-I4, branch `bbolt-options`, 2026-11-17)

* **Translation.** `bbolt.toml` translates `Options` and `DefaultOptions` (`translate = ["*",
  "!splitThreshold"]`; `splitThreshold` stays trusted). `os.FileMode`, the old gap, is this
  repository's `os` since 2026-11-03, so the struct translates as is. No other project's
  translation changes. `etc/gen-init.py`: `DefaultOptions` is a translated initializer (an
  allocation of a literal), so `go_etcd_io.bbolt.opaqueInitsOk` (`Proof/go_etcd_io/bbolt/Init.lean`)
  is gone.
* **bbolt's vocabulary** (`Spec/go_etcd_io/bbolt/Options.lean`): `optsVal v o` (the six tracked
  fields of the struct) and `optsAt l dq o := ∃ v, l ↦{dq} v ∗ ⌜optsVal v o⌝` are definitions,
  `optsAt_discard_persistent` an instance. `Proof/go_etcd_io/bbolt/Options.lean`: every law a lemma,
  statements unchanged (`optsAt_nonnull`, the twelve `optsAt_*_rd`, `optsAt_bool`/`_int`/`_mlock`/
  `_mmapFlags`/`_freelist`/`_timeout`/`_logger`, `wp_optsLit`/`Alloc`/`Load`/`Store`), plus
  `optsPt_eq` (the points-to field by field), `optsAt_acc`, `optsVal_zero`, `optsAt_zero`.
* **The backend's** (`BboltOptsDefs.lean`, `BboltOptions.lean`): `optsAt l dq o := ∃ m f,
  bbolt.optsAt l dq (o.toBolt m f)` (the backend's `OptsM` has no `Mlock`/`MmapFlags`: `newBackend`
  stores `cfg.Mlock`, which the backend's `OptsM.ok` does not restrict), `optsVal` likewise; its
  laws (`optsAt_discard_persistent`, `wp_opts*`, `optsAt_bool`/`_int`/`_freelist`/`_timeout`/`_logger`)
  are corollaries of bbolt's, statements unchanged; new `optsAt_zero`. `boltLogger` (and its
  persistence) stays an axiom, with `backend.newBoltLoggerZap.wp_proof`: bbolt's `boltLogger`
  (`Spec/go_etcd_io/bbolt/Logger.lean`) takes the file extension's instances, which the backend's
  statements do not carry until S1's `theFs`; zap is names-only, so `newBoltLoggerZap` stays a
  trust-boundary axiom either way. `boltOpenOptions_init` (the backend's `Init.lean`, names-only:
  `syscall.MAP_POPULATE`) stays an axiom, now over the defined `optsAt`.
* **`Options.String`** stays an axiom (`Proof/go_etcd_io/bbolt/Options__String.lean`): its
  `fmt.Sprintf` has `%p` of a func and of an interface, which no `Sprintf` spec admits
  (`notes/perennial-changes.md`, 2026-11-17).
* **Fallout.** `wp_auto` now runs `&bolt.Options{}` (literal and allocation) itself: `newBackend`
  and `bboltnan.Run` take the allocated zero value through `optsAt_zero` (the `wp_optsLit`/
  `wp_optsAlloc` steps and `newBackend`'s local `TypeRepr` instances, a workaround for the `sorry`
  instances, are gone). `Spec/go_etcd_io/bbolt/Open_kv.lean`: `bbolt.Open_kv.spec` is declared in
  namespace `bbolt`, so once bbolt's `Options` module is imported its `OptsM`/`optsAt` resolved to
  bbolt's; they are now written `backend.OptsM`, `backend.optsAt`, `backend.boltLogger` (the same
  constants as before: no change to the statement).
* **Trust base** (`etc/tcb-baseline.txt`, 24 axioms and 2 `sorry`s fewer; 41 collections updated,
  bbolt's, backend's, putget3's and mvccfull's among them, removals only): the axioms
  `bbolt.optsAt_*_rd` (11), `bbolt.optsAt_nonnull`, `backend.optsAt`, `backend.optsVal`,
  `backend.optsAt_discard_persistent`, `backend.wp_optsLit`/`Alloc`/`Load`/`Store`,
  `backend.optsAt_bool`/`_int`/`_freelist`/`_timeout`/`_logger`, `go_etcd_io.bbolt.opaqueInitsOk`;
  the `sorry`s `Options_typed_pointsto`, `Options_into_val_typed`. Also gone from the source (no
  result reached them): bbolt's copies `bbolt.optsVal`, `bbolt.wp_opts*`, `bbolt.optsAt_bool`/
  `_int`/`_mlock`/`_mmapFlags`/`_freelist`/`_timeout`/`_logger`, `bbolt.optsAt_discard_persistent`,
  and the translation's `Options`, `Options.zero_val`, `Options.underlying`, `DefaultOptions.init`.
  Left: `bbolt.Options.String.wp_proof`, `backend.boltLogger` (+ persistence),
  `backend.newBoltLoggerZap.wp_proof`, `boltOpenOptions_init` (above). No statement of a closed
  theorem changed; no axiom or `sorry` added.
* **Gates.** All pass but `k8s client error types` (`examples/k8s/etcd3`'s Go test: `startCluster
  failed`, an environment failure of the shared machine; this change touches no Go code).
