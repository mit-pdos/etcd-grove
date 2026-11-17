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
* 2026-11-17, **S1a** (branch `bbolt-api-adds`): two additions to bbolt's API (`Spec/go_etcd_io/bbolt/Api.lean`;
  `notes/bbolt-spec-decisions.md`, "API additions for the integration").
  - `boltTx_size (tx γ q D) : boltTx tx γ q (TxView.ro D) ⊢ ⌜∀ (n : GoString) (m : BktData),
    D.lookup n = some m → m.size < 2 ^ 61⌝`, proved from `boltTxDef_size_ro`
    (`Proof/go_etcd_io/bbolt/Inv/TxSize.lean`): the reader's view is well formed, its pages lie in
    the mapping (ids below `2 ^ 36`), a bucket's leaves are distinct pages (`viewUnique`), at most
    `2 ^ 16` elements each, so at most `2 ^ 52` entries. **For read transactions only** (the
    fallback form): a writer's `T.cur` is its nodes' entries, which nothing in the invariant
    counts. The backend needs only the reader case (`rtHeld_sizes`, `ReadLemmas.lean`, through
    `rtxSnap tx D` = `boltTx tx γ q (ro D)` under D-I2), so `backend.rtxSnap_size` becomes this law
    in S1. (SpecPlan's `boltTx_size` is another law, `tx.Size()`'s `txSize`: same name.)
  - `statSlot γ : Option (Loc × TxView) → IProp GF`, `some (tx, T) ↦ boltTx tx γ 1 T` for any view
    (SpecPlan's form). A writer's `statlock` token is the spare pair's, in its exclusive part
    (`txExcl`'s `wr` branch: `wdbLive` holds `sparePair`); `freepages` borrows it only inside
    `Commit`, which consumes `boltTx`. `Txn/StatSlot.statSlot_tok` gains the writer case;
    `DB.Stats.spec` re-proved, statement otherwise unchanged.
  No new axiom or `sorry`; `Link`/`Results` unchanged; interfaces regenerated. No client outside
  bbolt used `statSlot` (the backend still goes through `DB.Stats_kv`).
* 2026-11-17, **S1** (branch `bbolt-s1`, D-I1, D-I2): the backend over the proved bbolt.
  - **D-I1.** `backend.FsCtx GF` (`InvBbolt.lean`) packs `ExtSemantics fsExt`, `FsSemOk`,
    `HasExt fsExt` and, beyond the plan, `os.file.FieldAssumptions`/`os.fileStat.FieldAssumptions`
    (every result of bbolt's `Link.lean` takes them as section variables; Props, so the structure
    is still a subsingleton, `FsCtx.eq`); `theFs GF : Option (FsCtx GF)` (classical; `GF` explicit:
    the field facts are stated in the heap's local context), `onFs f` (`False` at `none`),
    `theFs_eq`/`onFs_eq`/`onFs_some`/`onFs_none`.
  - **D-I2.** `DBNames := bbolt.BoltName`; `ownDB db γ D := onFs (isBolt db γ ∗ boltState γ 1 D)`;
    `wrTok γ := emp`; `isDB db γ`; `txLive tx γ q T := onFs (boltTx tx γ q T)` (in place of
    `txLive tx q ∗ rtxSnap tx D`: a reader is `txLive tx γ q (TxView.ro D)`); `txBytes tx γ s b`;
    `wView D S G`, `ownWTxG tx γ D S G := txLive tx γ 1 (wView D S G)`; `wBkt tx γ b n g := onFs
    boltBkt` (also the reader's handles, at generation 0: `rBkt` is gone); `ownCur tx γ c T es pos`;
    `txDone tx`, `txDB tx γ db`; `curAt tx γ`. Laws from bbolt's (`txLive_fractional`,
    `txLive_later` — `boltTx` is not timeless: the read side's `wgInv` now carries `isDB db γ.db`,
    `wgBody_later` —, `txLive_agree`, `txLive_size` (S1a's `boltTx_size`, readers), `txBytes_acc`,
    `txLive_nonnull`, `ownWTxG_fill` (now with `¬ float64IsNaN`; `unsafePut` writes `0.9`)).
    `rtxStats` and its machinery are gone (`intvInv`'s stats invariant, `stats_take`/`stats_give`,
    `tmTok`'s second token; `BNames.txb` stays, unused, for the clients' layout). `fileHolds`,
    `dbFile` stay axioms.
  - **API addition** (bbolt): `boltBkt_timeless` (`Api.lean`, proved; the backend's buckets cache
    keeps reader handles in an invariant).
  - **The `_kv` specs.** 17 are theorems (`Proof/go_etcd_io/bbolt/*_kv*.lean`, each `wp_proof (h :
    ∀ [fs instances], bbolt.X.spec)`), linked by `etc/gen-link.py --backend` to bbolt's `Link.lean`
    (`@` callees in `etc/link-lean-first-backend.txt`). Restated: `Bucket.Cursor_kvr` (a handle
    `wBkt tx γ b n 0` and `D.lookup n = some m`), `Bucket.Cursor_kvw` (the cursor at `wView D S G`,
    `ownWTxG` back at once), `Cursor.Next_kv` (bbolt's position: stays at the last entry; `unsafeRange`'s
    loop keeps the position only while in range), `Cursor.Seek_kv`, `DB.Info_kv` (a fresh `i ↦ v`,
    not `↦□`), `DB.Stats_kv` (paid by a live transaction held whole, `statSlot (some (tx, T))`),
    `Tx.Bucket_kvr`, `Tx.DeleteBucket_kv` (the empty name's `ErrIncompatibleValue` case),
    `Tx.Rollback_kv`, `Tx.Size_kv`/`Tx.DB_kv` (any view); the rest only gain `γ`. `Open_kv` and
    `DB.Close_kv` stay axioms over the new predicates (S3). **`Bucket.Put_kv` stays an axiom**
    (its pre-S1 statement over the new vocabulary): the proved `Put` takes `kb.length + vb.length ≤
    bboltEntryMax = 2 ^ 28`, and no caller of the backend's `unsafePut` has that bound (mvcc's puts
    bound only the key, `< 2 ^ 63 - 1`; the server's value-length law bounds key and value by
    `etcdKeyMax = 2 ^ 27` each, and a marshalled `KeyValue` of both passes `2 ^ 28` by its framing):
    the bound must be threaded from the request size (`--max-request-bytes`) through apply, txn and
    mvcc's puts (and auth's records), or `bboltEntryMax` raised. Open, for the coordinator.
  - **bbolt's Link**: `PidSetDeleteUnfold` is now the WP of `delete` at `pidSet`, proved
    (`pidSetDelete_holds`, Perennial's `wp_mapDelete_underlying`); `etc/link_bbolt.py` gives each
    pending result only the hypotheses it reaches, so `DB.Begin`, `Tx.Commit`, `Tx.Rollback` are no
    longer pending (only `wp_Open` takes `h_fs_FileMode_String`).
  - Changed backend specs: `backend.begin`, `unsafeBegin`, `newBatchTxBuffered`, `batchTx.commit`
    (the vocabulary), `unsafeRange` (`γd`, the view `T`), the `UnsafeRange`s and `UnsafeDelete`s
    (`kvsOutRd γ.db`, `rdB γ.db`, `txBytes … γ.db`), `batchTx.UnsafeDeleteBucket` and
    `batchTxBuffered.UnsafeDeleteBucket` (new premise `bi.name ≠ []`). Outside the backend: mvcc's
    `BackendBridge` (proofs), `InvStore`'s `dbNames_countable`, `InvApplier` (proofs only); no spec.
  - `examples/axiomcx/bboltnan`'s proof (`Run.lean`) deleted: `boltTx_fill` refuses the NaN.
  - `RaftWitness/…/ProjSimps.lean` re-exports the main tree's (it now reaches it through
    `Proof.runtime.Start` → `InvBbolt` → bbolt's `Data`).
