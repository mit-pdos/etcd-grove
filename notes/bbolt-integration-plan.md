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
* 2026-11-17, **S4a** (branch `bbolt-writeto`, D-I6 bbolt side): **partly done; the proof of
  `Tx.WriteTo` is blocked by the invariant**, findings for the coordinator below.
  - Done: `boltImage (bs : List w8) (D : Data) : Prop` in bbolt's API (`Spec/go_etcd_io/bbolt/Api.lean`,
    sealed `@[no_expose]`, pure): `bs.length < 2 ^ 62 ∧ fileOK bs bs.length D` (`fileHoldsDef`'s pure part
    with the size the bytes' length). Its law `fileHolds_of_image (i m xs D) (hmaps : m.maps = ∅)
    (hsize : m.size = xs.length) (himg : boltImage (xs.map Prod.fst) D) : osMeta i (own 1) m ∗
    osBytes i 0 (own 1) xs ⊢ fileHolds i D` (the receiver's side: a file of exactly those bytes, no
    mapping). The backend's opaque `backend.boltImage` can become this definition in S4b. No new axiom
    or `sorry`.
  - Not done: `Tx.WriteTo.spec`/proof. The intended statement (not committed, since it cannot be
    proved without the changes below): for `boltTx tx γ q (TxView.ro D)`, the writer's contract
    `writerOk w Wr` (copied from the backend) and `Wr c bs₀`, `tx.WriteTo(w)` returns `(n, err)` with
    `boltTx tx γ q (ro D)` back, `Wr c' (bs₀ ++ bs)`, and `err = nil → boltImage bs D ∧ n = len bs`.
  - **Why the proof is blocked** (what a read transaction holds today, `Inv/Tx.lean`'s `rtxFrac`, and
    where the file's resources are):
    1. **The file handle.** `tx.db.file`, the `*os.File`'s `fileOwn` and the descriptor's `osFd` are
       all held whole in `rwlock`'s resource (`wdbCoreG`), i.e. by a live writer; a reader holds no
       share, so it can neither load `db.file` nor call `ReadAt`. Fix: a share of the three in
       `mmaplock`'s resource `Pm` (readers then hold `rfrac` of it; `close` holds all three locks and
       gets them whole), the writer keeping the rest; touches `Pm`'s users (Open, remap, close, begin,
       rollback) and `rtxFrac`.
    2. **The synced freelist page.** `fileOK` requires a valid freelist page when the meta names one
       (`flFileOK`; `init` always writes one, and `Open` reads it whatever `NoFreelistSync`). The current
       synced freelist page is a `W` slot (`wdbOK`: `W` is the complement of tree and pending slots),
       its page-cache bytes the writer's (`wBytes`); the reader's view and meta copy say nothing of it.
       So the image's freelist page is unprovable. Fix: the current synced freelist extent a store
       slot (in `slotsOf`), which reworks Commit's freelist part (`fbCond`/`fbInv`, `flCurOK` over `wb`),
       or restrict the spec to metas without a synced freelist (no client can state that today).
    3. **The page-cache bytes of the view's slots** are in `pagesInv` (`osSlot … (own 1)`), an
       invariant: readable only through an accessor opened around each `pread`. Needs a variant of
       `os.File.ReadAt.specRacy` taking an invariant accessor in place of held `osBytes` (provable over
       the trusted `os` model, `Proof/os/File__ReadAt.lean`), and a lemma that a registered reader's
       slots are store slots whose `σ.bytes` are its view's pages (via `viewCells` agreeing with
       `storeCells`). (Reading through the mapped cells instead needs a mapping witness, `osMeta`,
       which the writer holds whole.)
    4. **The reader's meta copy.** `rtxFrac` records only `mv.txid' = v.txid` and the `pgid` bound;
       the image's metas need `mv = metaOf (C.slot C.txid)` for a `C` with `C.metaOk`, `treeOK C`,
       `1 ≤ C.txid < 2 ^ 62`, `View.ofC v.base C = v` (`rdTxK_intro` has all of it; `viewWF` keeps
       only `∃ C, treeOK C`).
    5. **`WriteFlag`.** `rtxFrac` holds `tx.WriteFlag ↦{q} t.WriteFlag'` with no fact; `Begin` leaves it
       0 (`rdTxK_intro`'s `∃ wf`). Fix: the points-to at `W64 0` in `rtxFrac`, proved at begin.
    6. **Stdlib.** `io.NewSectionReader`, `io.CopyN` (and `Copy`, `LimitReader`, `SectionReader.Read`)
       are names-only in Perennial: trust-boundary specs needed, generic over a `ReadAt` contract.
       `CopyN` goes through `io.Copy`, which calls `dst.ReadFrom` when `w`'s type has one (an
       `*os.File` does; etcd's `*io.PipeWriter` does not), so the spec needs a premise that `w`'s
       dynamic type has no `ReadFrom` method, or a contract for it; `writerOk` says nothing of
       `ReadFrom`. bbolt's own callees (`Meta.DecTxid`, `SetChecksum`, `Sum64`, `Page.SetFlags`/`SetId`/
       `Meta`, `fmt.Errorf`) have specs.
  - So D-I6 needs a decision: the invariant work of items 1-4 (a large change to `Store`/`Locks` and
    Commit's freelist proof), or the snapshot path kept as trust-boundary specs over the now-concrete
    `boltImage`.
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
* 2026-11-17, **bbolt-inv** (branch `bbolt-inv`, off `bbolt-integrate` with S2 merged): the invariant
  redesign for (A) `DB.Close` giving the file back, done; (B) `Tx.WriteTo`, not done (what is left
  below). Decisions: `notes/bbolt-spec-decisions.md`, "bbolt-inv" (D-V1..D-V7).
  - **Found: the txid bound cannot survive a close.** `fileHolds`' `txid < 2 ^ 62` with `Open`'s
    receipts (`t0 < 2 ^ 62`, a session's commits below `receiptBound GF ≤ 2 ^ 62`) makes any
    hand-back unprovable (open at `2 ^ 62 - 1`, commit, close). Fixed by persistent time receipts
    (D-V1): `metaR` holds `⧖ C.txid`, raised by the meta write; `fileHolds` holds `fileRcpt` of its
    bytes; **API change**: `fileHolds_of_image` takes `boltImageRcpt (xs.map Prod.fst)` (new,
    sealed, persistent), which `Tx.WriteTo` will give.
  - **A file given back is whole pages** (D-V2): `fileHolds`/`boltImage` ask `size % 4096 = 0`;
    `wdbOK`'s size clause `size < 2 ^ 62`; `DB.grow`'s premise `sz + AllocSize < 2 ^ 62`; a file left
    with a partial last page (a failed chunked write) is given up at `Close` (`boltNoFile`).
  - **API additions**: `boltIno γ i` (persistent; both `Open` posts now `isBolt db γ ∗ boltIno γ i ∗
    boltState γ 1 D`), `boltNoFile γ` (persistent: the file given up by `DB.Close` or a leaked
    mapping), `boltImageRcpt`, and `FsNoErr` (`GooseLang/Ext/Fs/FsNoErr.lean`, a definition:
    `NoIoErr` and `NoMapLockErr` hold for an `IoSet` covering every file).
  - **`DB.Close_own.spec`** (`Spec/go_etcd_io/bbolt/DB__Close_own.lean`): `{isBolt db γ ∗ boltIno γ i
    ∗ boltState γ 1 D} db.Close() {err. (⌜err = nil⌝ ∗ fileHolds i D) ∨ (boltState γ 1 D ∗ (⌜¬ FsNoErr⌝
    ∨ (⌜err = nil⌝ ∗ boltNoFile γ)))}`. **`DB.Close_ownNoErr.spec`** (`DB.Close_noErr.spec`'s
    premises): `{same} … {err. ⌜err = nil⌝ ∗ (fileHolds i D ∨ (boltState γ 1 D ∗ boltNoFile γ))}`. The
    no-error variant keeps `boltNoFile` for: the database closed earlier by `DB.Close` (which keeps
    the file), a file left with a partial last page (impossible under the premises, not used there),
    and **a mapping leaked by a failed `madvise`**, which bbolt's `mmap`
    does not unmap and which no premise on `fsExt`'s steps excludes (`unix.Madvise`'s model returns
    any errno; for the user: modelling `madvise` as an `fsExt` operation would close it).
  - Invariant: `pagesInv`'s slot bytes in `slotsOs` (closed alternative, `cls` ¼ there, ¼ `metaR`);
    `store_close`; `wdbCoreG`'s junk clause holds the new name `nf`; `closedR` records `nf` or the
    validity token `bq`; `t0At` records the inode. Proof: `Proof/go_etcd_io/bbolt/DB__Close_own.lean`
    over `Open/CloseFile.lean` (the bytes gathered, `DB.close.spec_ownedNoErrM`) and
    `Inv/CloseImage.lean` (pure: `closeBytes_fileOK`).
  - Every existing public spec keeps its statement but the `Open` posts (`boltIno`, allowed) and
    `fileHolds_of_image` (premise, no client). No new `axiom` or `sorry`.
  - **(B) left**: S4a's blockers 1-3, 5, 6 (the file handle's share for readers, the synced freelist
    page a store slot, `pread` of store slots inside `pagesInv`, `WriteFlag`, `io.CopyN` specs);
    blocker 4's txid bound is D-V1 (`Begin` can copy `metaR`'s `⧖` into the reader's part).
* 2026-11-17: **S3b, `mmap` out of address space** (session `bbolt-oom`, branch `bbolt-oom` off
  `bbolt-integrate`): `mmap`'s `ENOMEM` no longer survives the premises; the error-free specs of
  the calls `Open` makes on its file, but `ReadAt`/`WriteAt`/`OpenFile`'s. No new `axiom` or
  `sorry`, no closed theorem's statement changed. `notes/decisions.md`, "fsExt: `mmap` out of
  address space does not return".
  - **The semantics** (`Impl.lean`, trusted, **pending the user's review**;
    `examples/osfs/semantics/map_mmap_no_room.go`): `FsStep := FsStepV ∨ MmapStall`, where
    `MmapStall "Mmap" v h st e' h' st'` is `IsFsStep` accepting the arguments, `¬ MmapRoom st h len`
    (no page-aligned base in `(0, maxAddr]`, no mapping's, with `len` free cells of `h` ending by
    `maxAddr`), and the step to itself (`e' = ExternalOp fsExt.name "Mmap" (Val v)`, `h' = h`,
    `st' = st`), as Perennial's `AllocOOMS`. `IsFsStep`'s `mmap` unchanged (any nonzero errno,
    `ENOMEM` included).
  - **The premise** (`Premises.lean`, pending review): `MapLockOk "Mmap" v e' := (∃ r, e' = osRes r 0)
    ∨ e' = ExternalOp fsExt.name "Mmap" (Val v)`: under `NoMapLockErr`, a covered `mmap` returns a
    mapping or does not return. `noMapLockErr_keeps` re-proved (`heapRendered_map`).
  - **The proofs' side**: `mmap` is not atomic any more (`fsOp_atomic` needs `[FsRetOp o]`); the
    lifting lemmas take `hM : o ≠ "Mmap"` (by `decide`) and hand `FsStepV` on (`fsStepV_of_ne`);
    `wp_os_stepXF` lifts any step with the step's masks; `wp_osMmapG` (`Specs.lean`) is `mmap`
    through an accessor of the `OsMeta`, the stall by Löb induction; `wp_osMmap` and
    `wp_osMmap_cs` keep their statements (the latter over `wp_osMmapG`, no longer `wp_atomic`).
  - **Error-free specs** (each beside the spec it refines; under `[FsStepSat (NoIoErr Sio)]` or
    `[FsStepSat (NoMapLockErr Sio)]`, `∀ st i, Sio.ino st i`): extension level `wp_osMmapNE`,
    `mmap_noFail` (`NoMapLockErrSpecs.lean`), `wp_osFstatNE`, `wp_osPReadNE`, `wp_osFsyncBNE`
    (`NoErrSpecsOpen.lean`); Go level `golang_org.x.sys.unix.Mmap.specNoErr`,
    `syscall.Fdatasync.specBNoErr`, `os.File.Stat.specNoErr`, `os.File.Sync.specBNoErr` (spec and
    proof files `…NoErr.lean`); with S3a's `syscall.Flock.specNoErr` (non-blocking and `LOCK_UN`,
    `EAGAIN` kept on a conflict), `unix.Munmap.specNoErr`, `os.File.Close.specNoErr`.
  - **Left.** `os.File.ReadAt.specRacyLt`, `os.File.WriteAt.specExt` and `os.OpenFile.specCreateS`
    without errors: the extension-level steps are there (`wp_osPReadNE`, NoIoErrSpecs'
    `wp_osPWriteFinishKNE`; `open`'s success needs the path resolved and a free fd, `NoIoErr`'s
    `ErrnoZero` premise), but the Go models' loops (250, 200 and 250 lines of proof) need re-proving
    over them, or their proofs made generic in the steps' errors as `DB.Close`'s was. A blocking
    `flock` cannot be error-free: the semantics has no success while another description holds a
    conflicting lock (`LockStep`: it waits, or fails), so `NoMapLockErr` keeps its failures; bbolt's
    `flock` is non-blocking (`LOCK_NB`), so `Open` does not need it.
* 2026-11-17: **S3c, the error-free `ReadAt`/`WriteAt`** (session `bbolt-noerr-os`, branch `bbolt-noerr-os` off
  `bbolt-integrate`): items 1 and 2 done; 3 and 4 (`OpenFile`) **blocked by `EMFILE`**, below. No new
  `axiom` or `sorry`, no existing statement changed, bbolt's proofs untouched.
  - **Generic proofs** (each public, in the spec's proof file): the Go models' loops made generic in
    their steps' errnos, the existing proof an instance (`Pe := True`), the error-free one another
    (`Pe e := e = 0`). `os.File.ReadAt.wp_proofRacyLtQ Pe hpost` (`File__ReadAt.lean`): `hpost`
    strengthens `pread`'s weakest precondition with `Pe` of its errno (the form `wp_ext_post` gives);
    the post's `*PathError` arm carries `∃ e, Pe e ∧ e ≠ 0`. `os.File.WriteAt.wp_proofQ B Pe hpost`
    (`File__WriteAt.lean`) and `wp_proofExtQ` (`File__WriteAtExt.lean`): `hpost` strengthens `pwrite`'s
    end, from its token (`pwTok`/`pwTokG`) at an offset below `B`, for a write ending by `B` (the
    form `wp_ext_postS` gives); the failure arm carries `∃ e, Pe e ∧ e ≠ 0`.
  - **Extension level** (`NoErrSpecsOpen.lean`): `pwTokG_inflight` (`pwTok_inflight` for a write
    anywhere) and `wp_pwFinish_postNE` (`pwrite`'s end below `maxBytes` returns errno 0 under `NoIoErr`,
    every inode covered, from any resource naming the write in flight: `pwFinish_noErr`, `wp_ext_postS`).
  - **The specs** (under `[FsStepSat (NoIoErr Sio)]`, `∀ st i, Sio.ino st i`; `NoMapLockErr` is not
    needed):
    `os.File.ReadAt.specRacyLtNoErr` (`Spec/os/File__ReadAtNoErr.lean`): `specRacyLt` without the
    `*PathError` arm: `nil` with all of `b`, or `io.EOF` with `n < len(b)` and every held byte of
    `[off, off + len(b))` read (the model's `io.EOF`: a `pread` that read nothing).
    `os.File.WriteAt.specNoErr` and `specExtNoErr` (`Spec/os/File__WriteAtNoErr.lean`): `spec`/`specExt`
    for a write ending by `maxBytes` (premise `off + len(b) ≤ maxBytes` in place of `< 2 ^ 63`: at
    `maxBytes` `pwrite` fails with `EFBIG` whatever the premise), returning `(len(b), nil)`: the
    `OsMeta` `pwPost m off n n` (resp. `os.pwPostE m off n n n`, which is `pwPost m off n n` by `rfl`),
    the bytes `os.PwOut … n` (resp. values `pwValsG … n`). A short `pwrite` (errno 0) is still followed
    by another attempt. Proofs `Proof/os/File__ReadAtNoErr.lean`, `File__WriteAtNoErr.lean`.
  - **`OpenFile` (items 3, 4): not done, needs a decision.** The model's `open` succeeds only with a
    free fd (`FdFree st fd`: nonnegative, unused by `fds`, `dfds`, `ofds`), and the fd maps are finite
    maps that may hold all `2 ^ 63` nonnegative fds: from such a state `open` has no success, so
    `NoIoErr` keeps every errno there (its doc: "`EMFILE` with no free fd"), and no spec can state
    "no error" without knowing the state has a free fd, which no resource of the logic says (fds are
    not counted). Either a premise (a bound on open fds, the closed theorems' or a `StepPrem`), or a
    semantics change as S3b's for `mmap`: `open` with no free fd does not return (a stall, like
    `MmapStall`, Go's out of file descriptors outside the model). Both trusted, so not made here. With
    either, the rest is mechanical, and was drafted (not committed): `wp_fs_stepM` handing the
    semantics' step on (`wp_fs_stepMX`), `wp_logStepSWG`/`wp_logStepSW` with a fact `SQ` of that step
    in `hpost` (`wp_logStepSWGQ`/`wp_logStepSWQ`), `wp_osOpenCreateS'` with the errno's `Pe` (from
    `hpe`, the success built from `OpenEffect` and a free fd), then a Go-level `specCreateSNoErr` with
    no loop (the first attempt succeeds); `ENOENT`/`EEXIST` are not possible outcomes there already.
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
  - **Trust base.** `etc/tcb-baseline.txt` and the collections updated. `putget3.txt`: removed 46 —
    `backend.{isDB, isDB_persistent, ownCur, ownDB, ownWTxG, ownWTxG_fill, ownWTxG_live, rBkt,
    rBkt_persistent, rBkt_timeless, rtxSnap, rtxSnap_persistent, rtxSnap_size, rtxStats,
    rtxStats_excl, rtxStats_timeless, txBytes, txBytes_acc, txBytes_persistent, txDB,
    txDB_persistent, txDone, txDone_persistent, txLive, txLive_fractional, txLive_nonnull,
    txLive_timeless, wBkt, wBkt_persistent, wrTok}` and `bbolt.{Bucket.Cursor_kvr, Bucket.Cursor_kvw,
    Bucket.Delete_kv, Cursor.Next_kv, Cursor.Seek_kv, DB.Begin_kv, DB.Info_kv, DB.Stats_kv,
    Tx.Bucket_kvr, Tx.Bucket_kvw, Tx.Commit_kv, Tx.CreateBucketIfNotExists_kv, Tx.DB_kv,
    Tx.Rollback_kv, Tx.Size_kv, Tx.Stats_kv}.wp_proof`; added bbolt's own trust boundary,
    `os.Getenv`, `reflect.DeepEqual.wp_proof_pgidSet`, `sort.SliceIsSorted`, `sort.Sort.wp_anyLess`,
    `strings.ToLower`. `backend.txt`: the same 46 less `rtxSnap_size` plus `Tx.DeleteBucket_kv`, and
    `fmt.Errorf` added too. Remaining of the old boundary: `bbolt.{Open_kv, DB.Close_kv,
    Bucket.Put_kv}.wp_proof`, `backend.{fileHolds, dbFile, dbFile_persistent, dbFile_timeless}`, the
    options' axioms (S2).
* 2026-11-17, **S1b** (branch `bbolt-putbound`): **`bbolt.Bucket.Put_kv` a theorem**, the backend's last
  in-memory bbolt axiom. The proved `Bucket.Put` takes `kb.length + vb.length ≤ bboltEntryMax` (`2 ^ 28`); the
  bound is threaded from where it is known (the request check, the hooks' conf state, the tester's
  generators), with no closed theorem gaining a premise. Changed statements:
  - **bbolt/backend.** `bbolt.Bucket.Put_kv.spec`: premise `kb.length + vb.length ≤ bbolt.bboltEntryMax`, one
    outcome (`nil`, the entry set; the `ErrValueTooLarge` case gone); proof over `bbolt.Bucket.Put`
    (`etc/link-lean-first-backend.txt`). `backend.batchTx.{unsafePut, UnsafePut, UnsafeSeqPut}`,
    `backend.batchTxBuffered.{UnsafePut, UnsafeSeqPut}`: the same premise.
  - **The constant.** `etcdKeyMax` `2 ^ 27` → `2 ^ 27 - 2 ^ 19` (the request check's bound,
    `etcdMaxRequestBytesOk`), so that a key and a value, encoded, fit an entry; in place of the proposed
    sum bounds (no change to `ChPutsLe`, `irrPutsLe`, `TxnOp.putsLe` or `MarshalIRR`). Ledger entry.
  - **Trust boundary, two length facts** (approved by the coordinator; ledger entries):
    `proto.Marshal.spec` (KeyValue): post `(kvEncode kv).length ≤ key + value + 128`;
    `schema.MustUnsafeSaveConfStateToBackend.spec`: premise `storage.csOkN n cs`, the callback's
    `vb.length ≤ 25 * n + 128`.
  - **mvcc.** `MvccReachable.notify` requires `ChPutsLe etcdKeyMax pend` (`reach_putsLe`: a reachable
    state's log and notified log put short keys and values); the write handle (`mvccTxnI .write`) carries
    `ChPutsLe etcdKeyMax pend` (law `mvccTxn_write_putsLe`, proved in `Api.lean`); `KV.Put.contract`,
    `Txn.Put.contract`: premise `k.length ≤ etcdKeyMax ∧ vv.length ≤ etcdKeyMax`. Internal:
    `storeTxnWrite.{put, Put}`, `metricsTxnWrite.Put`, `writeView.Put` (the same premise),
    `storeTxnWrite.delete` (`k.length ≤ etcdKeyMax`), `storeTxnWrite.{deleteRange, DeleteRange}`,
    `metricsTxnWrite.DeleteRange` (`LogPutsLe etcdKeyMax ilog ∧ ChPutsLe etcdKeyMax pend`),
    `writeView.DeleteRange` (the log's bound from the index certificate); `keyPutOk` (the bridge's put
    condition) has the entry bound; `meta_entry_fits` (compaction records).
  - **The server's txn and apply.** `txn.put`: `o.key ≤ etcdKeyMax ∧ (¬ ignoreValue → o.val ≤ etcdKeyMax)`
    (an `IgnoreValue` put's stored value bounded by the write handle's law); `txn.Put`: both;
    `txn.executeTxn`, `txn.txn`: every operation of the branch `putsLe etcdKeyMax`; `txn.Txn.specSole`:
    `TxnPreA log t ∧ t.putsLe etcdKeyMax`. `apply.putPre`/`putPreW`/`txnPre`/`txnPreW` and `apply.rqOk`,
    `rqSmall` carry the request's bound; `rqSmall_of_small` takes `irrPutsLe etcdKeyMax rq`, from the KV
    invariant's `logPutsOk` (`entryOk_of_shape`, `entryOkOn_of_shape` take `entryPutsOk m`).
    `EtcdServer.apply.spec`, `EtcdServer.applyEntries.spec`: premise `logPutsOk` of the batch;
    `EtcdServer.applyAll.specBatch`: the same in its pure part; `clusterWorkloadOk(M)`, `srvC(M)`: also
    `logPutsOk L` (from `kvWork`'s).
  - **The conf state.** `storage.csIdCount`, `csIdMax = 2 ^ 20`, `csOkN`; `csInv` keeps `csOkN csIdMax`;
    `BackendHooks.SetConfState.spec` takes it; `epCsOk` carries `csIdCount c ≤ csIdMax`
    (`epCsOk_of_csOptA` takes it); `EtcdServer.applyConfChange.spec`: premise
    `GMap.size γs.raft.cfg ≤ 2 ^ 20` (`srvApRes_cfg_size`); `EtcdServer.applySnapshot.specSnapM`: premise
    `csIdCount sv.Metadata'.ConfState' ≤ csIdMax` (`snap_csIdCount`, from the certificate);
    `restart_snapOnceR`: premise `GMap.size γr.raft.cfg ≤ 2 ^ 20`.
  - **Examples.** mvccrand: values `"v" ++ itoa n` (`newVal_short`). mvccfull: `runCfgOk` gains
    `MaxVal ≤ 2 ^ 20 ∧ Depth ≤ 2 ^ 20` (`Main`'s `MainConfig`: `5000`, `4`); `writerCtx`'s last pure part,
    `runner.newVal.spec` (premise `0 ≤ MaxVal ≤ 2 ^ 20`, post `v.length ≤ etcdKeyMax`),
    `runner.genSubs.spec` (the keys' and `MaxVal`'s bounds), `runner.writeSub.spec`, `opValid`'s put
    clause and `subsOk`'s (key and value `≤ etcdKeyMax`); the model's `PVals`/`opPend_vals`.
