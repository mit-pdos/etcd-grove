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
