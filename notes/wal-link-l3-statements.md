# WAL link L3: the server-statement stop (old → new)

**Date:** 2026-11-18. **Branch:** `wal-link`. For etcd-grove-03 (scope `notes/wal-link-scope.md` §3.3, §3.5, §6).
What is in Lean at this stop: the vocabulary (`Proof/go_etcd_io/etcd/server/v3/storage/WalRecs.lean`: `WalA`,
`WalH`, `storage.walOpen` moved there from `InvOpen.lean`, `walRecs`, `walBaseLb`, `walSnapRec`, `walFiles`,
`walPurgeRight`, `walMetaIs`, their laws) and `storage.storage.Release.spec` in place (`Spec/.../storage__Release.lean`,
proof `Proof/.../storage__Release.lean`, `ReleaseNext.lean` deleted). Everything below that file (`WalApi.lean` and
the server's clients) is NOT yet restated: the branch does not build past `WalRecs`/`storage__Release` until the
statements below are approved and applied.

## 1. The vocabulary (trusted opaques/axiom → definitions)

| Old | New |
|---|---|
| `opaque walRecGName (w : Loc) : GName`, `opaque walBaseGName (w : Loc) : GName` | gone (`WalH.γh`, the history-prefix ghost name) |
| `walRecs (w : Loc) σ sized := ghostVar (walRecGName w) 1 (σ, sized) ∗ monoNatAuthOwn (walBaseGName w) 1 σ.b` | `walRecs (h : WalH GF) σ sized := ∃ d, walDiskAt h.dir d ∗ monoListAuthOwn h.γh 1 d.H ∗ walNamed h.dir ∗ ⌜walFoldChkFrom walFresh (walSrvHist d.H) = some σ ∧ d.metadata = h.md ∧ (sized → walEntsSized d.H)⌝` |
| `walBaseLb (w : Loc) i := monoNatLbOwn (walBaseGName w) i` | `walBaseLb (h : WalH GF) i := ∃ H0, monoListLbOwn h.γh H0 ∗ ⌜∃ σ0, walFoldChkFrom walFresh (walSrvHist H0) = some σ0 ∧ i ≤ σ0.b⌝` |
| — | **new** `walSnapRec (h : WalH GF) i m := ∃ H0, monoListLbOwn h.γh H0 ∗ walSyncedLb h.dir (i+1) ∗ ⌜H0[i]? = some (snap m)⌝` (persistent; Q5) |
| `axiom walFiles (dir : GoString) id cid σ sized`, `axiom walFiles_timeless` | `walFiles (a : WalA GF) id cid σ sized := ∃ d, walDiskAt a.dir d ∗ walSyncedLb a.dir |d.H| ∗ walNamed a.dir ∗ walUnlockedTok ∗ osCallPerm (callKey a.R a.dir) ½ ∗ ⌜walRead (walSrvHist d.H) = some σ ∧ d.metadata = walMetaEnc id cid ∧ (sized → walEntsSized d.H)⌝` (exclusive now; Q5); `walFiles_timeless` an instance |
| `opaque walPurgeRight (dir : GoString)` | `walPurgeRight (h : WalH GF) := walPurgeW h.w h.dir` |
| `opaque walMetaRaw w id cid`, `walMetaIs w id cid := □ walMetaRaw w id cid` | `walMetaIs (h : WalH GF) id cid := ⌜h.md = walMetaEnc id cid⌝`, `walMetaEnc id cid := optVarintField 1 id ++ optVarintField 2 cid` (protobuf-go's bytes of `&Metadata{NodeID: &id, ClusterID: &cid}`, `bootstrap.go:712-715`) |
| `opaque walDirOf (w : Loc)` | gone (`h.dir`) |
| `opaque storage.walGName w`, `storage.walOpen w q := dghostVar (walGName w) (own q) ()` | `storage.walOpen (h : WalH GF) q := walOpenWS h.Sio walSrvP walSrvMr h.w h.dir h.γ q ∗ walAreaOk walCodec walSrvMr h.R h.jr h.r` (fractional) |
| `config.walDirOf` | unchanged (opaque; P2 states the dedicated directory, the non-dedicated branch is unused) |

`WalA` = the fs instances (`ExtSemantics fsExt`, `FsSemOk`, `HasExt fsExt`), `W : WalGS`, `Sio`, `FsStepSat (NoIoErr Sio)`,
`cov : walCov Sio` (every inode: Q3), `R jr r` (area), `dir`. `WalH` extends it with `BasicIntoValInj`, the wal/os/ioutil
package assumptions, `w`, `γ : WalShN`, `md`, `γh`. So no server module gains fs instance arguments. `walSrvHist H` = the
history's entries unwrapped (`walEntUnwrap`); `walEntsSized H` = every entry record is `walEntW c` with `entSizeOk c`.

Laws kept, re-proved over `h`: `walRecs_timeless`, `walRecs_excl`, `walRecs_baseLb`, `walBaseLb_mono`,
`walRecs_saveSnap_baseLb`, `walRecs_baseLb_le`, `walRecs_unsize` (Q6 dropped it because layer 1's `d.sized` could not be
cleared; with `sized` meaning `walEntsSized` it is free, so it stays — form). New laws needed by the clients (after the go):
`walRecs_open` (the durable state out, back with the same history: what `Release`'s AU and `Close` need),
`walRecs_save`/`walRecs_saveSnap` (the AU of layer 1 from the server's AU, with the history lb updated).

## 2. `isWalStorage` (sealed contract → proved from `NewStorage`)

`isWalStorage (st : GoInterface)` → `isWalStorage (st : GoInterface) (h : WalH GF)`; the laws' common changes: AU mask
`⊤` → `walAuMask` (layer 1's; the clients' AUs open only `rnDurN`), every error arm gone (`err = nil` under `h.cov`),
`storage.walOf st` → `h`.

- **Save.** Old: `∀ sized q hp (hs : HardStateModel) sl esL es Q, {{ walOpen w q ∗ hardStateAt hp hs ∗ sl ↦*□ esL ∗
  walSaveEnts sized esL es ∗ AU <{∃∃ σ, walRecs w σ sized ∗ ⌜WalSaveOk σ es⌝}> @ ⊤,∅ <{walRecs w (walSave σ hs.toM es)
  sized, COMM Q}> }} Save hp sl {{ err, walOpen w q ∗ ((⌜err = nil⌝ ∗ Q) ∨ ⌜¬ walSaveOk⌝) }}`.
  New: `∀ sized q hp (hs : HardStateM) sl esL (cs : List EntryC) Q, {{ walOpen h q ∗ hsOptC hp hs ∗ sl ↦*□ esL ∗
  ([∗list] l;c ∈ esL;cs, entRoC l c) ∗ ⌜∀ c ∈ cs, walEntWOk (walEntW c) ∧ (sized → entSizeOk c) ∧
  uint.nat c.model.Index' < 2^64-1⌝ ∗ AU <{∃∃ σ, walRecs h σ sized ∗ ⌜WalSaveOk σ (cs.map EntryC.model)⌝}> @ walAuMask,∅
  <{walRecs h (walSave σ hs (cs.map EntryC.model)) sized, COMM Q}> }} Save hp sl {{ err, ⌜err = nil⌝ ∗ walOpen h q ∗ Q }}`.
  Changes: `hardStateAt` → `hsOptC` (raft's canonical hard state: `walHsIn_of_hsOptC`); the entries always as frozen
  contents (`walSaveEnts false`'s `entriesAt` form dropped: the server's `P` needs the content, Q6); the index premise
  (new, from raft's room `σ.last ≤ 2^61-1`) and `walEntWOk` (valid unknown fields, nonempty, < 2^48 bytes: from
  `entSizeOk` + raft's `ufWire`); `walSave_spec` (the `entriesAt` corollary) goes, `walSaveSized_spec`/`walSaveRn_spec` stay.
- **SaveSnap.** Old: `{{ walOpen w q ∗ sn.Metadata ↦{dq} mp ∗ smPtsV mp dq' md ∗ AU<…walRecs w σ sized…> @ ⊤ }} SaveSnap sn
  {{ walOpen w q ∗ sn.Metadata ↦{dq} mp ∗ smPtsV mp dq' md ∗ ((⌜nil⌝ ∗ Q) ∨ ⌜¬ walSaveOk⌝) }}`.
  New: `∀ sized q sn mp dq (m : SnapMetaC) Q, {{ walOpen h q ∗ sn.Metadata ↦{dq} mp ∗ metaRoC mp m ∗
  ⌜m.index.isSome ∧ m.term.isSome ∧ metaWalC m = walSnapCanon m.model⌝ ∗ ⌜m.model.Index' = 0 ∨ m.confState.isSome⌝ ∗
  ⌜uint.nat m.model.Index' < 2^64-1 ∧ (walSrvMr.encSnap m.model).length < 2^40⌝ ∗ AU <{∃∃ σ, walRecs h σ sized ∗
  ⌜uint.nat m.model.Index' = σ.b → m.model.Term' = σ.base.term'⌝}> @ walAuMask,∅ <{walRecs h (walSaveSnap σ m.model) sized,
  COMM Q}> }} SaveSnap sn {{ err, ⌜err = nil⌝ ∗ walOpen h q ∗ sn.Metadata ↦{dq} mp ∗ Q ∗ ∃ i, walSnapRec h i m.model }}`.
  **No budget** (step 3: the snapshot room budget `walUsed`/`walSnapBudget` is gone from layer 1, so nothing of it reaches the
  law). The metadata frozen (`smPtsV` fractional → `metaRoC` persistent: R5; raft's `CreateSnapshot` result is frozen once
  handed out). **F2's conf-state discharge** (decision below): the premise `metaWalC m = walSnapCanon m.model`
  (the record's bytes are the marshaller's: L2's `snapEnc (metaWalC m) = Mr.encSnap m.model`, in its sufficient
  canonical form). Post gains `walSnapRec` (what `Release` takes).
- **Sync.** Unchanged but `walOpen h q` (layer 1's `walLenLb` premise is met inside: the share carries it — to check when
  proving; else `Sync` takes `walLenLb`).
- **Release (new law; the clients called `storage.Release.spec` on the concrete `*storage` before).** `∀ q sn mp dq dq' md
  γd img Rm i m (Q : IProp GF), m.Index' = md.Index' → {{ walOpen h q ∗ sn.Metadata ↦{dq} mp ∗ smOpt mp dq' md ∗
  inv snapDirN (snapDirInv ss γd img Rm) ∗ □ (∀ j, ⌜j < md.Index'⌝ -∗ Rm j) ∗ walSnapRec h i m ∗
  AU <{∃∃ σ s, walRecs h σ s}> @ walAuMask,∅ <{walRecs h σ s, COMM Q}> }} Release sn {{ err, walOpen h q ∗ sn.Metadata ↦{dq} mp
  ∗ smOpt mp dq' md ∗ Q ∗ ⌜err = nil ∨ ¬ snap.dirReadOk ss⌝ }}` (`ss` the storage's snapshotter, an `isWalStorage` parameter
  through `rnStorageOf`). Old (`storage.storage.Release.spec`, axiom): `storageSnap p ss → {{ … ∗ walBaseLb (walOf …) md.Index' }}
  … {{ … ⌜err = nil ∨ ¬ releaseOk⌝ }}`.
- **Close.** Old: `{{ walOpen w 1 ∗ walRecs w σ sized ∗ walMetaIs w id cid ∗ walPurgeRight (walDirOf w) ∗ ⌜σ.b ≤ σ.commit⌝ }}
  Close {{ (⌜nil⌝ ∗ walFiles (walDirOf w) id cid σ sized) ∨ ⌜¬ walCloseOk⌝ }}`. New: `{{ walOpen h 1 ∗ walRecs h σ sized ∗
  walMetaIs h id cid ∗ walPurgeRight h ∗ ⌜σ.b ≤ σ.commit⌝ }} Close {{ ⌜err = nil⌝ ∗ walFiles h.toWalA id cid σ sized }}`.

## 3. `storage.storage.Release.spec` (Spec file, in place)

Old: the axiom's statement (above; no WAL resource but `walBaseLb`). New: `ReleaseNext`'s statement verbatim, now the
spec (`(P : WalPbIn GF) (Mr : WalMarshal)`, fs instances and `Sio` as section variables): `storageOver p w ss ∗ storageRd p w
∗ isSnapshotter ss ∗ … ∗ walAreaOk ∗ walOpenWS Sio P Mr w dir γ q ∗ walSyncedLb dir n ∗ AU <{∃∃ d, walDiskAt dir d ∗
⌜d.H[i]? = some (snap ⟨cs, md.Index', t⟩) ∧ i < n⌝}> @ walAuMask,∅ <{walDiskAt dir {d with unl := max d.unl (walReleasePos …
md.Index')}, COMM Q d}>` → `storageRd p w ∗ … ∗ walOpenWS … q ∗ (∃ d, Q d) ∗ ⌜err = nil ∨ ¬ dirReadOk ss⌝`. Its
`wp_proof` is `wp_proofNext` renamed; **the axiom `storage.storage.Release.wp_proof` is gone**. The server reaches it only
through `isWalStorage`'s Release law (proved in `rnNewStorageOk`'s proof, where the fs instances are `h`'s).

## 4. `rnNewStorageOk` (premise of every example → proved)

Old: `□ ∀ lg w ss, {{ ⌜storage.walReady w⌝ }} NewStorage lg w ss {{ st, isWalStorage st ∗ ⌜rnStorageOf st ss ∧ storage.walOf st = w⌝ }}`.
New: `□ ∀ lg ss (h : WalH GF), {{ isSnapshotter ss }} NewStorage lg #h.w ss {{ st, isWalStorage st h ∗ ⌜rnStorageOf st ss⌝ }}`
(`walReady` gone: the handle `walOpenWS` is what a read WAL is, carried by `walOpen h 1` which the boot slot gives;
`storage.walOf` gone: `h` threaded; `rnStorageOf` keeps the snapshotter, `storageSnap` defined as `storageOver`'s `p.s`).
It leaves every example's `Hprem` (`etcdstart.commonPremises`) once proved (after the go).

## 5. `diskOk` and the environment opaques

Old: `diskOk := dbOpensOk ∧ snapOpensOk ∧ walSaveOk ∧ walCloseOk ∧ walCreateOk`. New: `diskOk := dbOpensOk ∧ snapOpensOk`
(`walSaveOk`, `walCloseOk`, `walCreateOk` gone, replaced by `NoIoErr` over all inodes, `WalA.cov`/`.sat`, in the closed theorems'
semantics: §1 #11); `snapOpensOk`'s `releaseOk` → the snapshotter's `dirReadOk` (already in it). `walReady`, `walOf` gone.

## 6. Exported-spec meaning changes from step 3 (already in the branch, for the record)

- `walCutPos` widened (third case `∃ m, H[b-1]? = some (snap m)`): `walNameBound`/`walOpenPos`/`walReleasePos`, hence
  `WAL.Open.spec`, `openAtIndex.spec`, `WAL.ReadAll.spec`, `WAL.ReleaseLockTo.spec`, `cut.spec` (wal-fsext exported), and
  WalTester's oracle (`examples/etcd/wal/ref.go` `cutPos`, `tCutPos_abs`, `nameBound`): a WAL file may start right after a
  snapshot record; Open/ReleaseLockTo's "locked from" positions may move later only past such a cut.
- The budget removed: `WAL.SaveSnapshot.spec` (and storage `SaveSnap.spec`) take no `walUsed` and give none; `Save.spec`'s room
  premise over `walFreshRoom` (was `walSaveRoom` with the snapshots' budget); `walHdl` has no γ; `walOpenWS_alloc` returns
  no `walUsed`. Strictly weaker preconditions (more callers), same posts.
- `Create` takes `SaveSnapshot.spec` at its `P` (was `walPbNone`).

## 7. Trust-base delta of L3 (expected, after the clients are re-proved)

Counts: `etc/tcb-baseline.txt` 890 axioms / 4 sorries after the lean merge (fmt soundness removed `fmt.ErrorfWrap.wp_proof`)
→ **888 / 4** (`walFiles` and `storage.storage.Release.wp_proof` leave it; `walFiles_timeless` is not listed there);
each of the 25 etcd/k8s collections loses both (−2) and gains layer 1's wal-fsext axioms they do not yet have.
Checked at this stop: `WalRecs.lean`, `Spec/.../storage__Release.lean`, `Proof/.../storage__Release.lean` 0 errors (lean-check
`-a`); the WAL proofs, the wal Link (regenerated) and WalTester's Links build after the merge (`/shared/tmp/wallink/m4.log`).

Removed: axioms `walFiles`, `walFiles_timeless`, `storage.storage.Release.wp_proof` (−3; `purgeFile` went at L2); opaques
`walRecGName`, `walBaseGName`, `walPurgeRight`, `walMetaRaw`, `walDirOf`, `storage.walGName`, `storage.walReady`, `storage.walOf`,
`walSaveOk`, `walCloseOk`, `walCreateOk` (trusted vocabulary); premise `rnNewStorageOk`. Added: nothing in this stage beyond what
§6 of the Scope lists (layer 1's 24 wal-fsext axioms join the server collections; `ReleaseSnapDBs` was added at L2). Restated
(still trusted): `bootstrapContract`'s/`bootstrapRestartContract`'s WAL slots (`wal.bootRes`, `wal.bootOk`, `wal.restartOk`) over
`WalH`/`WalA` (the slot gives `∃ h, walOpened h … ∗ walPurgeRight h` with `h.dir = cfg.DedicatedWALDir'`); `walOpened h dir id cid σ
sized := walOpen h 1 ∗ walRecs h σ sized ∗ walMetaIs h id cid ∗ ⌜h.dir = dir⌝`.

## 8. Decisions needed

1. **F2 (SaveSnap's record bytes).** raft's own snapshots are canonical (`ProgressTracker.ConfState()` sets every list and
   `AutoLeave`, no unknown fields; `tracker.go:148-155`), but a *received* snapshot's metadata keeps its wire content.
   Options: (a, recommended) the law's premise `metaWalC m = walSnapCanon m.model`, discharged for the apply thread's
   snapshot from raft's `ConfState()` facts, and for the raft loop's received snapshot from the cluster (single member:
   none is received; k members: a raft fact that `MsgSnap` metadata is canonical, every member being this code), at
   ~200-400 lines in raft's snapshot facts; (b) layer 1's snapshot record bytes from the client's object (as entries:
   `P.snapIn`), the read side needing only index and term (`walDecSnap`): a layer-1 change, ~500-1000 lines.
2. The forms of §1 (`WalA`/`WalH` fields, `walSnapRec`, `walRecs_unsize` kept, `walMetaEnc`, `storage.walOpen` moved).
3. The law texts of §2, `rnNewStorageOk` §4, `diskOk` §5.
