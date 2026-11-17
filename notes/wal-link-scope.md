# Scope: linking the real WAL (layer 1) to the server's WAL contract (layer 2)

**Date:** 2026-11-17. **Branch:** `wal-link` off `lean` `9702d5707e`. **Author:** the wal-link agent of
etcd-grove-03. A Scope (notes and Go tests only, no Lean changed or built). Go evidence:
`examples/wallink/link_test.go` (claims C1-C7 below; `GOWORK=off go test -race ./wallink/` from `examples/`,
all pass at the etcd pin `8c28a4296`; log of the run in the handoff).

Abbreviations: `E/` = `Proof/go_etcd_io/etcd/server/v3/etcdserver/`, `St/` = `Proof/go_etcd_io/etcd/server/v3/storage/`,
`SW/` = `Spec/go_etcd_io/etcd/server/v3/storage/wal/`, `PW/` = `Proof/go_etcd_io/etcd/server/v3/storage/wal/`,
S/ = the fork's `server/` at `8c28a4296`. Layer 1 = etcd's `wal` with bodies over `fsExt` (`SW/`, `PW/`,
`etc/tcb-collections/wal-fsext.txt`); layer 2 = the trusted contract `isWalStorage` and its vocabulary (below).
This Scope is the "C6" stage that `notes/wal-fsext-plan.md` and `notes/wal-crash-handoff/restart-wal-interface.md`
(§2-§5, gates 1-13) defer to; it keeps their analysis and adds what reading layer 1's final specs against the
server shows.

**Summary.** The link is feasible in four stages for the single-member theorems (L0-L3, about 5-9k Lean lines),
with four findings that shape it: (F-a) layer 1's handle is exclusive while etcd's raft loop and apply thread use
the WAL concurrently (`w.mu` serializes them, C2): layer 1 needs a shared-handle variant; (F-b) layer 1 admits one
open WAL per generation and needs the whole call permission for `Create`'s directory rename, while every
k-member example opens k WALs in one process and creates member j's WAL while member j-1's appends and cuts
(C5): the k-member theorems need a trusted `fsExt` refinement (L4); (F-c) `fsExt` covers only absolute paths
under its roots, and the examples' data directories are relative (`name + ".etcd"`,
`examples/lib/etcdstart/common.go:72`): the examples must move to absolute directories (or `fsExt` gain a cwd);
(F-d) layer 2's error arms (`¬ storage.walSaveOk`) cannot be produced from layer 1's honest error posts; the
server needs the user-approved `NoIoErr` premise on the WAL's files (the apply thread panics on any
`SaveSnap`/`Release` error, S/etcdserver/server.go:2158-2163). bootstrap's WAL part (`wal.Create`/`Open`/`ReadAll`
inside the names-only `bootstrap`) and the crash-model restart stay out (L5, L6: their own Scopes).

---

## 1. The trusted items the link touches, and the closed theorems they reach

Reach: the `etc/tcb-collections` baselines (`grep -l "^axiom X$"`), and for premises the closed statements'
`Hprem`/`Hdbo` (`examples/*/Results.lean`). "All 25" = the etcd/k8s example collections (auth3, authN, authkv,
cachekv, compactkv, k8scompactor, k8setcd3, leaseN, leasecatchup, leaseexpiry, leaseexpiryN, leasekv, linkv3p,
linkvtxn, m2, putget, putget3, putgetN, restart1, restart3, restartN, server, server-raft, txnlinfaultsN, watchkv).

| # | Item (file:line) | Kind today | Reaches | What the link does (stage) |
|---|---|---|---|---|
| 1 | `rnNewStorageOk` (`E/InvNodeStart.lean:243`; taken by `NewServer.spec`, `Spec/.../NewServer.lean:331`; bundled in `etcdstart.commonPremises`, `examples/lib/etcdstart/Defs.lean:200`) | premise (every example's `Hprem`) | every etcd/k8s closed theorem (all start through `commonPremises` or its copies) | **proved** from `serverstorage` with bodies over layer 1 (L2-L3); leaves `Hprem` |
| 2 | `isWalStorage`'s four laws (`E/WalApi.lean:78`; `Save`, `SaveSnap`, `Sync`, `Close`) | sealed trusted contract, inside #1's post | as #1 | **re-proved** (L3); statement changes in §3 |
| 3 | `walFiles`, `walFiles_timeless` (`St/WalRecs.lean:202,205`) | axioms | all 25 | **defined** over layer 1 (`walDiskAt` closed, synced, named, read back): −2 axioms (L3) |
| 4 | `walRecs`, `walBaseLb` (`St/WalRecs.lean:108,112`) over opaque `walRecGName`/`walBaseGName` (`:86-87`) | sealed defs, opaque names | as #1 | **defined** over `WalFs.walDiskAt` and a base ghost allocated in the slot (L3) |
| 5 | `walPurgeRight`, `walMetaRaw` (`St/WalRecs.lean:216,219`), `walDirOf` (`:181`), `config.walDirOf` (`:67`) | opaques | as #1 | `walPurgeRight` := layer 1's `walPurgeW w dir`; `walMetaIs` := the handle's metadata bytes are `etcdserverpb.Metadata{id,cid}`'s encoding; `walDirOf w` threaded as an explicit `dir`; `config.walDirOf` defined (`ServerConfig.WALDir()`) (L3) |
| 6 | `storage.walReady`, `walGName`, `walOf`, `walSaveOk`, `walCloseOk`, `walCreateOk`, `storageSnap` (`St/InvOpen.lean:60,71,79,84,89,93,115`); `storage.walOpen` (`:191`) | opaques; def over an opaque name | as #1; `diskOk` (`:123`) is every closed theorem's `Hdbo` | `walOpen w q` := a share of the shared handle (L1a) + the area's persistent facts; `walReady` an IProp (the handle's lock invariant); `walOf st` threaded (`storageOver st w`); `walSaveOk`/`walCloseOk`/`walCreateOk` leave `diskOk`, replaced by `NoIoErr` on the WAL's files (L3) |
| 7 | `wal.bootRes`, `wal.bootOk`, `wal.restartOk` (`E/WalApi.lean:311,326,448`), the slots of `bootstrapContract` (`E/InvBoot.lean:524`, row `Hwal` of `bootOk`, `:238`) and `bootstrapRestartContract` (`E/InvRestart.lean:659`, row `Hwal`, `:429`; premise `storage.walSaveOk`, `:671`) | sealed slots inside trusted premises | all 25 (`bootPremise`), restart1/3/N (`bootPremiseR`) | **bodies restated** over layer 1's resources; the slot laws (`wal.bootOk_start`, `wal.restartOk_facts`, `wal.restartOk_start`) re-proved; the clients unchanged (the slot convention's purpose). The contracts stay trusted (their text changes) until L5 |
| 8 | `storage.storage.Release.wp_proof` (`Proof/.../storage/storage__Release.lean:26`; spec `Spec/.../storage__Release.lean`) | axiom | 25 (all but restartN-only cases; see the baselines) | **proved** (`ReleaseLockTo` over layer 1, then `snap.Snapshotter.ReleaseSnapDBs`, which stays names-only under a new, narrower axiom: its half of today's spec). Net 0 axioms, the WAL half out of the trust base (L2) |
| 9 | `EtcdServer.purgeFile.wp_proof` (`E/EtcdServer__purgeFile.lean:24`) | axiom | 24 | **proved** with its body under `Cfg.MaxWALFiles = 0` (S/etcdserver/server.go:612-614: no WAL purge; C7: no example sets the field), −1 axiom (L2). A configuration with purging is L6 |
| 10 | `dataDirFresh` (`St/WalDir.lean:31`), `dataDirAbsent`, `dataDirsApart` (`Proof/runtime/Start.lean:143,147`), `goose_adequacy_start_files`' data-directory part (`:217`) | axioms | dataDirFresh 25, the others 24 | the WAL area's start resources come from `Fs.fs_start` + `WalFs.walInv_alloc` (`PW/Crash.lean:652`) under a checkable `FsInit`-level premise (the area present and empty); `dataDirFresh` keeps only the backend's half (bbolt and `snap` stay trusted); `dataDirAbsent`/`dataDirsApart` replaced by that premise where they speak of the WAL (L3) |
| 11 | `storage.walSaveOk`/`walCloseOk`/`walCreateOk` inside `diskOk` | opaque Props in a closed premise | all 25 (`Hdbo`) | removed from `diskOk`; the closed theorems' file semantics becomes `fs_semantics` restricted by `NoIoErr S_wal` (the user-approved premise kind, 2026-11-15) (L3) |

Untouched: `bootstrap` itself (names-only; its non-WAL parts), `OpenBackend` and bbolt's tokens (`backend.fileHolds`),
`snap`, `monitorStorageVersion` (its downgrade path calls `MinimalEtcdVersion`, risk R6).

## 2. Translating `serverstorage` (S/storage/storage.go) with bodies

`Code/go_etcd_io/etcd/server/v3/storage.toml` today translates `!*` plus the hooks and `OpenSnapshotBackend`.
Change: add `NewStorage`, `storage.SaveSnap`, `storage.Release`, `storage.Save`, `storage.Close`, `storage.Sync` to
`translate`, `storage.MinimalEtcdVersion` stays names-only (an axiom never reached by a linked result; R6); add
`go.etcd.io/etcd/server/v3/storage/wal` and `.../wal/walpb` to `imports` (both translated with bodies already,
project etcd). `etc/goose.py --project etcd`; `etc/gen-init.py` (the package's init gains no variable). The file
has no construct Goose rejects: an interface, a struct with an `RWMutex`, `defer`, a struct literal of
`walpb.Snapshot` with pointer fields read through getters (as in `wal`'s own code).

Callees and their specs:

| Go call (S/storage/storage.go) | Spec |
|---|---|
| `st.mux.RLock/RUnlock/Lock/Unlock` | Perennial `sync.RWMutex.wp_*` (`ownRWMutex rw P`): `P` holds `p.w ↦ w`; reader slots per the bounds plan (the laws take a share) |
| `snap.Metadata.Index/Term`, `GetConfState()`, `GetIndex()` | raftpb getters (the raft proofs' `smPtsV`/`smOpt`) |
| `st.w.SaveSnapshot(&walsnap)` | `WAL.SaveSnapshot.spec(NoErr)` (`SW/WAL__SaveSnapshot.lean`), shared-handle variant (L1a) |
| `st.w.Save(s, ents)` | `WAL.Save.spec(NoErr)` (`SW/WAL__Save.lean`, `WAL__SaveNoErr.lean`), shared variant |
| `st.w.Sync()` | `WAL.Sync.spec(NoErr)`, shared variant (the fork's fix 0006 makes `Sync` take `w.mu`: S/storage/wal/wal.go:1003-1006) |
| `st.w.Close()` | `WAL.Close.spec(NoErr)`, shared variant (the whole share) |
| `st.w.ReleaseLockTo(i)` | `WAL.ReleaseLockTo.specNoErr` (`SW/WAL__ReleaseLockTo.lean`), shared variant |
| `st.s.ReleaseSnapDBs(snap)` | **new axiom** `snap.Snapshotter.ReleaseSnapDBs.wp_proof`: the `snapDirInv` half of today's `storage.Release.spec` (removal facts below `i`, `nil` or `¬ releaseOk`) |

`snap.Snapshotter.SaveSnap` is not a callee: the fork's `storage.SaveSnap` writes only the WAL record (the
`.snap` file is gone from this path). Nothing Goose cannot take.

## 3. How each `isWalStorage` law follows from layer 1, and what must change

### 3.1 The records: `walRecs` as the eager fold of layer 1's history (C1)

Layer 2's records are a σ-level model updated eagerly (`walSave`, `walSaveSnap`, `St/WalRecsCore.lean:35`, `St/WalRecs.lean`);
layer 1's state is the history `d.H` (`WalDur`, `GooseLang/Ext/AbsDisk/Impl.lean:163`), and a restart reads `walRead`
(`St/WalHist.lean`), which drops the snapshot records above the final commit and then folds. Definitions:

- `walRecs w σ true := ∃ d, WalFs.walDiskAt dir d ∗ monoNatAuth γb σ.b ∗ ⌜walFoldChkFrom walFresh (d.H.map toM) = some σ ∧ d.sized⌝`
  (the unfiltered checked fold, `St/WalHist.lean`). `Save` appends `save hs es`; by `walFoldChkFrom_append`
  (`St/WalHistLemmas.lean:1415`) and "the `readEnt` fold is `appendEnts` under `WalSaveOk`" (new, ~80 lines) the
  fold becomes `walSave σ hs es`; `SaveSnapshot` appends `snap md` and the fold becomes `walSaveSnap σ md`
  directly (`walFoldChkFrom`'s `.snap` case is `walSaveSnap`).
- **The read bridge** (new pure lemma, L0): if the fold of `H` is `some σ` and `σ.b ≤ σ.commit`, then
  `walRead H = some σ`. Proof sketch: the base only grows along the fold (`walSaveSnap_base_ge`); a snapshot
  record above the final commit would have raised the base above it; so the filter `walKeep σ.commit` keeps every
  record that changed the fold, and drops only no-ops. **C1** (`TestEagerModelReadsBack`: 200 random
  server-shaped histories through `serverstorage`, graceful `Close`, bootstrap's read): the read equals the eager
  fold in all 178 runs with `σ.b ≤ σ.commit`; in all 22 runs with `σ.b > σ.commit` (a received snapshot not yet
  followed by its `Save`) the read fails (`ErrSliceOutOfRange`) or differs. So the guard is necessary, and it is
  the `Close` law's existing premise (`σ.b ≤ σ.commit`, `E/WalApi.lean:104`).
- `walFiles dir id cid σ true := ∃ d, WalFs.walDiskAt dir d ∗ walSyncedLb dir |d.H| ∗ walNamed dir ∗ walUnlockedTok ∗
  osCallPerm ½ ∗ ⌜walRead (d.H.map toM) = some σ ∧ d.sized ∧ d.metadata = metaEnc id cid ∧ walCommitLe … ∧ walIdxLe (2^61-1) …⌝`
  (what `Close.spec` returns, `SW/WAL__Close.lean`, plus the read bridge; the last two conjuncts are what a later
  `ReadAll` needs, `restart-wal-interface.md` §2 (a)). It becomes exclusive (today "no axiom says it is
  exclusive"): a strengthening.
- `sized`: layer 1's `d.sized` is `true` from `walDurFresh` on and no step clears it. The law at `sized = false`
  (`walSave_spec`, `E/WalApi.lean:125`) is not provable (layer 1's update needs `d.sized = sized`) and has no
  client (only `walSaveSized_spec`/`walSaveRn_spec` are used: `raftNode__start.lean`, `InvRestart.lean`): drop it;
  `walRecs_unsize` goes with it.

### 3.2 The handle: exclusive in layer 1, shared in the server (C2, C4) — finding F-a

Layer 1's `walOpenWF P Mr w dir` (`PW/Handle.lean:597`) is exclusive, its `w.mu` protecting `True` (`:567`). The
server writes the WAL from two threads at once: the raft loop (`Save`, `SaveSnap` of a received snapshot, `Sync`,
S/etcdserver/raft.go:257-280) and the apply thread (`SaveSnap`, `Release`, server.go:2158-2163; `applySnapshot`'s
`Release`, :1122), each under the storage's *read* lock (S/storage/storage.go:62-98). **C2**
(`TestStorageConcurrentClients`, `-race`): 2000 `Save`s racing 20 `SaveSnap`+`Release` pairs through one storage: no
race, every entry read back. What serializes them is `w.mu`, taken first by `Save`, `SaveSnapshot`,
`ReleaseLockTo`, `Sync` and `Close` (wal.go:1003-1105). So layer 1 needs **a shared-handle variant (L1a)**:
`walOpenWS w dir q` := a fraction of a ghost token ∗ `isMutex w.mu (walOpenWF … ∨ failed)`, and the five specs
restated to take it (the lock acquired inside gives the handle; `Close` with the whole fraction leaves the
mutex's invariant in a closed state). The proofs change only at the lock's acquire/release; the bodies' proofs
are reused. `storage.walOpen w q` := `walOpenWS w dir q ∗ □ walAreaOk …`. **C4** (`TestSaveAfterClosePanics`): a
`Save` after `Close` fails (`seek …: file already closed`): the whole share for `Close` stays.

### 3.3 Law by law

| Law (layer 2) | Layer 1 spec | Mismatches and the resolution | Server-side statement change (old → new) |
|---|---|---|---|
| `Save` (`E/WalApi.lean:81-88`) | `WAL.Save.specNoErr` | (i) handle: L1a. (ii) records: §3.1. (iii) objects: layer 1 is parametric in the client's protobuf model `P : WalPbIn` (`PW/Handle.lean:166`: `hsIn`, `entIn`, persistent) and marshaller `Mr : WalMarshal`; the server's `P` := `hardStateAt` frozen, `entRoC` (`walSaveEnts true`), its `Mr` := protobuf-go's encoders of `raftpb.HardState`/`Entry` (the raft proofs' `pbSchemaOf`), and `walAreaOk`'s law `encState < 2^32` from it. `hardStateAt hp hs` must be persistent (frozen) or the law takes a discarded fraction. (iv) layer 1's premises `index < 2^64-1` and `|encEntry e| < 2^40`: the second from `entSizeOk` (`entBytes ≤ 2^31`, `Proof/go_etcd_io/raft/v3/PbSized.lean:44-47`); the first is **new** in the law (raft's room fact, `σ.last ≤ 2^61-1`, discharges it at `raftNode.start`). (v) error: layer 1's error arm commits the update and loses the handle; with `NoIoErr` on the WAL's files (F-d) the `NoErr` spec returns `nil` and needs the room `k` (`walOpenWFR`), which the shared handle keeps. (vi) mask: layer 1's AU is at `walAuMask`, layer 2's at `⊤`; an AU's mask cannot be shrunk, so the law's AU moves to `walAuMask` (the clients' AUs open only `rnDurN`) | AU `@ ⊤` → `@ walAuMask`; `sized` fixed `true` (no `walSave_spec`); new premise `∀ e ∈ es, uint.nat e.Index' < 2^64-1`; error arm `∨ ⌜¬ storage.walSaveOk⌝` → gone (`err = nil` under `NoIoErr`) |
| `SaveSnap` (`:89-99`) | `WAL.SaveSnapshot.specNoErr` | (i)-(ii), (v)-(vi) as `Save`. (iii) `storage.SaveSnap` builds `walpb.Snapshot{Index, Term, ConfState: GetConfState()}` (storage.go:63-68), **sharing** raft's conf-state object, which layer 1's `walSnapAt` (`PW/walpb/PbSnapshot.lean:272`) needs frozen: the law's `smPtsV mp dq' md` becomes discarded (□) on the conf state, or layer 1 takes a fraction. (iv) layer 1's `md.Index' = 0 ∨ cs`: **C3** (`TestSaveSnapNeedsConfState`) a positive index with no conf state is refused (`missing ConfState`), on which the apply thread panics (server.go:2158-2159); an empty conf state survives the wire; raft's snapshot model must say the conf state is present above index 0 (new fact of `smPtsV`, or a premise). `uint.nat md.Index' < 2^64-1` (gate 5: a received snapshot's index is bounded only through the cluster's room invariant: open question Q4) and `|encSnap md| < 2^40` (a bound on the conf state's voters, from the cluster's member bound: Q4). (v) the post must give **a persistent witness of the synced record** (`walSnapRec w i md`: position `i` of the history is `snap md`, `i < ` the synced mark), which `Release` takes (layer 1's `ReleaseLockTo` needs it, `SW/WAL__ReleaseLockTo.lean`); new in layer 1: a monotone history-prefix fragment | AU mask; `smPtsV` on the conf state discarded; post gains `walSnapRec`; error arm gone |
| `Sync` (`:100-101`) | `WAL.Sync.specNoErr` | needs `walLenLb w dir n` (held inside the shared handle); layer 2 asks nothing and promises nothing more | none (error arm already absent) |
| `Close` (`:102-108`) | `WAL.Close.specNoErr` | (i) whole share. (ii) `walPurgeRight dir` := `walPurgeW w dir` (indexed by `w` too: form). (iii) post: `Close` returns `Q d`, `walSyncedLb dir |d.H|`, `walUnlockedTok`, `osCallPerm ½`; with `walNamed` (from the handle) and the read bridge at `σ.b ≤ σ.commit` this is `walFiles` (§3.1) | error arm `∨ ⌜¬ storage.walCloseOk⌝` → gone; `walPurgeRight (walDirOf w)` → `walPurgeRight w dir` |
| `rnNewStorageOk` (`E/InvNodeStart.lean:243`) | `NewStorage` (translated) | pre `⌜storage.walReady w⌝`, post `isWalStorage st ∗ ⌜rnStorageOf st ss ∧ storage.walOf st = w⌝`: `storage.walOf` is a pure function of an interface value, and the translated `NewStorage` returns a fresh `*storage` whose `w` lives in the heap (mutable under `mux`: `MinimalEtcdVersion` reassigns it), so no proof gives `walOf st = w` | `⌜walReady w⌝` → `walReady w` (persistent IProp); `storage.walOf st` → an explicit `w` with `storageOver st ss w` (persistent); 71 lines in 17 files mention `storage.walOf` (mechanical threading, ~300 lines) |
| `storage.Release.spec` (`Spec/.../storage__Release.lean`) | `ReleaseLockTo.specNoErr` + new `ReleaseSnapDBs` axiom | the premise `walBaseLb w i` does not give layer 1's "a synced snapshot record of index `i`"; **C6** (`TestReleaseLockToWithoutRecord`): Go needs no record (it compares the locks' first indices), but the server always releases at a snapshot it saved just before (server.go:2158/2162; raft.go:257 before applySnapshot's server.go:1122), so `walSnapRec` from `SaveSnap`'s post meets layer 1's premise | `walBaseLb (storage.walOf …) i` → `walSnapRec w j md` with `md.Index' = i`; the error arm `¬ releaseOk` stays only for `ReleaseSnapDBs` |

### 3.4 What `walFiles` becomes in `fsExt` terms, and the area

The WAL's directory must be `r/nm` for an area `r` (a clean absolute path, `cleanAbsPath`, `GooseLang/Ext/AbsDisk/Paths.lean:26`;
`InArea`, `PW/Inv.lean:67`) whose `walInv` holds every entry with a WAL name (`walNameOk`: no `/`, no `.`). Two
placements:

- **P1, the default layout** (`<dd>/member/wal`, area `<dd>/member`): the area also holds `snap` (a WAL name by
  `walNameOk`): `walInv` would claim the backend's directory (gate 9). Needs a name restriction parameter in
  `walInv` (layer 1 re-proof of `Inv`, `Crash`, `Create`, `Exist`), and the area's `walInv` allocated in the
  middle of the run, after `bootstrap`'s `TouchDirAll(DataDir)`, `TouchDirAll(MemberDir)` (S/etcdserver/bootstrap.go:64-68)
  create it (`walInv_alloc` is the boot-time allocation only: a new `walInv_alloc_fresh` from an empty durable
  directory, ~300-600 lines).
- **P2, a dedicated WAL directory** (`ServerConfig.DedicatedWALDir`, etcd's `--wal-dir`) at `/<root_i>/wal`, one
  `fsExt` root per member existing at start (`FsInit`): the area exists and is empty at start, allocated once at
  adequacy by `walInv_alloc`; it holds only the WAL; no layer-1 change for names. Needs the examples' Go to set
  `DedicatedWALDir` and the contracts' `cfg.DedicatedWALDir' = go!""` (`wal.bootRes`, `E/WalApi.lean:311`; `srvFiles`,
  `E/InvRestart.lean:96`) to become the dedicated directory.

Either way the paths become absolute (F-c: `fsExt` resolves only absolute paths under its roots,
`GooseLang/Ext/Fs/Tree.lean:121`, `Impl.lean:21-48`; today `DataDir: name + ".etcd"`). **Recommendation: P2** for
L3 (no layer-1 change, the trusted backend never shares a directory with the WAL, the area is allocated where the
`fsExt` start resources are), P1 later if the default layout matters.

### 3.5 Server-side statements that change (summary)

`isWalStorage`'s laws (AU mask; `sized` fixed; `Save`'s index premise; `SaveSnap`'s conf-state persistence and
`walSnapRec` post; no error arms); `rnNewStorageOk` (`walReady` an IProp, explicit `w`); `storage.Release.spec`
(`walSnapRec` for `walBaseLb`); `walPurgeRight w dir`; `walDirOf w` and `storage.walOf st` replaced by explicit
parameters; `diskOk` loses three conjuncts; `bootCfgOk` gains `cfg.UnsafeNoFsync' = false` (layer 1's `walSyncedLb`
assumes it; gate 4) and `cfg.MaxWALFiles' = 0` (§1 #9); the slots' bodies; `purgeFile.spec` gains the `MaxWALFiles`
fact (through `isServerReadM`'s configuration). Every client re-proof is local (the laws' consumers:
`raftNode__start`, `raftNode__onStop`, `EtcdServer__snapshot`, `applySnapshot`, `InvWal`, `InvRaftNode`, `InvRestart`).

## 4. The server's file model elsewhere

1. **`fsExt` becomes load-bearing for the server.** Since the merge the closed theorems run over `etcdFsExts =
   [idIssueExt, fsExt]` with `Hfs : Fs.FsInit …` (`examples/lib/etcdstart/FsExts.lean`), but no server proof takes an
   extension step (the `fileutil` probe takes none). The link makes the WAL's I/O real `fsExt` steps: the closed
   theorems allocate `osInv`/`osSharedInv` (`GooseLang/Ext/Fs/Adequacy.lean:83`, `fs_start`) and each WAL area's
   `walInv` (`walInv_alloc`), per generation's `WalGS`. `Hfs` stays, and the area premise joins it (§1 #10).
2. **Trusted code in the same tree.** Once the WAL's files are `fsExt` state owned by `walInv`, every trusted
   function that touches them must state its footprint, or it claims a WP the faithful translation could not
   have: `purgeFile` (proved under `MaxWALFiles = 0`, C7, so it touches nothing), `storage.Release` (proved),
   `bootstrap` (its WAL slot restated over layer 1's resources: `Create` takes `walAreaRes`, the lock token,
   `osCallPerm 1`; the restart's `Open`/`ReadAll` their resources), `MinimalEtcdVersion` (unreached: R6). `snap`,
   bbolt and `OpenBackend` touch only the data directory (P2) or `member/snap` (P1), outside the area.
3. **One WAL per generation; `Create`'s directory rename** (F-b, gate 1). Layer 1's lock token `walUnlockedTok`
   (`PW/Ghost.lean:385`) and `Create`'s `osCallPerm 1` (`SW/Create.lean`) admit one open WAL per process and no path
   call during `Create`'s rename (the model's rule: a directory rename is stuck while any other path call is in
   flight, `GooseLang/Ext/Fs/Impl.lean:97-101`). **C5** (`TestCreateWhileAnotherWALCuts`): in one process, 20
   `wal.Create`s while another WAL appends and cuts every 64 KB (10 segments): all succeed and read back, as
   `StartMembers` does (member j's bootstrap after member j-1's `Start`, `examples/lib/etcdstart/members.go:41-58`).
   Single-member theorems are unaffected (bootstrap runs before any other path call; `OpenBackend` waits for its
   goroutine). The k-member theorems (putget3, auth3, restart3, putgetN, authN, leaseN, leaseexpiryN, leasecatchup,
   txnlinfaultsN, restartN, linkv3p, k8s etcd3, k8s compactor) need **L4**: a per-area `WalGS` (lock token per
   area) and a trusted refinement of `fsExt`: a directory rename stuck only while a path call in flight resolves
   through the renamed directory or its target (Linux's lookup retries on `rename_lock`; Go example in
   `examples/osfs/semantics/`), with `osCallPerm` scoped to a subtree.
4. **`durableExt`, `WalTester/`, real bbolt.** Unaffected: the main tree's `durable` stays trusted for kvdurable;
   `WalTester/` keeps layer 1's exclusive specs (the shared variant is derived beside them); real bbolt over `fsExt`
   is not the server's backend (`OpenBackend` is names-only), so the backend file stays a trusted token.
5. **Restarts.** restart1/3/N restart in the same process after a graceful stop: `walFiles` (§3.1) carries the
   history, the lock token and the half permission from `Close` to the restart's `bootstrap` (its trusted restart
   contract, `wal.restartOk`'s body over layer 1: `Open` and `ReadAll`'s post with the read bridge give
   `walReadFacts σ`). The crash-model restart (`walCrashKeeps`, the history invariant (a)-(c)) is L6.

## 5. Steps, estimates, checkpoints

Lean lines are estimates at the WAL proofs' rate (layer 1: ~5.5k lines per two weeks of a session).

| Stage | Content | Lines | Checkpoint |
|---|---|---|---|
| **L0** pure | eager fold ⇔ `walSave`/`walSaveSnap` (`readEnt` fold = `appendEnts` under `WalSaveOk`); the read bridge (§3.1); `walCommitLe`/`walIdxLe` from the server's facts | 300-500 | lemmas proved, no trust change; C1 cited |
| **L1a** layer 1 shared handle | `walOpenWS` (`w.mu` holds the handle or a failed state); the five specs' shared variants (`NoErr`), derived exclusive ones unchanged for `WalTester`; the history-prefix fragment and `walSnapRec` from `SaveSnapshot` | 800-1500 | `etc/gen-link.py --walfs` links the variants; wal-fsext collection unchanged |
| **L1b** the server's `P`, `Mr` | `WalPbIn` from `hardStateAt`/`entRoC`, `WalMarshal` from protobuf-go's encoders, `walAreaOk`'s and `ReadAll`'s callee hypotheses (`SW/ReadAllCallees.lean`) discharged with them; `metaEnc` of `etcdserverpb.Metadata` (`pbSchemaOf` entry) | 600-1200 | the laws' premises stated in the server's vocabulary |
| **L2** `serverstorage` + `purgeFile` | goose config, regenerate; specs/proofs of `NewStorage`, `Save`, `SaveSnap`, `Sync`, `Close`, `Release` over L1a; `ReleaseSnapDBs` axiom; `purgeFile` with its body under `MaxWALFiles = 0` | 700-1200 | **HARD STOP**: new axiom `ReleaseSnapDBs`, two axioms gone |
| **L3** the server rebased (single-member) | definitions of §1 #3-#6 over layer 1; the four laws and `rnNewStorageOk` proved; threading `w`/`dir`; slot bodies and laws; area allocation at adequacy (P2), `dataDirFresh` narrowed; `NoIoErr` semantics for the closed theorems, `diskOk` narrowed; examples' absolute dirs (P2: `DedicatedWALDir`), `cfgOk`'s new fields; the 25 Adequacy/Results files | 2500-4500 | **HARD STOP** before (closed statements' premises change: the Freeze package) and at the end (trust-base delta, §6) |
| **L4** k members | per-area `WalGS`; `fsExt`'s scoped directory rename (trusted, Go example, the user's review); `Create`/`cut` re-proved over scoped `osCallPerm`; the k-member examples' allocation | 1500-3000 | **HARD STOP**: trusted semantics change |
| L5 (own Scope) | `bootstrap`'s WAL part with bodies (`bootstrapNewWAL`, `bootstrapWALFromSnapshot`, `openWALFromSnapshot`, `readWAL`, `Repair`'s use), the slots discharged | 3-6k | — |
| L6 (own Scope) | crash-model restart (`wal.restartOk` from `ReadAll` + `walCrashKeeps` + (a)-(c)); a configuration that purges (the server's concurrent purge, gate 8) | — | — |

Order: L0 ∥ L1a ∥ L1b, then L2, then L3 (single-member theorems first; the k-member theorems keep compiling only if
L3 lands with L4, so L3 and L4 land together, or the k-member examples get their WAL resources from L4's per-area
allocation before L3 changes the slots: Q1).

**Risks.**
- R1: L1a's lock invariant interacts with layer 1's `cut` (the file pipeline's goroutine holds a quarter of the call
  permission and `walPipeH`): the handle in the mutex must carry the pipeline's resources; medium.
- R2: the `NoIoErr` premise set `S_wal` must name the WAL's inodes at every state (segments created by `cut`): its
  `IoSet.ino` is by inode at the step's state; layer 1's `NoErr` specs already take `∀ st i, Sio.ino st i` (all
  inodes), the simplest choice (no I/O error on any file): a stronger world premise than needed; narrowing it is
  a follow-up.
- R3: the 25 closed theorems' statements change (semantics restricted by `NoIoErr`, area premise, absolute paths,
  `diskOk`); each is a Freeze item for the user.
- R4: build cost: `WalApi`, `InvOpen`, `WalRecs` are imported by most of the server; L3 rebuilds the server and
  every example (`etc/importers.py --count`); one full build per checkpoint under the 45G slot.
- R5: `hardStateAt` and raft's snapshot metadata may be fractional where layer 1 needs frozen objects (§3.3): if
  raft's `Ready` hands mutable objects, the law needs a clone (Go does not clone): a possible blocker, checked first
  in L1b.
- R6: `MinimalEtcdVersion` (names-only) reassigns `st.w` to a reopened WAL under `mux.Lock()` (storage.go:102-120),
  reached only through `schema.UnsafeMigrate` on a downgrade (S/storage/schema/schema.go:69-71) from
  `monitorStorageVersion` (trusted): its axiom must say no downgrade happens (a cluster version that only rises), or
  the storage's invariant breaks; to check in L2.

**Open questions (each with a recommendation).**
- Q1 (order of the k-member theorems): land L3 and L4 together, or L3 for single-member theorems with the
  k-member examples on a temporary trusted per-member slot? **Recommend together**: a temporary slot would be
  new trusted text that L4 removes.
- Q2 (placement): P1 (default `member/wal`) or P2 (`DedicatedWALDir` under per-member roots)? **Recommend P2** (§3.4),
  a user decision since it changes the examples' Go (a documented etcd flag).
- Q3 (error premise): `NoIoErr` on all inodes (as layer 1's `NoErr` specs take it) or on the WAL's files only?
  **Recommend all inodes now** (the user-approved kind; the server's other files are trusted anyway), narrowing later.
- Q4 (snapshot bounds): `SaveSnapshot`'s `index < 2^64-1` and `|encSnap| < 2^40` for a *received* snapshot (gate 5).
  **Recommend** deriving both from the cluster's room invariant (raft's `σ.last ≤ 2^61-1` holds of every leader's
  log, hence of its snapshots) and the member bound of the k-member theorems (`k ≤ 1000`); if the raft proofs lack a
  cluster-wide room invariant, a premise on `SaveSnap` discharged at `raftNode.start` from the snapshot's
  certificate.
- Q5 (`walFiles`'s exclusivity and `walSnapRec`): adding exclusivity and a new persistent witness are strengthenings
  of trusted vocabulary that becomes defined; **recommend** taking them (form decisions at the L3 Freeze).
- Q6 (`isWalStorage` at `sized = false`): drop the law and `walRecs_unsize` (no client). **Recommend drop.**

## 6. Trust-base delta (after L0-L3, single-member; L4 for the rest)

- **Removed:** axioms `walFiles`, `walFiles_timeless`, `storage.storage.Release.wp_proof`,
  `EtcdServer.purgeFile.wp_proof` (−4); the premise `rnNewStorageOk` (all 25 `Hprem`s); the opaques `walRecGName`,
  `walBaseGName`, `walPurgeRight`, `walMetaRaw`, `walDirOf`, `config.walDirOf`, `storage.walReady`, `walGName`,
  `walOf`, `walSaveOk`, `walCloseOk`, `walCreateOk` (trusted vocabulary, defined or gone); `diskOk`'s three WAL
  conjuncts; the WAL half of `dataDirFresh`/`dataDirAbsent`/`dataDirsApart` and of `goose_adequacy_start_files`.
- **Added:** axiom `snap.Snapshotter.ReleaseSnapDBs.wp_proof` (+1, narrower than the Release axiom it replaces);
  the `NoIoErr` restriction of the closed theorems' file semantics; the area premise on `FsInit` (P2: per-member
  roots present and empty); the examples' configuration facts (`MaxWALFiles = 0`, `UnsafeNoFsync = false`,
  `DedicatedWALDir`), proved from the examples' code like `cfgOk`; layer 1's trust base joins the server's
  collections (`wal-fsext.txt`'s 24 axioms; zap, proto, time already present: about +10 new names per
  collection: `binary.ReadInt64LE`, `fmt.SprintfWalName`/`SscanfWalName`, `io.ReadFull`, `proto.MarshalAppendCachedRecord`,
  `pbRecordC_reg`, `pbSnapC_reg`, `recEncC_ok`, `snapEncC_ok`, `strings.HasSuffix`), and `fsExt`'s trusted semantics
  (`GooseLang/Ext/Fs/Impl.lean`) becomes load-bearing for the server.
- **Restated (still trusted):** `bootstrapContract`'s and `bootstrapRestartContract`'s WAL slots (over layer 1's
  resources; `walSaveOk` leaves the restart contract's premise), `goose_adequacy_start_files` (its data-directory part
  narrowed to the backend), `dataDirFresh` (the backend's half).
- **L4 adds:** the `fsExt` scoped-rename rule (trusted semantics, the user's review).
