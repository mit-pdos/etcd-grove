# Unit `specgap`: are the `fsExt` WAL specs strong enough for etcd's server? (branch `wal-c-specgap`, 2026-11-15)

Base `origin/wal-int` (`bf4cf547b9`). This unit only reads and reports: no Lean file is edited, nothing is
built, no axiom or `sorry` is added. Its outputs are this note and the draft ledger entries under
"Proposed by specgap (2026-11-15)" in `notes/specs-only/ledger.md`.

Abbreviations: `Sp/` = `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/`, `S/` =
`LinuxFs/Proof/go_etcd_io/etcd/server/v3/storage/wal/`, `SP/` = `SpecPlan/Spec/go_etcd_io/etcd/server/v3/`,
`G/` = the fork's server module at `0b50f0426` (`~/go/pkg/mod/github.com/upamanyus/etcd/server/v3@v3.0.0-20261112123031-0b50f04262d9/`).
`RI` = `notes/wal-crash-handoff/restart-wal-interface.md`. `P1`-`P13` are the proposals in §4 (and in
the ledger).

## 0. Verdict

**No.** C6 cannot be written over the current `fsExt` WAL specs. The pure read facts are mostly there:
I1-I11 are reachable from `ReadAll`'s `walReadAllOk` and the W4b lemmas, and the crash keep law already
exists (`WalFs.walDiskAt_crash_keep`). But eight gaps block the server. Four need a user decision:
- **Environment failures (P1).** etcd calls `lg.Panic` on WAL errors, and `fsExt` lets any system call fail.
- **The lock model (P8).** The purge cannot be specified without it.
- **The failed-`Close` path at boot (P7).** It needs the lock model or a fork change.
- **The record contents (P5).** The WAL's marshaller must speak of wire content, not of a model.

Four are WAL-side spec changes:
- **The shared handle (P2).** The raft loop and the apply thread call the WAL concurrently under a
  read lock.
- **The area layout (P3).** `member/snap` and the boot `TouchDirAll`s collide with the area's slots.
- **The call permission (P4).** The boot-time calls need the whole permission while the backend is open.
- **From `Exist` to `Create` (P6).** `Exist`'s `false` does not give `Create`'s `walAbsent`.

SpecPlan is too strong in one respect: its storage specs post `RET nil` under the opaque `diskOk`,
which no proof over `fsExt` can produce. It also lacks premises the WAL needs (record sizes, indices).

## 1. The server's WAL calls: verdict per call

Each row gives the call site in `G/`, what the server relies on afterwards, SpecPlan's statement,
the `fsExt` spec (`Sp/`), and the verdict.

| # | Call (site) | Server relies on | SpecPlan | `fsExt` spec essentials | Verdict |
|---|---|---|---|---|---|
| 1 | `wal.Exist(WALDir)` (`etcdserver/bootstrap.go:77`) | `false` → `bootstrapNewWAL` → `Create` (needs no WAL); `true` → the restart path | inside `bootstrap`'s trusted contract (`SP/etcdserver/bootstrap.lean:8`), no per-function spec | needs `walUnlockedTok`, `osCallPerm 1`, `walAreaRes`, `InArea`/`NameOk`; post `b = false → ExistFalseOk o` (`o = none` or a fresh unnamed WAL); `true` claims nothing; the `false` arm rests on the hypothesis `fileutil.ReadDir.specChildIs` (ENOENT, pending the user, ledger 2026-11-14) | **insufficient**: `ExistFalseOk` does not give `Create`'s `walAbsent dir` (P6); `osCallPerm 1` (P4); the ENOENT hypothesis |
| 2 | `fileutil.IsDirWriteable(WALDir)` (`bootstrap.go:85`) | no error | in the contract | no spec usable: it creates and removes `member/wal/.touch`, a non-`.wal` name of the WAL directory, whose claim the WAL invariant owns (`walOthersL`) | **insufficient**: needs a WAL-side law lending that name, or the call dropped (P3, P13) |
| 3 | `wal.ValidSnapshotEntries` (`bootstrap.go:451`, `recoverSnapshot`) | the newest valid `(index, term)`; its `ConfState` `proto.Clone`d; then `Open` at it | in the contract (`Recs.validSnaps`, `Recs.newest`) | token framed, `osCallPerm 1`; post `walSnapsAt ps (walValidSnaps H cut)` (persistent `snapRoC` of each record) | **sufficient with adapter lemmas**: `newestSnapshotEntry`'s result is `walNewestPair` (pure; `>=` keeps the last among equals, which is `walNewestPair`'s order); the list is never empty because `cut = 0` while nothing purges, so `walValidSnaps H 0` begins with `Create`'s `(0, 0)`; `proto.Clone` of the conf state from `snapRoC`. Blocked only by `osCallPerm 1` while the backend is open (P4) |
| 4 | `wal.Open(WALDir, &walsnap)` (`bootstrap.go:675`) | a handle for `ReadAll`; `err ≠ nil` → `Fatal` | in the contract | `osCallPerm 1`, token, `walSnapIdTerm sp s`; the AU raises `unl` (bookkeeping); success `walOpeningF ∗ osCallPerm ½` | **sufficient with adapter**: `walSnapIdTerm` of the literal `walpb.Snapshot{Index, Term}` (a freeze lemma); blocked by P4 |
| 5 | `w.ReadAll()` (`bootstrap.go:680`) | I1-I11 (`RI` §2): `st`, `ents`, metadata decodable (`pbutil.MustUnmarshalMessage` panics otherwise), the handle open for append; with `ForceNewCluster` the server **mutates** `st` (`:640`, `:787`) and `append`s to `ents` (`:781`) | in the contract; replay = `Recs.hs`, `Recs.entsAfter` | AU premise `some s = walNewestPair (walValidSnaps H cut)`; success `walReadAllOk H cut s σ ∗ P.hsIn hp σ.hs ∗ sl ↦*□ esL ∗ walEntsIn ∗ mdp ↦*□ d.metadata ∗ walOpenWF ∗ walNamed ∗ walSyncedLb |H| ∗ walLenLb ∗ walPurgeW`; error `walReadFailedF` | **sufficient with adapter lemmas** for I1-I11 (§2); **insufficient** for `ForceNewCluster`: the hard state and the slice come back read-only (P10). The error path is row 6 |
| 6 | `w.Close()` after a failed `ReadAll`, **error ignored**, then `wal.Repair` (`bootstrap.go:683-689`) | `Repair` callable | in the contract | `WAL.Close.specFailed`: `(walUnlockedTok ∗ osCallPerm ½) ∨ ⌜err ≠ nil⌝`; `Repair` takes the token | **insufficient**: on the `err ≠ nil` arm the token is lost, yet the server calls `Repair`. In Go, `Close` returns before unlocking, so `Repair`'s blocking `LockFile` hangs: a hang, not a panic, but unprovable without locks (P7) |
| 7 | `wal.Repair` (`bootstrap.go:689`) | `true` → `Open` again; `false` → `Fatal` | in the contract | token, `osCallPerm 1`; post `(walUnlockedTok ∨ b = false)`, state unchanged | **sufficient** (the `true` arm gives the token back); P4 |
| 8 | `wal.Create(WALDir, md)` (`bootstrap.go:717`, `bootstrapNewWAL`) | a WAL at `Recs.init md`; error → **`lg.Panic`** | contract + `Wal.walCreating` (rename to fsync), `Recs.init`; `diskOk` excludes failure | `InArea`, `NameOk`, `dir < 2^59`, `cleanAbsPath r`, `md ≠ []`, `md < 2^41`, `WalMarshalCreateOk`; `walAreaRes`, **`osCallPerm 1`**, token, AU from **`walAbsent`**; three outcomes, two of them errors | **insufficient**: the error arms are reachable and the server panics (P1); `osCallPerm 1` with the backend open (P4); `walAbsent` from `Exist` (P6); the area (P3). `md ≠ []` holds through an adapter: both `Metadata` fields are set, so the encoding is non-empty, but `etcdserverpb.Metadata` needs a `proto` spec. `walCreating` maps onto `walDiskAt dir (walDurFresh md)` (`named = false`), with the move to `.member` done after `Create` returns (`walNamed`): adapter |
| 9 | `serverstorage.NewStorage(lg, w, ss)` (`bootstrap.go:613`) | `isStorage`, `storageOpen 1` | `SP/storage/NewStorage.lean`: takes `Wal.walOpen w wd` | the handle is `walOpenWF` (exclusive) | **insufficient** as it stands: the storage invariant cannot share an exclusive handle between two goroutines that hold only read locks (P2) |
| 10 | `storage.Save` → `w.Save` (`etcdserver/raft.go:264`, `Fatal` on error; `bootstrap.go:782`, `Fatal`) | entries and state durable when `MustSync`; a restart reads them | `SP/storage/storage__Save.lean`: two AUs (`walRecs` → `walWriting` → `walRecs (R.save …)`), `RET nil` under `diskOk`, premise `es = [] ∨ floor < k ≤ floor+|log|+1`, **no size or index premise** | one AU committed after `w.mu.Lock()` to `H ++ [save hs es]`; premises: every index `< 2^64-1`, every encoding `< 2^40`, `walEntsIn P` (canonical entries); success `walLenLb (|H|+1)`, `walMustSync → walSyncedLb (|H|+1)`; error: handle lost | **insufficient**: shared handle (P2); raft's entries are not canonical (P5, already recorded by U4b); SpecPlan lacks the size and index premises (P12); SpecPlan's `RET nil` (P1; the raft loop `Fatal`s, so honest error arms suffice there). The two-AU shape maps onto one: `walWriting R w` ≈ `walDiskAt` with the mark below `|H|`, and `crashedMid` ⇐ `walImg` (adapter, P11) |
| 11 | `storage.SaveSnap` → `w.SaveSnapshot` (`raft.go:257`, `Fatal`; **`server.go:2147`, `lg.Panic`**, the apply thread's `snapshot()`) | the record durable; then `Release` at it | `SP/storage/storage__SaveSnap.lean`: two AUs, `RET nil` | `walSnapAt Mr sp md cs`: the bytes equal `Mr.encSnap md`, whose conf state is canonical (`AutoLeave` set); index `< 2^64-1`; encoding `< 2^40`; always synced | **insufficient**: (a) after a restart `ep.confState` is `buildConfStateFromV3store`'s `ConfState{Voters, Learners}` with `AutoLeave` nil (`bootstrap.go:145`, `server.go:804`), so the apply thread's first snapshot before a conf change is **not canonical** (P5); **[withdrawn 2026-11-15, `notes/wal-units/autoleave.md`: `ep.confState` is the `MemoryStorage` snapshot's, which `ApplySnapshot`/`Snapshot` ensure (`AutoLeave` set); measured]** (b) shared handle (P2); (c) `lg.Panic` on error (P1); (d) no bound on a received snapshot's index (`RI` gate 5) |
| 12 | `storage.Sync` → `w.Sync` (`raft.go:279`, `Fatal`) | the hard state synced before `notifyc` and `Release` | `SP/storage/storage__Sync.lean`: `RET nil` | needs `walLenLb w dir n`, gives `walSyncedLb n`; error: handle lost | **insufficient**: `WAL.Sync` does **not** take `w.mu` (`storage/wal/wal.go:994`). Under `storage`'s read lock it runs concurrently with the apply thread's `Release` → `ReleaseLockTo`, which writes `w.locks` (`wal.go:1039`) while `sync`'s `tail()` reads it: a Go data race (candidate, §3). No shared-handle spec of `Sync` is possible without the mutex (P2). The `walLenLb` comes from `Save` (fine) |
| 13 | `storage.Release` → `w.ReleaseLockTo` (`server.go:1111` and `:2151`, **`lg.Panic`** on error) | files below the snapshot released; the restart still reads | `SP/storage/storage__Release.lean`: premise `∃ w ∈ R.validSnaps, w.index = sn.index`; post `R.release i` (floor raised) | premise: a **synced** snapshot record of index `a` at `i < n` (`walSyncedLb n`), weaker than SpecPlan's; post: `unl` raised (bookkeeping); `err` unconstrained, handle kept | **sufficient with adapter** for the WAL state (nothing is purged in `fsExt`, so it is stronger than `Recs.release`), except: the server panics on `err ≠ nil` and the post does not exclude it (P9); shared handle (P2); the purge that gives `release` its meaning cannot be specified (P8) |
| 14 | `storage.Close` → `w.Close` (`raft.go:441`, **`lg.Panic`**; `bootstrap.go:160`) | none afterwards | `SP/storage/storage__Close.lean`: `storageOpen 1 ∗ walPurgeRight` → `RET nil ∗ walPurgeRight` | `walOpenWF ∗ walPurgeW` → `(Q d ∗ walSyncedLb |H| ∗ walUnlockedTok ∗ osCallPerm ½) ∨ err ≠ nil`; `walPurgeW` consumed | **sufficient** but for P1 (the panic on error). SpecPlan returning `walPurgeRight` is stronger than any user needs: SpecPlan should consume it, as `fsExt` does (P11) |
| 15 | `storage.MinimalEtcdVersion` (`storage/storage.go:102`; downgrade only, `schema.UnsafeMigrate`) | some version; `panic` on any error | `SP/storage/storage__MinimalEtcdVersion.lean`: `RET v` under `diskOk` | **no specs** of `WAL.LatestSnapshotEntry`, `Reopen`, `wal.MinimalEtcdVersion`; `LatestSnapshotEntry` calls `ValidSnapshotEntries` on the WAL's own directory, but VSE takes `walUnlockedTok`, which the open handle holds | **insufficient** (P13; low priority: downgrade path). `Reopen` closes every lock while `purgeFile` runs: suspected window, §3 |
| 16 | `EtcdServer.purgeFile` (`server.go:608`, `fileutil.PurgeFileWithDoneNotify`) | removes only unlocked, released files | `SP/etcdserver/EtcdServer__purgeFile.lean` (`srvPurge`) | none possible: `fsExt` has no lock state (`notes/wal-fsext-plan.md` gap 3, Q1 [user]) | **insufficient** (P8; `RI` gate 8) |
| 17 | `w.SetUnsafeNoFsync()` (`bootstrap.go:678`, `:720`) | — | — | no spec; every `walSyncedLb` assumes `unsafeNoSync = false` | **config premise** `UnsafeNoFsync = false` (`RI` gate 4) |

## 2. Boot and restart as a whole

**Area boot (`walBoot0`, `walBootCrash`, `S/Boot0.lean:89`, `S/BootCrash.lean:395`).** Both give
`walAreaOk ∗ walAreaRes` and the token (`walInv_crash` gives the token after a crash). Neither fits
the server's member directory:
- **The area must be a root of the shared mode that exists at boot (`hr : (r, jr) ∈ R`).** On a
  first start etcd creates `member/` itself (`TouchDirAll(MemberDir)`, `bootstrap.go:68`), after
  `TouchDirAll(DataDir)` (`:64`). Neither call has a spec here: `DataDir` lies above the root (only
  `O_RDONLY` opens there), and `member/.touch` is under the WAL invariant's area claim. Both are the
  tester's U1 mismatch 1.
- **`AreaSlot` covers every `walNameOk` name.** `walNameOk` means non-empty, no `/`, no `.`
  (`GooseLang/Ext/AbsDisk/Paths.lean:34`), so `snap` is a slot. `walBoot0` requires no entry at any
  slot (`hslots`), while `bootstrapSnapshot` creates `member/snap` before the WAL
  (`TouchDirAll(SnapDir)`, `bootstrap.go:211`). `walBootCrash`'s `bootWals` would take `member/snap`
  for a WAL directory, and the invariant holds half the area's claim on `snap`. This is U1 mismatch 4.
- **`DirsRoots`: every durable directory is a root, and `RootsOk` forbids nested roots.** So
  `member/snap` (whose renames the snapshotter fsyncs) cannot be a root beside `member/`. Its
  durability must come from a claim below the area's root.

Proposal P3. With it, `walBoot0` at the first start needs `member/` to exist and be empty of `wal*`
names. That is a world premise of the closed theorem, together with `cleanAbsPath` of the data
directory and `DedicatedWALDir = ""` (`RI` gate 9). `walBootCrash` additionally needs `hfo`, the
files-only fact; it is not derivable (ledger 2026-11-14), so it is a premise until the invariant
owns those claims.

**I1-I11 against `ReadAll`'s post** (all over the history `I = d.H.map toM` and `cut`; `cut = 0`
always, because `pur` never moves without a purge):
- I1 (wf), I2 (last ≤ 2^61-1), I3 (b ≤ commit ≤ last), I4 (the snapshot at the base), I6 (entries
  from `Save`s): `walReadCut_*` (`WalHistLemmas`) through `walReadAt_cut` (`WalReadAllPost.lean:99`).
  At `k = 0` this needs `walReadsBack I` (`walCommitLe` and `walRead I ≠ none`). That is a
  **server invariant** fed by raft's `Ready` facts (`RI` gate 6, invariant (a)); the post itself
  does not say which `k`. **Adapter, provable from current definitions, given the invariant.**
  - I2 also needs `walIdxLe (2^61-1)`, from raft's room fact.
  - I4: the post's `σ` comes from the fixed-base fold and carries no snapshot. The server builds its
    snapshot from VSE's pair `s`, the same `s` as the fold's base: fine.
- I5: `walReadAllOk_hs` (`WalReadAllPost`). **Available.**
- I7: `walReadAllOk_walRead` (`:126`), under `¬ walHasMaxIdx` (in `WalsBounded`), a record of index
  `s.1`, and `s.1 ≤` the last commit. **Available.**
- I8: `walInv_crash` + `walStCrash` + `WalFs.walDiskAt_crash_keep` (the tester's `tWal_crash` uses
  it). **Available.**
- I9 (sizes): does not arise. `P.entIn` carries no size cache (`walEntSmall` only), so `γs.sz` must
  be re-derived in C6 from `walEntSmall`, or dropped.
- I10: `mdp ↦*□ d.metadata`, kept across crashes. The server's `MustUnmarshalMessage` needs `d.metadata`
  to be `Create`'s marshalled `Metadata`. That is a server invariant: there is no WAL at the first boot,
  so the metadata traces back to `Create`. It also needs a round-trip law of `etcdserverpb.Metadata`
  (not registered). **Adapter plus a missing `proto` spec.**
- I11: `walOpenWF ∗ walSyncedLb |H| ∗ walNamed ∗ walLenLb ∗ walPurgeW`. **Available.**

**`ValidSnapshotEntries` → `Open` → `ReadAll` consistency.** VSE commits unchanged, and the server
holds the token and its `walDiskAt` throughout, so `d` and `cut` are the same at `Open`. The pair
`Open` gets is `walNewestPair` of VSE's list (row 3). **Adapter, pure, provable.**

**Crash and durability claims the server needs.**
- **Synced prefixes.** `Save` gives `walSyncedLb (|H|+1)` under `walMustSync` (raft's `MustSync`,
  `MustSyncLaw`, proved in U4b). `SaveSnapshot` always gives it, `Sync` gives `walLenLb n →
  walSyncedLb n`, and `Close` gives `walSyncedLb |H|`. These are enough for a follower's
  "persist before send" and for the snapshot `Sync` before `notifyc`.
- **`walNamed`** comes from `Create` and `ReadAll` (F-N4).
- **SpecPlan's `Recs.crashed`/`crashedDuring` against `walImg`.** An image keeps every synced op
  (`j ≥ m`). Every `Save` with entries or a new term or vote syncs, and so does every
  `SaveSnapshot`. So what an image can drop is trailing commit-only `Save`s (`Recs.crashed`), or the
  write in flight (`crashedDuring`, whose torn `Save` with a zero hard state is `crashedMid`'s first
  case). **Adapter** over the server's invariant "every op past the mark is a commit-only `Save` or
  the one in flight" (P11).
- `unsafeNoFsync` off: a config premise.

## 3. Go findings (to report; not written into `issues/` by this unit)

Recorded 2026-11-15 (branch `wal-c-findings`): 1 reproduced under `-race` at upstream `main` and the
fork, `issues/etcd-wal-sync-releaselockto-race.md` (with `fix.patch`); 3 reproduced (a purge with a
short interval), `issues/etcd-storage-downgrade-reopen-purge-panic.md`; 2 by code reading only,
`nonissues/etcd-bootstrap-repair-close-error-hang.md`. None is fixed or reported upstream.

1. **`WAL.Sync` holds no lock** (`storage/wal/wal.go:994-996`), and `storage.Sync` takes only
   `st.mux.RLock` (`storage/storage.go`). Here is how the two calls can overlap:
   - Batch N: the raft loop hands it over and moves on once raft has advanced (`raftAdvancedC`).
   - Apply thread, batch N: `applyAll` → `snapshotIfNeededAndCompactRaftLog` → `snapshot()` →
     `storage.SaveSnap` / `storage.Release` (`server.go:2147-2151`). `applySnapshot`'s `Release`
     (`:1111`) can overlap the same way.
   - Raft loop, batch N+1, carrying a received snapshot: `storage.Sync()` (`raft.go:279`).
   - The race: `ReleaseLockTo` writes `w.locks = w.locks[smaller:]` while `sync()` reads `w.tail()`.
     The encoder has its own mutex, so the race is on the slice header.

   This is a candidate data race, not yet run under `-race`. The fix is one line in the fork
   (`Sync` takes `w.mu`). Check upstream first.
2. **`openWALFromSnapshot` ignores `w.Close()`'s error before `wal.Repair`** (`bootstrap.go:683`).
   If the close's fdatasync fails, `Close` returns before releasing the locks
   (`wal.go:1053-1066`), and `Repair`'s blocking `LockFile` then waits forever on a lock this
   process holds. The result is a boot hang instead of a `Fatal`. A fork fix would check the error.
   Low severity, but it is what keeps row 6 unprovable.
3. **Suspected window in `storage.MinimalEtcdVersion`** (downgrade only): `Reopen` closes the WAL,
   which releases every lock, while `purgeFile` may run. Before `Open` relocks, the purge could
   delete unlocked segments beyond `MaxWALFiles`, including the one holding the snapshot record, and
   `MinimalEtcdVersion` would then panic. This is from reading the code only; it needs a Go test.

## 4. Proposed changes, in priority order

Each is a draft ledger entry (`notes/specs-only/ledger.md`, "Proposed by specgap"); none is made.

1. **P1 [user]. Environment failures against `diskOk`.** etcd `lg.Panic`s on WAL errors at five
   sites: `Create` (`bootstrap.go:719`), `snapshot()`'s `SaveSnap`/`Release`, `applySnapshot`'s
   `Release`, `onStop`'s `Close`, and `Reopen`. `fsExt` lets every system call fail, so these panics
   are reachable in the model, and no `⌜diskOk⌝` premise can refute an error arm.
   - Options:
     - (a) a failure ledger in `fsExt`: a ghost "some call failed" flag, with the adequacy theorem
       conditioned on it staying false. This is a trusted change.
     - (b) fork changes, `Panic` → `Fatal` at those sites.
     - (c) a closed theorem whose notion of failure exempts a panic after an I/O error.
   - SpecPlan's storage specs get honest error arms either way.
2. **P2. A shared-handle form of the WAL specs.** `Save`, `SaveSnapshot` and `ReleaseLockTo` would
   take a fraction of a handle whose resources sit in `w.mu`'s invariant; `Close` takes all of it.
   `Sync` too once it locks; until then the fork fix of §3.1.
3. **P3. The area layout.**
   - Slots: parametrize `AreaSlot`/`walAreaRes`/`walBoot*` by the WAL's own name `nm` (slots `nm`
     and `nm.<sfx>`), and hand every other name of the area to the client.
   - Durable directories: allow one below a root, through spine claims (or make the data directory
     the root).
   - A law for `IsDirWriteable(WALDir)`'s `.touch`.
   - The world premises of the closed theorem: the data directory exists, is clean and absolute,
     and `DedicatedWALDir = ""`.
4. **P4. Fractional call permission** for `Exist`, `ValidSnapshotEntries`, `Open`, `OpenForRead` and
   `Repair` (no directory operation). `Create` keeps `osCallPerm 1`. The server then needs the
   backend quiescent at `bootstrapNewWAL`, through a backend-side protocol that returns the
   permission, or through a reordering in the fork [user].
5. **P5 [user for the representation]. Record contents.** `Mr.encEntry`/`encSnap` over wire
   contents (`EntryC`/`WalSnapC`), not models. Raft's entries carry the proposal's presence (U4b),
   and the restarted server's conf state has `AutoLeave` nil. **[The conf-state half withdrawn 2026-11-15: `notes/wal-units/autoleave.md`.]** Alternative for the conf state alone:
   a one-line fork fix in `buildConfStateFromV3store`.
6. **P6. `Create` from `Exist`'s `false`.** `Create`'s AU starts from `walDirIs dir o ∗
   ⌜ExistFalseOk o⌝`, not `walAbsent`. Or `Exist`'s `false` gives `o = none` once the ENOENT model
   fix lands and the moved-aside state is recorded.
7. **P7 [user].** The failed-`Close`-then-`Repair` path: the lock model, or a fork fix (§3.2).
8. **P8 [user, Q1].** The lock model, for the purge (`purgeFile`, `Reopen`'s window) and `unl`.
9. **P9. `ReleaseLockTo` posts `err = nil`.** Every lock is a segment whose name parses, by the
   invariant's `WalDirClaim`/`walNameStr`; the server panics on an error.
10. **P10. `ReadAll` returns the hard state owned** (`HsO`, which the client can freeze), and the
    entries slice's capacity, for `ForceNewCluster`'s mutations.
11. **P11 (SpecPlan).** Restate `Wal.Recs`/`walRecs`/`walWriting`/`walCreating` as views over
    `walDiskAt` (`RI` §2), with the refinement lemmas of §2. `storage.Close` consumes the purge right.
    `storage.*`'s `RET nil` gets error arms (with P1).
12. **P12 (SpecPlan).** `storage.Save`/`SaveSnap` gain the WAL's premises: indices `< 2^64-1`,
    encodings `< 2^40`, conf state set unless the index is 0. They come from raft's invariants; a
    received snapshot's index bound is still open (`RI` gate 5).
13. **P13.** Specs of `WAL.LatestSnapshotEntry`/`Reopen` over an open handle, for
    `MinimalEtcdVersion` (downgrade only).

## 5. What is left, next step

The coordinator triages P1-P13. The user decides P1, P5's representation, P7 and P8. P2, P3, P4, P6,
P9 and P10 are WAL-side statement changes that can go ahead now; P2 and P3 are the largest. The SpecPlan
side (P11, P12) follows the ledger.

The provable adapters, all pure or nearly so, could be written before C6:
- `newestSnapshotEntry` ≡ `walNewestPair`;
- `walReadAllOk` → `walReadCut` under `walReadsBack`;
- the `walImg` → `Recs.crashed`/`crashedMid` refinement;
- `walCreating` ≈ `walDiskAt (walDurFresh md)`.
