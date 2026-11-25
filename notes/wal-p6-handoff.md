# P6 (etcd_safe #52/#50), phase B: re-prove the WAL over the torn-Save fix — handoff

## P6b progress (branch `etcd-safe-p6b`, worktree `/shared/etcd-grove-p6`; keep current at each push)

- **2026-11-25, P6b session 1.** Merged `etcd-safe-p8` @ `1dce32d84a` (clean; the coordinator: merge early).
  **Design revised (v2, `notes/wal-p6b-design.md` top)**: incarnation = a ghost counter (not the inode:
  freshness unprovable from the Fs specs); the views carry it (`walDiskAtI dir i d`, the old names as `∃ i`);
  handle currency through a three-way split of `γI` (walGhost ½, the program's `walOwn` ¼, the lock ¼);
  `walDirKey` keyed by `(dir, i)`. **Lean**: `Ghost.lean` additive core only (`γI`, `γpi`, `incOf`, `walLeI`
  and laws, `walPastI`/`walPastIAuth` and `_le`/`_grow`/`_snap`), checked with `etc/lean-check.py -a`
  (0 errors, no `sorry`); nothing uses it yet, so every proof is unchanged. **Built** at `d9eeabf41a` (local build-slot: `wal.Link`, `CrashS`, `WalRecsCrash`, `WalCrashRead`, WalTester `Link`/`Adequacy`/`TopLevelRobustness`; 4680 jobs, exit 0).
- **2026-11-25, P6b session 2 (WIP, branch `etcd-safe-p6b-wip`).** The swap is in: `Ghost.lean` (v2.1,
  below), `HandleAlloc`, `NamedView`, `OpenWLocked`, `Handle` (`WalHS.inc`, `walHandleIn` holds
  `walOpenWI w dir h.inc`, `walDirH`'s `nmd` has no default), `Crash`/`CrashS` (keep lemmas at
  incarnations: old view at `i`, new generation at `0`; `walCrashWal` carries the new generation's
  `walIncQ ∅` and `walPastI (s', ∅)`), `CreateNamed`/`CreateNamedStep` build. `wal.Link` does not.
  **v2.1 deviations from the approved v2** (to write into `notes/wal-p6b-design.md`):
  * facts are retired-able: `walIncFact I dir i P := (incOf I dir = i ∧ P) ∨ i < incOf I dir`
    (handle records are keyed by `GName`, a stale record of the same `Loc` cannot be excluded, so
    `Sync` with a stale `walLenLb` must yield a (retired) `walSyncedLb`); `walSyncedLb dir i n`,
    `walNamed dir i`, `walLenLb w dir i n` all take `i`;
  * a step lemma that hands out a fact takes a past `walPastI (s0, I0)` and returns the fact at
    `incOf I0 dir` (`walNamed_of_le`, `walSyncedLb_of_le`: current or retired), so no step lemma needs
    the caller's quarter (pattern: `walInvBody_named`/`walInv_named`);
  * the lock's quarter lives inside `walLockedTokI I` (`walLockedTok := ∃ I, …`); `walOpenWI w dir i`
    is the handle with `⌜incOf I dir = i⌝`; `walHandleInc` dropped (`WalHS.inc` instead); the view's
    share is the quarter `walIncQ`; `walDirKey` by `(dir, i)` deferred until a re-`Create` needs it.
  **Later in session 2**: `CreateAu` (builds), `CreateAuFresh` (builds), `HandleAlloc` (+ `walHandlePI`,
  `walHandleP_inc`, `walHandleP_mintI`, `walHandlePI_openWI`, builds); `CreateRename`/`CreateHandle`
  threaded with the incarnation `ic` (`createU … nm ic …`, `createUH … nm ic …` with
  `walPastI (s', I) ∗ ⌜incOf I (child r nm) = ic ∧ …⌝`), not yet built because `HandleUnnamed` (their
  import) fails at `walOpenWFU_seal`: **the client handle must carry the incarnation**. Plan: add
  `walOpenWFI P Mr w dir i := ∃ h, walHandleIn … h … ∗ ⌜h.inc = i⌝ ∗ …` (and `walOpenWFUI`), laws to the
  old `walOpenWF` (`∃ i`); `walOpenWFU_seal` takes `walNamed dir i` and gives `walOpenWFI … i`; for the
  shared handle, add `inc : Nat` to `WalShN` (so `walOpenWS … γ q` carries `γ.inc`, and `Save`'s AU is over
  `walDiskAtI dir γ.inc d`, its post `walLenLb w dir γ.inc …`/`walSyncedLb dir γ.inc …`: minimal spec
  churn). `walPurgeW_fresh_lbs` is ported (from `walPastI (s, I)`, facts at `incOf I dir`); the four
  `_unlocked_excl` lemmas too. **Open design point**: `CreateSplit.lean:284` (`walInv_register`) and
  similar lemmas use a past `walPast s0` with the WAL present to conclude it is present now; with
  incarnations that needs currency (the caller's lock quarter: pass `walLockedTokI I0`/`walIncQ I0` and agree
  with the ghost by `walGhost_inc`/`walGhostI_lockedI_agree`, then `walLeI`'s fourth conjunct at equal
  incarnations gives the WAL). Same pattern expected in `CreateSteps`, `ReadAllNamed`, `TailLenLb`.
  **Next**: `walOpenWFI`, `HandleUnnamed`, `CreateSplit`, `Create.lean` + `Spec/.../wal/Create.lean`
  (`∀ i` in the spec, AU over `walDirIsI dir i`, post `walOpenWFI … i ∗ walNamed dir i ∗ walLenLb w dir i 0 ∗
  walSyncedLb dir i 0`; ledger entry in `notes/specs-only/ledger.md` before the spec edit), then rebuild
  `wal.Link`.
  The `CreateAu` plan as carried out: `walCreateP` gets `i`, its AU over `walDirIsI dir i o`,
  committing `walDiskAtI dir i (walDurFresh md)`; at the commit, `walGhost_inc` with the view's quarter
  `Iv`, `walGhostI_upd`, the lock (from `walParked_lock`) agreed to `Iv` (`walIncQ_agree`), and
  `walCreateQ`'s `some` arm gives `walLockedTokI I ∗ ⌜incOf I dir = i⌝ ∗ walPastI (s', I)`; then a
  `walHandleP_mintI` from `walLockedTokI I` at `incOf I dir`. Specs take `i` as a spec parameter
  (`∀ i`, AU over `walDiskAtI dir i …`), the handle `WalHS.inc = i`. Then rebuild `wal.Link` for the
  next wave (`HandleUnnamed`, `Append`, `TailSync`, `CutAuLemmas`, `ReadAll*`, ...).
- **2026-11-25, P6b sessions 3-4 (WIP, `etcd-safe-p6b-wip`).** Session 3 (`c99735b77c`): `walOpenWFI`/
  `walOpenWFUI` (Handle), `HandleUnnamed`, `CreateSplit` (lock quarter), `CreateHandle`, `Create` spec at `i`,
  `renameWALPost` arm 2 dropped (ledger: for the coordinator to confirm), `TailLenLb`, `CutAu`/`CutAuLemmas`,
  `TailSync`, `Append`, `HandleAppend` at incarnations. Session 4:
  * **the sync's incarnation, without the lock quarter**: `walIncLb dir i` (Ghost: `⌜i = 0⌝ ∨` a past
    state whose incarnation is `≥ i`; persistent). Every ghost handle carries it (`walHandleDirI` now
    `γ ↪ (w, dir, i) ∗ walIncLb dir i`; `walHandle_alloc`/`walHandleP_mint(I)`/`walOpening_mint` take it,
    minted by `walGhost_lockedI_incLb`); `walOpenWI_incLb`/`walOpenWCI_incLb` read it off a handle;
    `walIncLb_ghost` bounds it by the ghost. `walInvBody_sync`/`_syncP` take `walIncLb dir i` and return
    `walSyncedLb dir i |H|` (`walSyncedLb_intro_le`); `_syncPE` keeps `walPast` (its fact is dropped).
    Threaded through `wp_tailFsync`, `FdatasyncPend`, `TailFdatasync`, `TailFdatasyncNE` (`ic` parameter,
    `walIncLb dir ic` premise) and `ReadAllTailCallees.specWalPend`; `WAL.sync.specLent` passes
    `walIncLb_zero`.
  * **shared handle**: `WalShN.inc`; `walHdl … i`, `walOpenWFR … k i`, `walOpenWS_alloc` returns
    `⌜γ.inc = i⌝`; `walOpenWFI_iff`. Checked: `HandleRoom`, `HandleShared`, `Ghost`, `HandleAlloc`.
  * **specs** (ledger addendum 2026-11-25 session 4): `Save`, `SaveSnapshot`, `Sync`, `ReleaseLockTo`,
    `Close`, `storage__*` at `γ.inc`; `ReadAll`, `Create.specFresh` and the read-only updates (`Open`,
    `openAtIndex`, `openLast`, `OpenForRead`, `Exist`, `Repair`, `ValidSnapshotEntries`, `Unsaved`) take
    `∀ i`/`ic`; internal sync specs post `walSyncedLb dir h.inc …`.
  * **proofs edited, not yet checked**: `WAL__sync`, `WAL__syncNoErr`, `WAL__cut`, `WAL__syncLent`,
    `OpenAtPin`, `OpenAtSteps`, `CreateHandle` (mint), `ReadAllOpen`, `PurgeLend`, `CloseHandle`
    (`walHandleC` at `h.inc`; `WalCloseLaw` at `i`), `CloseLaw`, `CloseLawU`.
  * **left** (in order): check the above; the read-only-AU proofs (`unfold walDirIsI`, carry `I`);
    `ReadAll` (commit: agree the opening handle's lock quarter with the view's `walIncQ` to get
    `h.inc = i`; `ReadAllNamed.walInv_namedBy` returns `walNamed dir` with no `i`: give it the handle's
    `walIncLb` or a past); `Create.lean`'s proof (handoff's session-3 list); the method proofs over
    `walOpenWS` (`walOpenWS_acquire` now yields `walHdl … γ.inc`); `CreateSrv`; the tester; P8's
    consumers; `DiscardUnsaved`. Then merge `etcd-safe-main-pin/2026-11-24` @ `3717c7903b` (coordinator,
    2026-11-25: at the next building state pushed to `etcd-safe-p6b`).
- **2026-11-25, P6b session 5 (WIP, `etcd-safe-p6b-wip`).** Checked (lean-check, 0 errors): the sync
  chain (`TailFsync`, `FdatasyncPend`, `TailSyncPendE`, `TailFdatasync(NE)`, `WAL__sync`, `WAL__syncNoErr`,
  `WAL__cut`, `CalleeCov`), `CloseLaw`, `CloseLawU`, `WAL__CloseU`, the read-only pins (`ExistPin`,
  `RepairPin`, `VsePin`, `OpenAtPin`, `ReleaseAu`, `ReleaseTie`) and their callers (`Exist`, `openLast`,
  `openAtIndex`, `ValidSnapshotEntries`, `Unsaved`, `Open`, `OpenForRead`), `WAL__ReleaseLockTo`,
  `WAL__CloseOpening`, `PurgeLend`, `ReadAllOpen`, `HandleLaws`, `HandleAppend`. New:
  * **the read handle at its incarnation** (ledger 2026-11-25, "session 5", decision needed):
    `walOpening w dir s i` (= `walHandlePI … i (.opening s)`), `walOpeningF … i`; `Open` posts
    `walOpeningF … ic` (`walPinOut … ic`: `walInvBody_pinOut` takes the view's `walIncQ` and agrees it with
    the lock it hands out, `walLockedTokI_incQ_agree`); `ReadAll` pre `walOpeningF … i`; `Close`'s
    `opening` arm `∃ i`. `walHandlePI_set`; `walOpening_incLb`; `walInvBody_pastAt` (a past at the view's
    incarnation); `walOpening_ghost_inc`/`walOpening_pastCur` (Ghost: **currency**, a past state at the
    handle's incarnation is below the ghost's at `dir`, by the lock), used by `ReadAllSynced.walInv_tailH`
    and `ReadAllNamed.walInv_namedBy` (both now take `walPastI (s1, I1)`, `incOf I1 dir = ic` and the
    handle); `walInv_readCommitReg` also returns that past. `walNamed_intro_le`.
  * methods over `walOpenWS`: `walHdl_open … γ.inc` gives `h.inc = γ.inc`; `walHandleIn_lenLb` and
    `walHandleIn_append` take `(i) (hi : h.inc = i)`; `SaveSt`/`SaveFin` carry `inc`; `cut`'s post adds
    `h'.inc = h.inc`; `save_post` at `γ.inc`. Edited, being checked: `WAL__Save`, `WAL__SaveSnapshot`,
    `WAL__Sync`, `WAL__Close`, `WAL__ReadAll`, `ReadAll{Exit,Synced,Named,RegCommit}`.
  * **checked since** (lean-check `-a`, 0 errors): `WAL__Save`, `WAL__SaveSnapshot`, `WAL__Sync`, `WAL__Close`,
    `WAL__CloseFailed`, `WAL__syncLent`, `Repair`, `WAL__ReadAll`, `ReadAllFail`, `HandleUnnamed` (new:
    `walOpenWFUI_lockAcc`, `walOpenWFU_sealL`, `walOpenWFI_unlocked_exclX`). Pushed as `45979e5b19`+.
  * **`Create.lean`** (`--fast`): everything but the deferred cleanup's registration. Done: `ic` binder,
    `walCreateP`/`createU`/`createUH`/`create_ghost`/`create_handleIn`/`createHS` at `ic`, `renameWALPost`'s
    arm 2 removed, the success exit registers under the handle's lock (`walOpenWFU_sealL`, `walInv_register
    … s' I0 Il`, `walInv_named … I0`), arm 3 (committed error) registers under `walCreateQ`'s `walLockedTokI`.
    **Open (12 errors, one cause)**: `create_cleanup`'s two `walInv_register` calls (the cleanup's `Close`
    failed, `Hlt : walLockedTok`; or succeeded, `walUnlockedTokX`): the token comes back from
    `WAL.cleanupWAL.spec`/`WAL.Close.spec`'s `unnamed` arm without its incarnation, so "the WAL is still
    present" (`walInv_register`'s currency) cannot be shown. Proposed: (a) `walInv_register` takes the
    quarter `walIncQ I'` (it only agrees it with the ghost) instead of `walLockedTokI I'`; (b) `Close.spec`'s
    `unnamed` arm takes `walOpenWFUI … i` and returns the quarter at `i` (`walLockedTokI I ∗ ⌜incOf I dir = i⌝`,
    and the unlocked token's `walIncAny` as `walIncQ I` with the same fact); (c) `cleanupWAL.spec` likewise.
    Ledger entry first (internal specs; "still present" lemmas take the lock quarter, as approved).
  * **left**: the above; `WAL__CloseFailed`/`WAL__syncLent`/`Repair` (failed only on stale
    dependencies so far); `Create.lean` (handoff's session-3 list); `CreateSrv`; `storage__*`; then a
    `lake build` of `wal.Link`; WalTester (20 files use the facts), P8's consumers (`WalViews`' crash laws
    `walDiskAt_crash*` take facts without incarnation: they need `walDiskAtI`/facts at `i` and the
    crash's incarnation map), `DiscardUnsaved`; then the merge of `3717c7903b`.
- **2026-11-25, P6b session 6 (WIP, `etcd-safe-p6b-wip`).** Coordinator approvals recorded in the ledger (the
  Create cleanup fix (a)-(c); `renameWAL`'s arm 2, proved from its body; the session-4/5 spec changes, `walIncLb`,
  the read handle at its incarnation). **Create done**: `walInv_register` takes the quarter `walIncQ I'`
  (`walInv_registerL` with the lock); `WalCloseSt.unnamed … i`, `Close.spec`'s `unnamed` arm over `walOpenWFUI … i`
  returning `∃ I, walUnlockedTokXI I ∗ ⌜incOf I dir = i⌝` / `∃ I, walLockedTokI I ∗ …`; `cleanupWAL.spec` likewise;
  `sync.specC`'s error arm at `h.inc`. New Ghost lemmas: `walUnlockedTokXI` (+ `_X`, `_incQ`), `walLockedTokI_incQ`,
  `walLockedTokI_unlockXI`, `walOpenWI_lockedTokI`; `walParked_unlockXI`, `walInvBody_unpinXI` (the old `unpinX` a
  corollary); `walCloseLawU` takes `walOpenWI … i`. **`wal.Link` builds** (real `lake build`, 3842 jobs, exit 0, no
  `sorry` outside the generated axiomatized types): commit `a283427990`.
  **Server/P8 consumers**: `WalRecs` at the handle's `h.γ.inc` (`walRecs`, `walSnapRec`, `walOpen`'s `walLenLb … 0`,
  the AU laws over `walDiskAtI h.dir h.γ.inc`); `walFiles`/`walFilesC` `∃ i`; `walFilesC_crash` takes `i` (new
  generation at `0`). **Tester**: incarnation `0` throughout (a tester never discards; a crash's new generation is at
  `0`): `TInvBody` over `walDirIsI … 0`, `tRelI`/`tRelW` facts at `0`, its specs (`member__{save,sync,close}`,
  `restartRead`) over `walOpenWFI … 0`, `purgeRound` at any `i`; `Boot` passes `0` to `Create.specFresh`.
  Also: `walStart_boot0`/`walBoot0`/`walBoot0s` hand out the first generation's `walIncQ ∅` (the view's quarter,
  for `walAbsent`/`walDirIsI … 0` at boot; `WalAreas`, the tester's `Boot0`); `walPurgeAcc dir inc Pc` over
  `walDiskAtI dir inc` (ledger); the shared handle (`walOpenWS_alloc … i`, `⌜γ.inc = i⌝`) substituted to `0` in the
  tester (`rcases γs …; subst; let γs := ⟨_, _, 0⟩`).
  **Merged `etcd-safe-main-r3/2026-11-25` @ `5a1c41d945`** (after P8's head `36457e1448`; conflicts resolved by
  a three-way merge on `36457e1448`, which both sides contain; manifest unchanged): P8's `WalRecsH`/`InvWalCrash`
  at `h.γ.inc`; `bootFs.walAbsent_au` at an incarnation (`BootFsLaws`). Built: the WAL cone, the tester's
  Link/Adequacy/TopLevelRobustness, the server's consumers and P8's crash modules (5549 jobs), then every leaf the
  change reaches against r3 (`etc/importers.py --git 5a1c41d945 --leaves`, 57 targets, ~14,000 jobs).
  **Left: `wal.DiscardUnsaved`** (not started; multi-session). What it needs (from reading `Inv.lean`): a WAL
  directory renamed `nm` → `nm.tmp` while its layout stays in `Ls` (`WalsAt`, `DirClaimsOk`, the area's
  `AbsentNone`/`DirsOk` all tie `Ls dir` to the entry `nm`): a "discarding" state with `named := false` (the
  rename not durable: a crash may keep either name), then `syncDir(parent)` commits the removal (`s.wal` drops
  `dir`, `incOf` bumped, `walLeI_discard`) and the directory at `nm.tmp` becomes leftover that `Create`'s
  `RemoveAll(dir.tmp)` removes (its segments' resources move to the tmp-parked part, `walTmpParked`). The spec:
  `Unsaved`'s pre plus the parent's resources (as `Create`'s), `walUnlockedTok`, and an update
  `<{∃∃ d, walDiskAtI dir ic d}> <{walAbsentI dir (ic+1), COMM Qd}>` committed only on `true`.
- **2026-11-25, P6b session 7: the `DiscardUnsaved` plan (no Lean yet).** Reading the invariant against the Go
  (`DiscardUnsaved`, fork `e94f33b50` `unsaved.go:97`: `lg` nil check; `Unsaved` (error or `false` → `false, nil`);
  `dir := Clean(dirpath)`; `os.RemoveAll(dir.tmp)`; `os.Rename(dir, dir.tmp)`; `syncDir(Dir(dir))`; each error →
  `false, err`; `true, nil`) found **three obstacles the session-6 sketch missed**, each a prerequisite:
  1. **The WAL's name claim cannot be made whole (the path loans leak).** The rename (`os.Rename.specDirS`/
     `specDirAnySnc`) needs one *whole* claim holding `nm` and `nm.tmp`. A registered WAL's `nm` is its own claim
     `(jr, .only [nm], hn)`: the invariant's half in `cl`, the program's half in `nameShare` (`walNamesRes`), from
     which `walInvBody_dirPath` lends fractions that are **never returned** (it even drops part: `⟨Hne, -⟩`,
     `NameClaims.lean`); `Unsaved` itself borrows one (`Unsaved.lean:176`) and drops it. So after `Unsaved` no proof
     can merge `nm` back into the area claim. **Fix (A, loans)**: the γnm ghost variable's value becomes
     `NmSt := ⟨reg : Option GoString, disc : Option GoString, loans : List (GoString × Qp)⟩` (Ghost.lean;
     `walNamesFrag o := walNamesFragS ⟨o, none, []⟩`, `walNamesAuth` likewise, so the specs naming `walNamesFrag`
     — `WAL__Close`, `WAL__cleanupWAL`, `WAL__syncC` — are unchanged); `walNamesRes` keeps
     `nameShare jr Ls nm q` with `q + Σ (loans of nm) = ½` (exact); `walInv(Body)_dirPath` takes
     `walNamesFragS ⟨none, none, L⟩` and returns it with `(nm, e) :: L`; a new `walInv_dirPathRet` takes the path
     `osPathS R dir (own e) j` back (decomposed by `osPathS_child`'s inverse: the area spine's fraction and the
     name claim's) and erases the loan. Every function that returns `walUnlockedTok` (or a handle that later does,
     `Close`) returns its loans first: call sites of `walInv_dirPath` — `openLast`, `openAtIndex`, `Open` (the
     handle keeps its loan in `walNamesFragS`, `Close` returns it), `ValidSnapshotEntries`, `Unsaved`,
     `WAL__ReadAll` (2), `WAL__CloseFailed` (3: `walCloseLeft` carries its loan; check `Repair.specHeld`, which takes
     `walCloseLeft` and returns the lock); arms that lose the lock token may drop loans. Users of `walNamesRes`'s
     fields: 29 files (most only frame it). Boot (`Crash.lean` ~1043, `walInv_alloc`): `⟨none, none, []⟩`, every
     `nameShare` at `½`.
  2. **The client's view cannot stay named across the rename (one AU is not enough).** Between the rename and the
     parent's fsync a crash may keep `dir` or lose it, so the real WAL must be **unnamed** there (`walCrash`), and
     `walNamed dir ic` must be retired (`walDiskAt_crash_keep` would be false), so the incarnation is bumped at the
     rename (`walLeI` keeps `named` at an unchanged incarnation). Bumping needs the view's quarter (`walIncQ`, inside
     the client's `walDiskAtI`), and `walMapLe M s.wal` needs the view unnamed too: the view must change at the
     rename, and again at the fsync (absent; a second bump, since `walLeI` keeps a present WAL at an unchanged
     incarnation and facts minted at `ic+1` in the window must not bind a re-created WAL). An AU commits once and
     its abort returns the same `α x`, so **the spec takes two AUs** (ledger entry 2026-11-25, "DiscardUnsaved"):
     `AU₁ <{∃∃ o, walDirIsI dir ic o}> <{∃ d, ⌜o = some d ∧ walBlank (d.H.map WalOpG.toM)⌝ ∗
     walDiskAtI dir (ic+1) {d with named := false}, COMM Q₁ o}>` (at the rename's commit) and
     `AU₂ <{∃∃ d, walDiskAtI dir (ic+1) d}> <{walAbsentI dir (ic+2), COMM Q₂}>` (at the parent's fsync). Pre as
     `Unsaved`'s (with `zapLoggerOk lg`, `walAreaOk`, `osPathS R r qp jr`, `walAreaRes jr`, `osCallPerm 1`,
     `walUnlockedTok`) plus `Create`'s premise `FsNoErrOn (p = dir ∨ p = dir.tmp ∨ p = r) ∧ PathFits dir.tmp ∧
     PathFits dir`, `dir.length < 2^59` (so `RemoveAll`/`Rename` cannot fail; `syncDir` can). Post, always
     `osPathS R r qp jr ∗ osCallPerm (callKey R r) 1` and: `b = false ∧ err = nil` with `walAreaRes jr ∗
     walUnlockedTok ∗ AU₁ ∗ AU₂` back; or `b = true ∧ err = nil` with `walAreaRes jr ∗ walUnlockedTok ∗ ∃ o, Q₁ o ∗
     Q₂`; or `b = false ∧ err ≠ nil` (the fsync failed) with `∃ o, Q₁ o ∗ AU₂` (the lock token and `walAreaRes` lost:
     the WAL is left unnamed at `nm.tmp`, unregistered, as `Create`'s failed arm 3 leaves its WAL).
  3. **`walDirKey` must be keyed by the incarnation now** (design v2.1 item 5, deferred until a re-`Create`): after
     the fsync the WAL's layout leaves `Ls`, so `DirKeysOk`'s clause for a persistent `dir ↦ (j, X)` fails, and
     `bootstrap`'s re-`Create` cannot insert its new `(j', X)`. **Fix (B)**: `γdk : GMap (GoString × Nat) (Ino ×
     List GoString)`, `walDirKey dir i j X`; `DirKeysOk` speaks of the current incarnation only (`walInvBody` exposes
     `walGhostI s I`'s `I`, or `DirKeysOk` takes it); lookups take the holder's incarnation (handles: `h.inc`, current
     by their lock quarter; pins: the lock token's `walIncAny`). 189 occurrences in 55 files; internal specs naming
     it: `WAL__renameWAL`, `newFilePipeline`, `WAL__syncIdle(F)` (ledger entry with B).
  **The discarding state (C)**, reusing `Create`'s failed-cleanup state (an unnamed WAL whose layout stays in `Ls`,
  its directory moved off `nm`: `WalsAt`'s `none` disjunct, `CrashTo`'s left disjunct) with `NmSt.disc = some dir`
  in place of `reg` (so `Create`'s cleanup keeps "the pending registration's WAL is unnamed": the clause becomes
  `disc = some dir → named = false ∨ the area's claim still holds the directory at nm`, the second only before the
  rename). Steps, all under `walUnlockedTok` (no handle, everything parked, `CR` empty, no cut):
  * **U (unregister, ghost, after `RemoveAll(dir.tmp)`)**: loans `[]` ⇒ `nameShare` at `½`; take the invariant's
    half of `(jr, .only [nm], hn)` from `cl` and of the area claim `(jr, N, h)`; with `walAreaRes`'s half,
    `osNames_merge` (`osSharedInv`, `osShN`) into `(jr, N ∪ {nm}, h')`, halves back (one claim replaces two in `cl`:
    `ClaimOnce`, `WalsCreateOk`, `WalsAt`, `AbsentNone`, `CreatingOk` (vacuous, `CR = ∅`)); `Wn' = Wn.erase nm`
    (both `walSplit` halves); `disc := some dir`.
  * **R (the rename's commit, inside `os.Rename.specDirSnc`'s `osAUnc`)**: real `s` → `nm` unnamed, `I` bumped
    (`walLeI_unname`, new: as `walLeI_discard` without the deletion); AU₁ committed (`walOwn M` →
    `M[dir := unnamed]`, all three quarters of `I`); invariant as `CleanupAu`'s rename (to `nm.tmp` in place of
    `nm.broken.*`; `nm.tmp` is an `AreaSlot`, `DirsAvoid` unchanged).
  * **S (the parent's fsync's commit lb, ghost)**: `osCommitLb n` raised past the rename (as `CreateNamedStep`);
    real `s` → `dir` deleted, `I` bumped (`walLeI_discard`); AU₂ committed (`M.delete dir`); `Ls.delete dir`;
    out of the invariant, whole: the directory claim `(lay.j, .except walTmps, hj)` (both halves: `cl` and
    `walParked`), `walTmpsRes lay.j` + `walTmpsHalf lay.j` (`walTmpParked`'s `Jt`/`Jh` lose `dir`); merged
    (`osNames_merge`, twice) into `(lay.j, .except [], hj')` and tagged `tmpName nm` in `walAreaRes`'s `cl`
    (`SubCover`: every entry of a WAL directory is a file — `SegsNamed`, `tmpEnt`, `walOthersL`; no other claim of
    `lay.j` among the program's, by `osNames_disj`; `ClRanked`: `lay.j` ranked above the rest). Segment files'
    halves dropped. `AbsentNone`/`AbsentOk` for `dir` from the raised commit lb. `disc := none`; `walUnlockedTok`
    rebuilt.
  **Order of work** (each step lean-checked, then a `lake build` of `wal.Link` at A, at B, at C):
  A (loans) → B (keys by incarnation) → C's ghost lemmas (`walLeI_unname`, `walGhost` steps U/R/S as
  `Inv`-level lemmas in a new `DiscardSteps.lean`) → the spec (`Spec/.../wal/DiscardUnsaved.lean`, after the ledger
  entry is accepted) → the proof (`Proof/.../wal/DiscardUnsaved.lean`: `Unsaved` with a peek AU from AU₁,
  `os.RemoveAll.specSubS` as `Create`'s, U, `os.Rename.specDirSnc` with R, `syncDir.spec`, S) → `etc/gen-link.py
  --walfs` → builds (wal.Link, tester, server consumers, P8 crash modules, then `etc/importers.py --git 5a1c41d945
  --leaves`). Estimate: A 400-800 lines, B 300-600, C 600-1000, spec+proof 300-500: three to five sessions.
- **2026-11-25, P6b session 8 (WIP, `etcd-safe-p6b-wip`): fix A's core; its borrowers left.** Ledger entry
  "wal.DiscardUnsaved" marked approved (coordinator brief; P5 asked about the two-update shape).
  **Done, each lean-checked with 0 errors** (Ghost, Inv, NameClaims, NameSplit, Crash, CreateAu, CreateSplit,
  AreaPath; no `lake build` yet, `wal.Link` does not build):
  * `Ghost.lean`: `structure NmSt := ⟨reg, disc, loans : List (GoString × Qp)⟩` (countable); `walNamesFragS`/
    `walNamesAuthS st` the ghost variable's halves; `walNamesFrag o`/`walNamesAuth o` are now **abbrevs** of
    `…S ⟨o, none, []⟩` (so every existing use is unchanged); `walNamesS_agree`/`walNamesS_set`; `loanSum Lo nm : Rat`.
  * `Inv.lean`: `shareLs Wn Lo k nm := if Wn.idxOf nm = k then loanSum Lo nm else 0` — **the loans of a name count
    at its first index in `Wn`** (decision: this avoids a `Wn.Nodup` invariant, whose upkeep at boot and
    registration would need the claims' disjointness); lemmas `loanSum_{nil,cons_eq,cons_ne,perm}`,
    `shareLs_{nil,perm,cons_ne,cons_eq,reg_tail,reg_head}`, `idxOf_getElem?`. `nameShare jr Ls nm ls` is exact:
    `q.val + ls = ((1:Qp).half).val`. `walNamesRes` is over `st : NmSt` with a new pure conjunct
    `⌜st.disc = none ∧ ∀ x ∈ st.loans, x.1 ∈ Wn⌝` (after `hun`: destructs become `⟨%o, %Wn, Ha, Hs, %hf, %hun,
    %hst, Hsp, Hl⟩`), the shares `[∗list] k ↦ nm ∈ Wn, nameShare jr Ls nm (shareLs Wn st.loans k nm)`;
    `walNamesRes_noneL` (any loans; `walNamesRes_none` its `[]` case). Update a share with
    `BigSepL.bigSepL_lookup_acc_impl` (used as `icases BigSepL.bigSepL_lookup_acc_impl hi $$ Hl with ⟨Hn, Hl⟩`,
    then `iapply Hl $$ [] [Hn]` with the `shareLs_cons_ne` side condition).
  * `NameClaims.lean`: `walInvBody_dirPath`/`walInv_dirPath … Lo`: input `walNamesFragS ⟨none, none, Lo⟩`, output
    `∃ nm q, ⌜dir = child r nm⌝ ∗ walNamesFragS ⟨none, none, (nm, q) :: Lo⟩ ∗ osPathS R dir (own q) j` (the share
    keeps `q.half + a`, lends `e`); `walInvBody_dirPathRet`/`walInv_dirPathRet … (hx : (nm, q) ∈ Lo)`: the path
    `osPathS R (child r nm) (own q) j` back (unchilded through the invariant's area spine), frag `Lo.erase (nm, q)`;
    `walInv_dirPathRet0` (`[(nm, q)]` → `walNamesFrag none`). Local copies `nc_osSpine_unsnoc`/`nc_osPathS_unchild`
    (`os.osPathS_unchild` drags `go.Semantics`/`os.Assumptions`/`FieldAssumptions` in as section instances).
  * `NameSplit.lean`: `walNamesRes_lendAt … Lo` is now `==∗` and records `(nm, q1)`; `walNamesRes_returnName`
    returns an `osNames jr (.only [nm]) (own q) hn'` fraction (`(nm, q) ∈ Lo`). The area spine fraction lent
    beside it is not counted (the discard gets its parent's spine from its caller).
  * `CreateSplit.lean`: `walInvBody_register`/`walInv_register`/`walInv_registerL` take `Lo` with
    `hLo : q.val + loanSum Lo nm = ½` and `hLn : ∀ x ∈ Lo, x.1 = nm` and return `walNamesFragS ⟨none, none, Lo⟩`
    (was `walNamesFrag none`): the registrant's own fractions of the name's program half (beyond the `q` given)
    become its loans. `Crash.lean`: `names_split_start` at `nameShare … 0` (shares at ½), `walInv_alloc` at
    `⟨none, none, []⟩`. `CreateAu.lean`: the new destruct.
  **Next (in order; scope found this session):**
  1. **Holders' bundle** (recommended, in `NameClaims`/`NameSplit`): `walLoanP R jr r x := (∃ j, osPathS R
     (child r x.1) (own x.2) j) ∨ (∃ hn, osNames jr (.only [x.1]) (own x.2) hn)` and `walInv_returnAll :
     walNamesFragS ⟨none, none, Lh⟩ ∗ [∗list] x ∈ Lh, walLoanP R jr r x ={⊤}=∗ walNamesFrag none` (induction on
     `Lh`, head by `walInvBody_dirPathRet`/`walNamesRes_returnName`; at `walInv` level with `notCrashed`), so each
     borrower keeps `[∗list] walLoanP` beside its frag and returns all at its exit.
  2. **The pins** (`walNamesFrag none` out of `walParked_lock`): `ExistPin` (`existPin`'s output frag
     `⟨none, none, [(nm, q1)]⟩`; `existUnpin`/`walInv_existEnd` take it with `Hn1` back; `Exist.lean` keeps `Hn1`
     past `ReadDir`), `ReadAllCommit:91` and `ReadAllRegCommit:250` (`walInvBody_nameClaim`: the lendAt pattern;
     `ReadAllNamed` keeps the claim), `Unsaved` (`unsaved_putback` returns the path first), `ValidSnapshotEntries`,
     `openLast`, `openAtIndex`, `WAL__ReadAll` (2), `WAL__CloseFailed` (3; `walCloseLeft` carries its loan,
     `Repair.specHeld` returns it).
  3. **The handles** (the larger part): `Open`'s handle keeps its directory path (`walOpeningF`: `iexists f, fd, j,
     X` frames `Hpd`), `Create`'s keeps two pinned paths of fraction `d` and a claim `c.half`/`b1 + b1` (see
     `create_qp_twice`: `d + (d + (b1 + b1)) = ½`; register calls at `Create.lean` 180, 221, 439, 1381 must pass
     `Lo` = those kept fractions). So the handle's frag (`walReadH`'s `walNamesFrag none`, `ReadDefs` 121/243;
     `Handle.lean:620` `walNamesFrag nf`; `HandleUnnamed` 64/92/116/139; `OpenAtSteps`/`OpenAtPin`/`OpenLastDefs`;
     `CloseHandle:127`; `Parked` 272/292) becomes `walNamesFragS ⟨nf, none, Lh⟩` with `[∗list] x ∈ Lh, walLoanP`
     held in the handle (the paths it uses are those loans: keep them inside `walLoanP`'s left disjunct, or keep the
     path in the handle and the loan's record beside it), and `Close`/`CloseHandle` returns them before
     `walLockedTok_unlock`. `walNamesRes_noneL` serves the naming steps with the handle's loans.
  Then `lake build` of `wal.Link`, push WIP, and B, C, the spec, the proof as session 7's plan.

- **2026-11-25, P6b session 9 (WIP, `etcd-safe-p6b-wip`): fix A continued; the handles left.** Started from
  `09932cd216`; a `lake build` of `wal.Link` there failed in ExistPin, ReadAllCommit, ValidSnapshotEntries,
  openLast, Unsaved, openAtIndex, Open, Create (and what imports them). **Done, each lean-checked with 0 errors
  (`-a`)**:
  * New `NameLoans.lean` (imports NameClaims, NameSplit): `walLoanP R jr r x` (a path to `r/x.1` of fraction
    `x.2`, or the claim's fraction); `walInvBody_returnName`/`walInv_returnLoan`/`walInv_returnAll` (every loan
    back, `walNamesFrag none`); `walInv_dirPathRetD` (`[(nm, q)]`, the path to `dir` with `dir = child r nm` as
    `walInv_dirPath` gives it) and `walInv_dirPathRetDL` (any further loans). `NameSplit`:
    `walNamesRes_returnName0`. The pins' files now import NameLoans in place of NameClaims.
  * **Pins done**: `ExistPin` (`existPin`/`existStart` hand out `walNamesFragS ⟨none, none, [(nm, q1)]⟩`;
    `existUnpin`/`existEnd` take it with the claim `osNames jr (.only [nm]) (own q1) hn` and return it first),
    `Exist` (keeps the claim `ReadDir` returns), `Unsaved` (macro `unsaved_putbackP`, used after the lend and by
    `unsaved_close`), `ValidSnapshotEntries`. The destruct of `walInv_dirPath` is now
    `⟨Hnc, %nmd, %qd, %hdn, Hnf, Hpd⟩` (with `Lo` passed, `[]` from a pin).
  * `walInvBody_nameClaim` re-proved over `walNamesRes_lendAt` (any `Lo`, records `(nm, q)`; the area spine
    fraction dropped); `walInv_readCommit`/`walInv_readCommitReg` take `{Lo}` and return
    `walNamesFragS ⟨none, none, (nm, q) :: Lo⟩` **inside** their `∃ … nm q hn` (beside the claim).
    `walInvBody_named`/`walInv_named` (Create) and `walInvBody_namedBy`/`walInv_namedBy` (ReadAll) take an
    implicit `{Lo}` (frag `⟨none, none, Lo⟩` in and out), so `Create` can name after registering with loans.
  **Not building yet** (in order): `openLast` (its success arm hands `walLastOpen` the path: give `walLastOpen`
  the area root `r` and `∃ nm, ⌜dir = child r nm⌝ ∗ walNamesFragS ⟨none, none, [(nm, qd)]⟩` in place of
  `walNamesFrag none`; its users `Repair`, `RepairPre`, `RepairReg`, `RepairBroken`, spec `openLast.lean` must
  return it (`walInv_dirPathRetD`) before the lock, or hand it to `walCloseLeft`; its two failure arms return it
  before `walInv_unpinLast`), `WAL__ReadAll` (line ~380: `walInv_dirPath … []` then `readCommitReg` with that
  loan; the probe path and the name claim returned, `walInv_returnLoan`, after `walInv_namedBy` and before the
  handle is formed, except the path the handle keeps), `openAtIndex` (read mode: return before returning the
  lock; write mode: the path goes to the pipeline, `isFilePipe … dq`, a handle loan), `Open`, `WAL__CloseFailed`,
  `Create` (**its three error-arm registrations done**, lean-checked: `Lo := [(nm, d + d)]`, `hLo` by
  `create_loSum2` from the spine law, the frag dropped with the lock; **left, the success arm** (line ~452,
  `walInv_registerL … c.half`, error at the `create_named_cont` call, 1288): `Lo := [(nm, c.half), (nm, d),
  (nm, d)]`, then `walInv_named` (now any loans) returns `Hnm2`, which goes back by `walInv_returnLoan`, leaving
  the handle `[(nm, d), (nm, d)]`).
  **The handles (decided this session, not started).** A write handle holds two path loans of one name: the
  `walDirH` path (`osPathS R dir (own q) j`, `q` existential inside it) and the pipeline's (`isFilePipe fp γ R dir
  dq j sz`, `dq` existential in `walPipeH`; `filePipeline.Close` gives it back in `pipeLeft`, so `Close` has both).
  Plan: `walHandleIn` binds `qp : Qp`, passes `walPipeH … (fun R dq => pp R dq ∧ dq = DFrac.own qp)` and `qp` to
  `walDirH` (new last parameter); `walDirH` holds `∃ Lh, walNamesFragS ⟨nf, none, Lh⟩` (for `walNamesFrag nf`)
  with `⌜nf = none → ∃ r' nm, dir = child r' nm ∧ NameOk nm ∧ Lh = [(nm, q), (nm, qp)]⌝` and `⌜nf ≠ none → Lh =
  []⌝`; `Close` merges the two paths and returns both (`walInv_dirPathRetDL` twice, `r' = r` by `child_inj`, copy
  from `SnapDirCrash.lean`, against `walDirKey`'s `InArea r dir lay.nm`), before `walLockedTok_unlock`; the
  `walFailH`/`walReadTie` handles likewise (`walFailH`: its pipeline loan only); `HandleUnnamed`'s seal takes the
  loans `Create` registered. About 13 `unfold walDirH` sites, `CloseHandle`'s `WalCloseLaw` (frag in), `WAL__Close`,
  `WAL__CloseU`. These are internal predicates (no trusted text), but `walLastOpen` and `WalCloseLaw` appear in
  internal specs: add a ledger line ("loans carried in the handles", covered by fix A's approval) when editing them.
  **Coordinator, during this session (for step 3, the spec):** the fork will drop `DiscardUnsaved`'s internal
  `Unsaved` re-check (renamed `Discard`, or the same name documented as "the caller checked"); `bootstrap` calls it
  only after `Unsaved` returned `(true, nil)` and the backend was removed. **Specify and prove that version**
  (`RemoveAll(dir.tmp)`, `Rename(dir, dir.tmp)`, `syncDir(parent)`): its pre is what `bootstrap` holds there (the
  WAL unsaved, from `Unsaved`'s post), no `Unsaved` completeness. P5's three conditions on the two updates: (1) a
  crash lemma for the window between them (the unnamed blank WAL at `ic+1` crashes to the same blank WAL or to
  none); (2) on a failed parent fsync, `AU₁`'s result stays with the crash invariant, not the caller; (3) the first
  update commits only after the backend is gone (the caller's order). Pin and commit to come from the coordinator.

- **2026-11-25, P6b session 10 (WIP, `etcd-safe-p6b-wip`): the write handle's loans done; the read handles
  next.** Coordinator approvals (session 10 brief): the session-7 plan, the earlier choices, the session-9 handle
  design, the edits to `walLastOpen`/`WalCloseLaw`; the ledger line "loans carried in the handles" added (fix A's
  entry). Discard's fork change: `251a430ce` (branch `goose-lean-fmt1c-discardfix` on the pin `e94f33b50`,
  local `/shared/tmp/p6/etcd-tornsave`, not pushed): `func Discard(lg, dirpath) error` = `RemoveAll(dir.tmp)`,
  `Rename(dir, dir.tmp)`, `syncDir(parent)`, no `Unsaved` inside; `bootstrap` calls it after its own `Unsaved`
  returned `(true, nil)` and after `removeBackendDurably`. Spec that version (pre: the WAL unsaved, `Unsaved`'s
  post); no pin bump or retranslation until the coordinator says; the body's proof after it.
  **Done, each lean-checked with 0 errors** (`-a`, `--fast` for the long ones; commit `109cb378e7`):
  * `Handle.lean`: `WalHS.qp : Qp := 1` (the pipeline's path fraction; a field, not a binder of `walHandleIn`,
    so its 61 destructs are unchanged: decision of this session, the approved design's `qp` bound once per
    handle); `walHLoans dir nf qs := ∃ Lh, walNamesFragS ⟨nf, none, Lh⟩ ∗ ⌜(nf = none → ∃ r' nm, InArea r' dir nm
    ∧ Lh = qs.map (nm, ·)) ∧ (nf ≠ none → Lh = [])⌝` (`InArea`, not `NameOk`: `walNameOk` excludes `/`, which
    `inArea_root` needs, and does not exclude NUL, which `NameOk` does); `walHLoans_some` (`some d`: it is
    `walNamesFrag (some d)`); `walDirH … cuts qp nmd nf` (new parameter after `cuts`) holds `walHLoans dir nf
    [q, qp]` in place of `walNamesFrag nf` (same position: destruct arities unchanged); `walHandleIn` passes
    `h.qp` and pins the pipeline: `walPipeH fp dir j h.pc (fun R dq => pp R dq ∧ dq = DFrac.own h.qp)`.
  * New `HandleLoans.lean` (imports Handle, NameLoans): `sep_last_inj`, `inArea_root`, `inArea_child`,
    `walInv_dirKeyArea` (a keyed WAL directory is `InArea r dir nm`, through `DirKeysOk`/`WalsOk`),
    `walHLoans_mk` (the record from `qs.map (nm, ·)` loans), `walInv_returnHLoans2` (key + record + both paths →
    `walNamesFrag none`).
  * `HandleUnnamed`: `walDirH_split` now gives `∃ R q, A R q ∗ walHLoans dir nf [q, qp] ∗ (∀ nf', walHLoans … -∗ B R q
    -∗ walDirH … B nf')`; `walHandleIn_split` and `walOpenWFU_seal` deleted (unused); `walOpenWFU_sealL`'s wand takes
    `walHLoans dir none [qp, qp]` (for `walNamesFrag none`), `h.qp = qp` read off the pipeline's pin.
  * `CreateHandle`: `createHS … ic qp` (new last parameter; `create_handleIn` at `q`). `CloseHandle`
    (`walHandleC`'s `walDirH` at `h.qp`), `ReleaseLocks`/`PurgeLend` (`qp` parameter), `SaveHandle`,
    `CutPipe` (`wp_walPipeH_open`/`walPipeH_next` over any `pp`, the open's post gives `pp R dq`), `WAL__cut`
    (`h1.qp = h.qp` in `hh1e`), `WAL__sync`, `WAL__CloseU`: adapted.
  * Spec `WAL__syncC.lean` (internal; ledger line): the error arm gives `∃ qs, walHLoans dir nf qs`.
  * `WAL__Close.lean` (shared arm): keeps the pipeline's path from `pipeLeft` and returns both loans
    (`walInv_returnHLoans2`) before `walCloseLaw`; **not yet checked** (it imports `WAL__CloseFailed`, a borrower).
  **Next, in order:**
  1. **The read handles** (decided, not started): `walReadTie dir write s j qs fs lfs w` (new parameter `qs`
     after `j`) holds `walTailsFrag ∅ ∗ walHLoans dir none qs` for `walNamesFrag none`; `walReadH` binds `qs`
     after `j` and its write branch pins the pipeline, `walPipeH fp dir j 0 (fun _ dq => ∃ qp, dq = DFrac.own qp
     ∧ qs = [qp])`, its read branch `⌜fp = null ∧ qs = []⌝`; `walFailH` binds `qp`, `walPipeH … (fun _ dq => dq =
     DFrac.own qp)`, `walHLoans dir none [qp]`; `walReadH_namesOut` (Open) gives the record out. Sites: walReadTie
     (6 unfolds, 13 files), walReadH (9), walFailH (2), `ReadAllFail`'s own `walNamesFrag none` (5 statements:
     with `walFailH`'s loan), `ReadAllGive` (the write handle from the read one: `walHLoans_mk` with `[qd, qp]`,
     ReadAll's own `walInv_dirPath` loan first, the pipeline's second, `WalHS.mk … ic qp` at `WAL__ReadAll.lean`
     ~1223).
  2. **The borrowers** (each returns or hands over its `walInv_dirPath` loan): `Open` (returns its `OpenDir` path
     right after `OpenDir`, `walInv_dirPathRetDL` with the pipeline's loan behind it in `Lo`, then `Hback`);
     `openAtIndex` (write mode: the path goes to the pipeline, the read tie records `[qp]`; read mode: returned
     before the lock); `openLast` (`walLastOpen` gets `r` and `∃ nm, ⌜dir = child r nm⌝ ∗ walNamesFragS ⟨none,
     none, [(nm, qd)]⟩`; `Repair`, `RepairPre`, `RepairReg`, `RepairBroken`, spec `openLast.lean` return it,
     `walInv_dirPathRetD`, before the lock or hand it to `walCloseLeft`); `WAL__ReadAll` (line ~381); 
     `WAL__CloseFailed` (160, 368, 571: `walFailH`'s pipeline loan and its own probe path, `walInv_returnLoan`/
     `walInv_returnAll`); `Create`'s success arm (line ~1288: `Lo := [(nm, c.half), (nm, d), (nm, d)]`, then
     `walInv_named`, `walInv_returnLoan` of `c.half`, `walHLoans_mk` with `[d, d]` and `InArea r (child r nm)
     nm` into `sealL`'s wand).
  3. `lake build` of `wal.Link` (state at session start: openLast, openAtIndex, Open, WAL__ReadAll,
     WAL__CloseFailed, Create failed, all at the loans), push WIP; then B, C, the Discard spec as session 7's plan.
- **2026-11-25, P6b session 11 (WIP, `etcd-safe-p6b-wip` @ `abf27f427f`): fix A done; `wal.Link` builds.**
  Coordinator approvals (session 11 brief): `WalHS.qp`, `InArea` in the loan record, `sync.specC`'s error arm
  (ledger line marked approved). **Done** (real `lake build Proof.go_etcd_io.etcd.server.v3.storage.wal.Link`,
  3847 jobs, exit 0, no `sorry`):
  * read handles: `walReadTie dir write s j qs …` holds `walHLoans dir none qs`; `walReadH` binds `qs`, its write
    branch pins `walPipeH … (fun _ dq => ∃ qp, dq = own qp ∧ qs = [qp])`, read branch `fp = null ∧ qs = []`;
    `walFailH`/`walFailCommon` bind `qp`, pipeline pinned at `own qp`, `walHLoans dir none [qp]`;
    `walLastOpen` holds `walHLoans dir none [qd]` (the loan of its kept path; no new parameter).
  * new lemmas: `HandleLoans`: `walInv_returnHLoans1`, `walHLoans_nil`, `walHLoans_loans` (with `InArea r dir nm`
    known, the record's loans are of `nm`), `walInv_returnClaimPath` (ReadAll's claim and probe path back);
    `HandleUnnamed`: `walPipeH_pinLoan`; `Open`: `walReadH_namesOut` now gives `walOpenIn` out and the loans' frag.
  * borrowers: `Open` (returns its `OpenDir` path right after `OpenDir`), `openAtIndex` (error arms and read mode
    return; write mode records `[qd]`, the pipeline's), `openLast` (failure arms return; success hands the path and
    its record to `walLastOpen`), `Repair` (returns before both put-backs), `WAL__CloseOpening`/`WAL__CloseFailed`
    (the pipeline's path from `pipeLeft` returned before `walInv_unpin`; `CloseFailed`'s error arms give
    `walCloseLeft` the pipeline's path instead of a fresh `walInv_dirPath`, the record dropped with the lost lock),
    `WAL__ReadAll` (the claim and the probe path returned at each failure exit and after `walInv_namedBy`; the write
    handle gets `[qd, qpp]` and `WalHS.qp := qpp`), `Create`'s success arm (`Lo := [(nm, c.half), (nm, d), (nm, d)]`,
    `create_loSum3`, `walInv_returnLoan` of `c.half` after `walInv_named`, `[d, d]` into `sealL`).
  **B's design (decided this session, not started):** keep `DirKeysOk` and the keys group's binders unchanged;
  change only the authority and the fragment:
  * `γdk : GMap (GoString × Nat) (Ino × List GoString)`; `walDirKey dir i j X := (dir, i) ↪□ (j, X) ∗ ⌜X = walTmps⌝`.
  * `walDirKeysAuth K := ∃ Kall I, ghostMapAuth γdk 1 Kall ∗ [∗map] Kall persistent ∗ walIncQ I ∗
    ⌜∀ dir x, K !! dir = some x ↔ Kall !! (dir, incOf I dir) = some x⌝`: `K` stays the map of the *current* keys,
    so `DirKeysOk` and the 36 keys-group destructs are unchanged.
  * `γI` re-split: `walGhostI` holds a quarter (not the half), the keys authority the fourth quarter;
    `walGhost_init` hands it out inside `walDirKeysAuth ∅`. (Agreement lemmas are fraction-free; nothing updates
    `I` yet, so no update lemma changes; C's discard steps update `I` with all four quarters.)
  * lookup: `walDirKeysAuth K -∗ walDirKey dir i j X -∗ walIncQ I' -∗ ⌜incOf I' dir = i → K !! dir = some (j, X)⌝`;
    insert/get take `walIncQ I'` and give `walDirKey dir (incOf I' dir) j X`. The holder supplies its quarter:
    the lock (`walLockedTokI_incQ`), a handle (`walOpenWI_lockedTokI`), `walOpening`/`walHandlePI` (to add).
  * the 28 lookup sites (`grep walDirKey_lookup`) and the 4 internal specs (`WAL__renameWAL`, `newFilePipeline`,
    `WAL__syncIdle(F)`: `∀ i`, `walDirKey dir i j X`), approved in the ledger entry.
- **2026-11-25, P6b session 11, fix B (subagent): stopped before any Lean edit; B's design has a gap.** B's lookup
  (`walDirKey_lookup … walIncQ I' -∗ ⌜incOf I' dir = i → K !! dir = some (j, X)⌝`) needs, at every lookup, a
  share of `γI` held by the caller. Two callers hold none, and giving them one changes specs beyond "take the
  incarnation":
  1. **The pipeline's goroutine** (`filePipeline.run`/`alloc` → `PipeLemmas.wp_createTmp`/the remove →
     `walTmp_osAUnc` → `walInvBody_tmpAcc`, `TmpAu.lean:72`) holds only `isFilePipe` (persistent: the key),
     `pipeRes` (`osPathS R dir dq j`, a quarter of `osCallPerm`) and `tmpClaim j b`; it runs concurrently with the
     handle, so it cannot borrow the lock's quarter. A share in `pipeRes`/`pipeLeft` (split off the handle's
     quarter, back at `filePipeline.Close`) changes `newFilePipeline` *and* `filePipeline.Close`/`run`/`alloc`
     (they name `pipeRes`/`pipeLeft`): a ledger entry first.
  2. **`WAL.sync.specIdle`/`specIdleF`** (`TailSyncIdle.lean:317`, `TailFsyncIdle`) hold the key,
     `osNames j (.except X) ½`, `walTailsFrag ∅`, `walCutFrag none`, but not the lock's quarter (their callers,
     `Close`, `CloseFailed`, `CloseOpening`, hold it). Adding `walIncQ I ∗ ⌜incOf I dir = i⌝` to their pre and
     post is in the four approved specs, but more than the approved "takes `h.inc`".
  Ways out (a decision, not a subagent's): (a) the specs as above (ledger entry for the pipeline family; the
  sync change recorded); (b) no spec change: the keys authority keeps, for each retired key `(dir, i) ↦ (j, X)`,
  the whole claims `osNames j (.except X)` and `osNames j (.only [b])` (`b ∈ walTmps`), so that a caller's
  fraction of one of them (`osNames_frac`) proves its key current; the authority then needs `L` (it lives in
  `Ghost.lean`, `W` only: move it or parametrize it), and C's discard must move those claims there (all parked
  when the lock is free) and keep them (a later `RemoveAll(dir.tmp)` of that `j` needs them back: check); (c) a
  path-based lookup for the pipeline, from its `osPathS R dir dq j` against `walNamesRes`'s share of `nm`
  (fix A), which needs a "the directory at a registered `nm` is the current layout's `j`" fact. The other ~22
  lookup sites have a holder (lock, `walOpenWI`/`walOpenWCI`, `walOpening`/`walHandlePI`, or a coiter predicate,
  `walBrokenP` etc., that can be given the caller's quarter): B as designed works there.
- **2026-11-25, P6b session 12 (WIP, `etcd-safe-p6b-wip`): fix B half done; `wal.Link` does not build yet.**
  Coordinator's decision: option (a). Ledger entries (newest first, all marked approved/applied and to report):
  "filePipeline … fix B's key lookup needs a share" (approved; amended: the reserve's place), "WAL.renameWAL
  (`RenameWALOk`'s spine law …)" (the law returns `UH x`, arms 1 and 4 hold `UH x`), "openAtIndex …, WAL.Close
  (`.opening`) -- the read handle's key must name its incarnation".
  **The encoding (Ghost.lean, checked).** `γI` split: `walGhostI` ¼, views ¼ (`walIncQ`), lock ¼ (inside
  `walLockedTokI`), keys authority ⅛ (`walIncE`, in `walDirKeysAuth`), pipeline reserve ⅛. The reserve is in
  `walOutAuth o` when `o.T = []` (`walOutOut o` is its holder's side: `walOut_setR` moves it, `walOut_set`
  needs `o.T` unchanged); it leaves with the pipeline names (`walParked_takeTmps0`, write-mode `Open`;
  `walParked_create`, `Create`'s commit) and comes back with them (`walParked_putTmps0`, `T = [dir]`).
  `walDirKey dir i j X` (keyed by `(dir, i)`), `walPipeKey dir j := ∃ I X, walIncE I ∗ walDirKey dir (incOf I
  dir) j X` (in `pipeRes`). Lookups: `walDirKey_lookup{G,,I,L,WC,H}` (any share; the view's quarter; the lock
  token; `walOpenWCI`; `walHandlePI`), `walPipeKey_lookup`, `walPipeKey_ofLocked`, `walHandlePI_incQ`. A
  lookup that only needs `∀ b ∈ X, walNameP b = false` takes no share: `walDirKey_tmps` (`ReadAllGive`).
  **Done (each `etc/lean-check.py -a`, 0 errors):** Ghost, Parked (+ `takeTmps0`/`putTmps0`), ParkedPut,
  BrokenAu*/BrokenLend/CutAuLemmas (`walOut_set … rfl`), CreateKeys, CreateAu (`walCreateQK`; `walCreateQ …
  (some _) = walCreateQK ∗ walIncEAny`), CreateRename (`createUK`, `create_spine` gives `walPipeKey`),
  CreateHandle (`create_ghost` from `createUK`), TmpAu, PipeLemmas (`wp_createTmp`/`wp_removeTmp` thread
  `walPipeKey`), Pipe, filePipeline alloc/run, `WAL__renameWAL` (spec + proof), NameClaims (`walInv_dirPath`
  takes `I` and `walIncQ I`), ReadAllLaws, ReadAllWF, OpenPinTake, ExistPin, Exist, OpenAtPin (`walPinOut`:
  key at `ic`, write mode `walTmpsRes ∗ walIncEAny`), OpenUnpin/OpenAtSteps (`walInv_unpin` takes
  `walLockedTokI I`, `hi : incOf I dir = i`, the reserve in write mode), RepairPin (`walPinLast` with `I`,
  `walInv_unpinLast … I`), VsePin (`walPinAllRes` starts `∃ I`), ValidSnapshotEntries, Unsaved, HandleLoans
  (`walInv_dirKeyArea`/`returnHLoans{1,2}` take `i I hi` and the lock token), ReadAllGive (`i`), CutAu (key at
  the handle's `i`, `walDirKey_lookupWC`), TailSyncIdle/TailFsyncIdle/FdatasyncIdle/`WAL__syncIdle(F)` (the
  approved `walIncQ I ∗ ⌜incOf I dir = i⌝`), ReadDefs (`walReadTie dir i …`, `walReadH … s i`, `walFailH … i`,
  `walReadFailedF := ∃ i, walHandlePI w dir i .failed ∗ walFailH … i`, `walReadOnlyF := ∃ I, walLockedTokI I ∗
  walReadH false … (incOf I dir) ∗ …`), OpenLastDefs (`walLastOpen` with `I`), ReadState (`i I hi`, `walIncQ`).
  Specs edited: `WAL__renameWAL`, `newFilePipeline`, `WAL__syncIdle(F)`, `openAtIndex` (post), `WAL__Close`
  (`.opening` pre); `Pipe.lean`'s `pipeRes`.
  **Frontier** (`lake build …wal.Link`, `/shared/tmp/p6b-build6.log`): `BrokenAu:183,192`, `CloseHandle:124`
  (`WalCloseLaw`: key at the handle's `i`, and it must take the pipeline's `walPipeKey` from `pipeLeft` to
  put the reserve back with `walParked_putTmps0`; same in `CloseLaw`, `CloseLawU`, `WAL__CloseOpening`,
  `WAL__CloseFailed`), `CutSync:148`, `Open:42-64` and `OpenForRead:47` (`walReadH … i`), `ReadAllCommit:78,128`
  and `ReadAllInv:76` (thread `walIncQ I` from the handle: `walHandlePI_incQ` / `walLockedTokI_incQ`),
  `ReleaseTie:105-162`, `openAtIndex:144` (`subst hIl` then `walInv_dirPath … Il` with `walLockedTokI_incQ`;
  pass `walLockedTokI Il` to `walInv_unpin` directly instead of `walLockedTokI_tok`; write mode's reserve),
  `openLast:98` (`walPinLast` now has `%I`; `walInv_dirPath … I` with the quarter). Behind them (not yet
  reached): Repair, CloseFailed/CloseOpening, WAL__ReadAll (`walDirKey_agree` at `:359`), PurgeAu/PurgeOther/
  PurgeRoundLaws, RepairPre, ReadAllPrefixAccess, ReadAllRegCommit, HandleUnnamed's users, Create.lean (pass
  `UH := fun x => createUK … x`, arm 4 destructs `createUK`), and the leaves.
  **Then** (unchanged from the brief): the pin bump to `251a430ce` (commit alone), state C, the `Discard` spec
  (ledger first) and proof, `etc/gen-link.py --walfs`, the builds.
- **2026-11-25, P6b session 19 (WIP, `etcd-safe-p6b-wip`): S's pure facts and the layouts' distinctness done; S's
  Iris step not started.** **Decision (coordinator, internal):** the gap "two WALs have different directory inodes" by
  the fraction argument, an invariant fact only if it does not follow; **it follows** with no invariant change: with no
  write-mode handle out (`walParked`'s `o.T = []`, the lock token free), `walTmpParked0` holds `walTmpsRes J` for each
  layout's directory, three quarters (`qTmp`) of `J`'s `0.tmp` claim each; two layouts on one `J` give two (`qTmp_two`).
  (The `walTmpsHalf` route also works: `qTmp + qTmpI + qTmpI > 1`; the parked route is simpler.) Noted in
  `notes/wal-p6b-design.md`.
  **Done**, new `Proof/.../wal/DiscardSInv.lean` (imports `DiscardSPure`, `DiscardR`, `CreateDropInv`, `BootPure`;
  `lake build` of the module on fk-lean1 at `2457004ed8`: exit 0, no `sorry`, `/shared/tmp/p6b-s19-b6.log`; nothing
  imports it yet):
  * `dropC cl c` (`cl.filter (· ≠ c)`, classical: `Claim` has no `BEq`; the form of `osClaims_filter_once`,
    CreateMergeStep.lean, which takes the claim out of `osClaims` under `ClaimOnce`), `mem_dropC`;
  * `DropDirOk cl j N h` (log, mem, no other claim of `j` on `N`) and **`DropDirOk.crash`**: a crash of `dropC cl
    (j,N,h)` has a crash `m''` of `cl` equal off `j`'s names of `N` (over `regionCrashedK_dropDir` + `_cover`);
    `entsOf_off`;
  * `discS s dir` (`wal := delete dir`), `crashOkA_dropDir`/`crashOkW_dropDir`, `walDirClaim_dropDir`;
  * `DiscSet Ls cl jr dir lay N hj` (lay at dir, `DropDirOk`, other layouts on other inodes, `lay.j ≠ jr`) and
    **`discSet_of`**: from `DirKeysOk`'s `DirClaimsOk`/`DirClaimExcl` (N = `.except walTmps`), the claims' log
    (`osClaims_log`), and the distinctness;
  * `absentNone_discard`, `walsOk_discard` (`DirsOk` by `dirsOk_roots`: needs `RootsOk R`, from `osPathS`,
    TreeSharedClaims.lean:582; `AbsentOk` by `absentOk_of_absentNone`), `walsNamed_discard`, `walsCreateOk_discard`,
    `walsAt_discard`, `claimOnce_dropC`, `dirClaimOk_dropC`, `dirKeysOk_discard` (keys `K.delete dir`);
  * **`discNone_of`**: `hnone` for `dir` from the area claim `(jr, N0, hC) ∈ cl` holding nothing at `nm`, being the
    only claim of `jr` on `nm` (`honly`: from `osNames_disj`/`osClaims_excl` against the program's half), and
    `LastWrite hC jr nm x e Es`, `x < n`, `Es !! nm = none` (`regionCrashed_lastWrite`); `inArea_nm_inj`;
  * **`discS_pure`**: every pure conjunct of `walInvBody` at `(discS s dir, Ls.delete dir, dropC cl (lay.j, N, hj),
    n, K.delete dir)` from the old ones at `n0 ≤ n` (mono lemmas inside), given `DiscSet`, `RootsOk`, `hnone`;
  * Iris: `walTmpsRes_excl`, **`walTmpParked0_inj`** (`walTmpParked0 Ls [] ⊢ ⌜distinct⌝ ∗ walTmpParked0 Ls []`).
  **Next: S's Iris step** (`walInv_discardS`, at a program step after `syncDir.spec`, mask ⊤, as `walInv_named`
  in CreateNamedStep.lean). Program in: `walUnlockedTokX`, `walNamesFragS ⟨none, some dir, []⟩`, the program's half
  of `(jr, .only [nm, tmp], hC)` after R (`renDirOut`'s: `nm` none, `tmp` the directory `J`), `osCommitLb n` with
  the rename's `LastWrite hC jr nm x e Es`, `x < n`, `AU₂`, `osSharedInv R`, `osPathS` (for `RootsOk`). Inside
  `walInvBody s`: `walGhost`'s `walGhostI s I` (`walGhostI_bump` to `(discS s dir, <[dir := incOf I dir + 1]> I)`,
  `walLeI_discard`, Ghost.lean:294; the shares from `walUnlockedTokX_open`, `walParked_incE`,
  `walDirKeysAuth_bump`, the view's out of `AU₂`, as `discAU`'s logged arm, DiscardR.lean); `osClaims_log` →
  `DropDirOk.log`; `walParked` with `o = empty` (from the token's `walOutFrag empty`): `walTmpParked0_inj` →
  distinctness; then `discSet_of`, `discNone_of` (`honly` by `osClaims_excl`), `discS_pure`; resources out:
  `osClaims_filter_once` (the dir claim's invariant half), `walParked`'s `ParkedClaim` half of it, `walTmpsRes
  lay.j` (`walTmpParked0`'s `Jt` delete `dir`) and `walTmpsHalf lay.j` (`walTmpHalves`' `Jh` delete `dir`),
  segments' halves of `lay` dropped (`laysResF` and `walParked`'s `segResP` over `segsAll (Ls.delete dir)`:
  split with `BigSepM.bigSepM_delete` as `segsAll_sep_same`, TailSync/PurgeAuLemmas), `walTailsRes` over
  `Ls.delete dir` (find/write a `walTailsRes_delete`; `s.wal !! dir`'s tail record goes), `walOthersL` (dir's
  others, files: to the program for `SubCover`), `walNamesRes` with `disc := none` (`Wn` unchanged: `dir` not
  in it), `AU₂` committed (`walOwn M → M.delete dir`), `walUnlockedTok` rebuilt. Then out of the step:
  `osNames_merge` twice (`.except walTmps` + `.only [0.tmp]` + `.only [1.tmp]` → `.except []`), tagged `tmp`
  into `walAreaRes`'s `cl` (session 18's notes on `SubCover`/`ClRanked`), the program's area half merged back
  (`walInv_mergeIn`). Then the `Discard` proof, the crash lemma, the docstrings, `gen-link --walfs`, builds.
- **2026-11-25, P6b session 18 (WIP, `etcd-safe-p6b-wip`): S started (its crash-tree core); S's plan refined.**
  **Done**: new `Proof/.../wal/DiscardSPure.lean` (imports `CreateDrop`; `etc/lean-check.py -a`: 0 errors, no
  `sorry`; nothing imports it yet, not in a `lake build`): `exists_dir` (a `Dir` from a function supported on a
  candidate list, through `GMap.ofList`), `valAfter_cands`, `exists_treeSetN` (the tree with `j`'s names of `N` set
  by `f`), and **`regionCrashedK_dropDir`**: dropping a whole directory claim `(j, N, h)` from the invariant's
  claims (no remaining claim on a name of `N` of `j`): every crash `m'` of the rest has an `m''` that is a crash
  of all (kept set `dropK`), equal to `m'` off `j`'s names of `N`. This is what S needs to take the discarded WAL's
  directory claim `(lay.j, .except X, hj)` out of `cl` (as `CreateDropInv`'s `DropOk.crash` for one name).
  **Found reading for S (check these first next session):**
  * the pipeline names' claims (`tmpHalf`/`tmpClaim`, `TmpClaim.lean`) are **not in `cl`**: they are separate
    `osNames` fractions `qTmpI`/`qTmp` (in `walTmpHalves`, and `walTmpParked0` or out); so `cl` loses only the
    directory claim; the program gets the tmps claims whole from `walTmpParked` (lock free: `o.T = []`) and the
    invariant's `walTmpHalves` (`Jh` loses `dir`), then `osNames_merge` twice into `(lay.j, .except [], hj')`.
  * `walAreaRes`'s new conjuncts for `tmp := tmpName nm`: `SubCover (clOf cl' tmp) (some (.dir J))` needs only
    `(J, .except [], hj') ∈ clOf cl' tmp` and that every entry of `hj'.cur` is a file (`ClReach` then stays at
    `J`): `SegsNamed` (`.wal` names), `tmpEnt` (pipeline names), `walOthersL` (the others); `ClRanked` is then
    trivial (no directory entry). `clOf cl tmp` before S is `[]` (the `RemoveAll(dir.tmp)` consumed it).
  * the area claims: after U' the invariant holds half of `(jr, .only [nm, tmp], hC)` in `cl` and the program the
    other half (`renDirOut`'s); merging it back into the program's area claim `(jr, N \ tmp, h)` is an invariant
    step (`walInvBody_mergeIn`, as `Create`'s commit), giving `walAreaRes`'s `N ∪ {nm}` (`nm` left `Wn` at U').
  * pure facts over `cl'` (the dir claim dropped) by `regionCrashedK_dropDir`: other WALs' crash conditions read
    `entsOf m' lay'.j` and the area `jr`: **needs `lay'.j ≠ lay.j` for other layouts** (no lemma seen yet:
    check `DirKeysOk`/`walDirKey`'s keys, `DirClaimOk`'s `ClaimOnce`; else derive from `WalsAt` + the area
    claim's entries; checked at the end of session 18: `DirKeysOk`/`DirClaimsOk` do not give it, and two layouts
    sharing `J` would share one `ClaimOnce` claim; an Iris route: `walTmpHalves`' `[∗map] dir ↦ J ∈ Jh` holds one
    `walTmpsHalf J` per layout, so two layouts on `J` give two `qTmpI` fractions of `osNames J (.only [0.tmp])`
    besides the program's `qTmp` (parked, lock free): over 1 if `qTmp + qTmpI = 1`; check `TmpClaim.lean`) and `lay.j ≠ jr` (`WalsAt.ne`); `DirsOk` by `DirsRoots` (durable dirs are roots); `AbsentOk`
    is implied by `AbsentNone`; `AbsentNone` for `dir` from the raised commit lb past the rename (the rename is
    the last write of `nm` in the area claim: `regionCrashed_lastWrite`, as `CreateNamedStep`).
  **Next**: the rest of S (pure: `walsOk_discard`, `absentNone_discard`, `walsNamed_discard`, `dirKeysOk_discard`
  (keys `K.delete dir`), `walsAt_discard`, `walsCreateOk_discard`; Iris: the layout's resources out of
  `laysResF`/`walParked` (segment halves dropped), the tmps claims, `walTailsRes`/`walNamesRes` over `Ls.delete
  dir`, `walGhostI_bump` with `walLeI_discard`, `AU₂` committed, `disc := none`, `walUnlockedTok` rebuilt), then
  the `Discard` proof, the crash lemma, docstrings, `gen-link --walfs`, builds. Session stopped at the ~150k-token
  handoff rule (most of it spent reading for S). **Build**: `lake build` of `wal.DiscardSPure` + `wal.DiscardR` on
  fk-lean1 at `3b1a5575df`: 3023 jobs, exit 0, no `sorry` in either (`/shared/tmp/p6b-s18-b1.log`).
- **2026-11-25, P6b session 17 (WIP, `etcd-safe-p6b-wip`): R done; S not started.** **Decision (coordinator,
  approved, internal, not a spec change):** `walDirKeysAuth` (Ghost.lean) gains `⌜∀ dir i x, Kall !! (dir, i) = some x
  → i ≤ incOf I dir⌝` (keys are recorded only at incarnations up to the current one; no existing lemma gave `Kall !!
  (dir, ic+1) = none`). Sites fixed: `walDirKey_lookupG`, `walDirKey_insertG` (the new key is at the current
  incarnation), `walDirKeysAuth_getG`, `walGhost_init` (`Kall = ∅`). New `walDirKeysAuth_bump K : walDirKeysAuth K ⊢ ∃ I,
  walIncE I ∗ ∀ I' K', ⌜(∀ d, incOf I d ≤ incOf I' d) ∧ ∀ d x, K' !! d = some x ↔ (incOf I' d = incOf I d ∧ K !! d =
  some x)⌝ -∗ walIncE I' -∗ walDirKeysAuth K'`. Ghost.lean lean-checked (0 errors).
  **R** in the new `Proof/.../wal/DiscardR.lean` (imports `DiscardSteps`, `CleanupAu`, `CreateNamed`; `etc/lean-check.py
  -a`: 0 errors; nothing imports it yet, not yet in a `lake build`):
  * pure: `unnameS s dir := absDiskUpd s dir (named := false)` (+ `_none`/`_wal`/`_area`/`_dirs`), `crashTo_unname`,
    `crashOkA_unname`, `crashOkW_unname`, `walFullOk_unname`, `walsOk_unname`, `dirKeysOk_unname` (over fewer keys
    `K'`), `absentNone_unname`, `walDurLe_unname`, `incOf_bump`, `keys_bump` (`K.delete dir` after the bump);
  * `walUnlockedTokX_open` (the token less its `walIncQ` quarter and `walOutFrag empty`, a wand back at any `I'`),
    `walParked_incE` (the pipeline reserve's eighth out of `walParked`, lock free);
  * **`discAU`**: `⊢ walInv … -∗ discP dir N h jr ic Q₁ -∗ osAUnc (osNames jr N ½ h) (renDirOut jr J N nm tmp h ½ lb)
    (discQ dir N h jr ic Q₁)`, premises `InArea r dir nm`, `nm ≠ tmp`, `N.Mem nm`, `N.Mem tmp`, `h.cur !! nm = some
    (.dir J)`, `h.cur !! tmp = none`, `h.next ≤ lb`, `¬ walNameOk tmp`, `AreaSlot tmp`. `discP := walCleanPin N h jr ∗
    discAU₁ dir ic Q₁` (`discAU₁` = the spec's `AU₁`); `discQ none := discP` (as `walCreateQ`), `discQ (some _) :=
    walUnlockedTokX ∗ ∃ d, Q₁ d`. Opens `AU₁` up front with the os update (as `walCreate_osAUnc`); the logged arm:
    `walCreating_deleteC` (token back), the five shares (`walUnlockedTokX_open`, `walParked_incE`,
    `walDirKeysAuth_bump`, the view's, `walGhostI`'s) through `walGhostI_bump` with `walLeI_unname`, `AU₁` committed at
    `unnameS s dir`, `<[dir := ic+1]> I`, the claims `movClaims` (`renDirEnt = movEnt` as `h.cur !! tmp = none`), the
    pure facts `walsOk_unname` then `*_moved` over `unnameS s dir`, keys `K.delete dir`, `walNamesRes_congr`.
  **The pin**: the Discard proof calls `walInv_pinClean` (CleanupAu.lean; `b := nm`, `walNameOk nm` from U') right
  after `walInv_discardU`, depositing U's `walUnlockedTokX`; the pin is needed because `osAuMask` excludes `osShN`
  (no `osClaims_keys` inside the update).
  **Next:** S (`syncDir.spec`'s commit: as session 7's/16's plan; `walGhostI_bump` again with `walLeI_discard`, keys
  `K.delete dir` again trivial (`keys_bump`), the WAL's layout out of `Ls` and its directory's claims out, tagged
  `tmpName nm`, into `walAreaRes`'s `cl` (`SubCover`, `ClRanked`)), the `Discard` proof, the crash lemma, docstrings,
  `gen-link --walfs`, the builds. **Build**: `lake build` of `wal.Link` + `wal.DiscardR` on fk-lean1 at `c1366806fa`:
  3849 jobs, exit 0, no `sorry` (`/shared/tmp/p6b-s17-b1.log`). Session stopped at the ~150k-token handoff rule.
- **2026-11-25, P6b session 16 (WIP, `etcd-safe-p6b-wip`): U' done; R/S not started.** Ledger "wal.Discard's
  post had no arm for a failed `RemoveAll(dir.tmp)`" marked approved (coordinator: the `RemoveAll` error arm returns
  `walAreaRes`, `walUnlockedTok`, `AU₁`, `AU₂`, nothing committed; U' with `Create`'s creating-claim shape `.only [nm,
  tmp]` approved). **Done** in the new `Proof/.../wal/DiscardSteps.lean` (imports `CreateSteps`, `NameSplit`;
  `etc/lean-check.py -a`: 0 errors; not yet in any `lake build`, nothing imports it yet):
  * step 1: `exists_walName_notin Wn : ∃ b, walNameOk b ∧ b ∉ Wn` (with `walAreaRes`'s `∀ nm, walNameOk nm → N.Mem nm
    ∨ nm ∈ Wn` it gives the WAL name `walInv_drop` needs in the area claim `N`);
  * U': `lay_nm_inj` (pure), `nameShares_erase` (loans `[]`: every share `0`, `bigSepL_perm` by `perm_cons_erase`),
    `walInvBody_unregister` (frag `none` → `⟨none, some dir, []⟩`, `Wn` → `Wn.erase nm` on both halves, the program
    half `(jr, .only [nm], hn)` out of `nameShare`, `hn.cur !! nm = some (.dir J)`), `walInvBody_discardU` (=
    unregister, then `walInvBody_mergeIn` with `N1 = .only [nm]`, `N2 = .only [tmp]`, `T := walUnlockedTokX`; NO
    creating-map entry is used: the claim is found later by `osClaims_keys`), `walInv_discardU` (program step:
    peeks `AU₁` for `s.wal !! dir = some _`, as `walInv_absent`; AU destructuring that works: `isimp only
    [texist_cons, texist_nil] at Hacc`, then `isimp only [Std.Tele.app, ULift.down]` on the opened `α` only, else
    the AU handed back by the abort does not unify with the original). Post: `walUnlockedTokX ∗ walNamesFragS
    ⟨none, some dir, []⟩ ∗ walSplitFrag (Wn.erase nm) ∗ osNames jr (.only [nm, tmp]) ½ hC ∗ ⌜nm ∈ Wn ∧ hC.restrict
    jr (.only [tmp]) = hT.restrict … ∧ hC.cur !! nm = some (.dir J)⌝`, and `AU₁` back.
  * R/S ghost core: `walGhostI_bump s s' I I' I1..I4 M hle hk hst hlk`: sets **all five** shares of `γI` to `I'`
    (`walGhostI`'s quarter, the view's and the lock's `walIncQ` quarters, and two `walIncE` eighths: the keys'
    authority's, in `walDirKeysAuth`, and the pipeline reserve's, in `walOutAuth` while `o.T = []`, i.e. the lock
    free). Session 15's plan for R named only three; the eighths must be taken out of the body's `walDirKeysAuth K`
    and `walParked`'s `walOutAuth o` too. `hle` from `walLeI_unname` (R) / `walLeI_discard` (S), both in Ghost.lean.
  **Risk found for R (check first):** `walDirKeysAuth K` says `K !! dir = some x ↔ Kall !! (dir, incOf I dir) = some x`;
  after the bump `K' := K.delete dir` satisfies `DirKeysOk` (it only constrains present entries) but the `↔` needs
  `Kall !! (dir, ic + 1) = none`, which nothing states today. If no lemma gives it, add to `walDirKeysAuth`'s body
  `⌜∀ d i x, Kall !! (d, i) = some x → i ≤ incOf I d⌝` (internal invariant, not a spec; inserts are at the current
  incarnation) and fix its few construction sites (`grep -n walDirKeysAuth *.lean`).
  **Next (unchanged order):** R (`osAUnc` for `os.Rename.specDirSnc`: as `cleanAU`, claim found by `osClaims_keys` on
  `.only [nm, tmp]` + `osClaims_once` + `osNames_coh`; commit: `s' := absDiskUpd s dir (named := false)`, `I' :=
  <[dir := ic+1]> I`, `walGhostI_bump`, `movClaims` and `CleanupMoved`'s `*_moved` with `hun` true of `s'`, `walNamesRes`
  over `s'` (disc conjunct: `dir`'s layout exempt), `AU₁` committed with the view's `walIncQ`), S, the `Discard` proof,
  the crash lemma, docstrings, `gen-link --walfs`, the builds.
- **2026-11-25, P6b session 15 (WIP, `etcd-safe-p6b-wip`): `Discard` approved; a spec defect found; state C started
  (the invariant's relaxation only).** Ledger "wal.Discard" marked approved (coordinator: as written; P5's condition 2
  met because the client chooses `Q₁`, written into the entry).
  **Spec defect (ledger 2026-11-25, "wal.Discard's post had no arm for a failed `RemoveAll(dir.tmp)`", pending; applied
  on this branch):** the approved post gives `∃ d, Q₁ d` in every arm, i.e. says `RemoveAll(dir.tmp)` cannot fail, but
  `os.RemoveAll.specSubS` allows an error under `FsNoErrAt` (only `nil ⇒ gone`), and `Discard` returns it before the
  rename. New first arm: `err ≠ nil ∗ walAreaRes jr ∗ walUnlockedTok ∗ AU₁ ∗ AU₂` (nothing committed; `Create`'s
  `create_abortTmp` gives exactly the token and `walAreaRes` back). The spec file builds.
  **`walNamesRes` relaxed** (`Inv.lean`): conjunct A's second part `… → st.reg ≠ some dir → st.disc ≠ some dir → lay.nm
  ∈ Wn` (the discarded WAL is the one present layout not registered); the disc conjunct is now `(st.disc ≠ none →
  st.reg = none) ∧ loans registered`. Sites fixed: `walNamesRes_addWal`/`_insert` (Inv), `NameSplit` (`split_present`'s
  `hW` takes the extra `none ≠ some dir`), `NameClaims`, `CreateSplit` (`walInv_register`), `Crash` (`walInv_alloc`'s
  construction). `lake build` of `wal.Link` + `Spec...wal.Discard` on fk-lean1 at `3177f4b87d` (the commit before these
  notes): 3848 jobs, exit 0, no `sorry` (`/shared/tmp/p6b-s15-b2.log`). Not yet built: the tester and the leaves.
  **Refined plan for C (found reading `Create`; replaces session 7's U):** the rename needs ONE claim holding `nm` and
  `nm.tmp` (`os.Rename.specDirSnc`: `N.Mem bs ∧ N.Mem bt`, the program's fraction `q`, the update's `r`). Do it as
  `Create` does, with `Create`'s creating-claim shape `.only [nm, tmp]`, not by merging into the area claim:
  1. `walInv_drop` (`CreateSteps.lean`) of `tmpName nm` off the program's area claim `(jr, N, h)`: it needs a WAL name
     `b ∈ N` to find the invariant's half; `nm` is registered (not in `N`), so add a fresh-name lemma `∃ b, walNameOk b ∧
     b ∉ Wn` (`walNameOk` = nonempty, no `/`, no `.`: a string of `a`s longer than every name of `Wn`), then `N.Mem b` by
     `walAreaRes`'s first fact. Then `area_takeTmp`, `wp_removeAllTmp` (`CreateTmp.lean`) with `os.RemoveAll.specSubS`;
     on its error `create_abortTmp` (`CreateAbort.lean`) → the new first arm.
  2. **U'** (`DiscardSteps.lean`, `walInvBody` level, then `walInv`): open the invariant, peek `AU₁` (open at
     `walAuMask`, abort) for `s.wal !! dir = some d` (the view's `walOptLe` into `s.wal`), `WalsOk` → `lay`, `InArea r dir
     nm`, `lay.nm = nm`; with `walNamesFrag none` (from `walUnlockedTok`) `walNamesRes` gives `nm ∈ Wn` and, loans `[]`,
     `nameShare` at exactly `½`: the program half of `(jr, .only [nm], hn)` with `hn.cur !! nm = some (.dir lay.j)`.
     The invariant half is in `cl` (`osClaims_keys` + `WalsCreateOk` at `nm`, as `walInvBody_merge2`'s `hm1`). Merge it
     (both halves, `osNames_halves`) with the whole `.only [tmp]` claim (`osNames_merge`) into `(jr, .only [nm, tmp], hC)`,
     halve it (one in `cl` in place of nm's: `CoverOk` by `coverOk_merge`-style; the facts by the `*_cover` lemmas of
     `CreateMerge.lean`), the other half to the program; `Wn' := Wn.erase nm` in both `walSplit` halves
     (`walSplitFrag` is `walAreaRes`'s; `shareLs` over `Wn.erase nm`: loans `[]` so every share is `0`, a re-index of the
     big sep); frag `⟨none, some dir, []⟩` (`walNamesS_set`). Creating map empty: `walCreating_empty` with `T :=
     walUnlockedTokX`, `walUnlockedTokX_exclX`. Template: `walInvBody_mint` (`CreateMint.lean`), whose `nm` comes off the
     area claim instead of a registered claim.
  3. **R**: the rename's `osAUnc` as `cleanAU` (`CleanupAu.lean`) with `brk := tmpName nm` (`tmpName_not_walName`,
     `tmpName_areaSlot`, `tmpName_ne`), the claim `.only [nm, tmp]` found by its record (no pin needed if U' records it:
     simplest, keep it `ClaimOnce` and found by `osClaims_keys`), but the real state changes: `s' := s` with `dir`'s
     `named := false`, `I` bumped (`walLeI_bump`), and `AU₁` committed in the same commit (the client's quarter in
     `walDiskAtI`, the ghost's half, the lock's quarter from `walUnlockedTokX`'s `walIncAny`). `CleanupMoved`'s
     `walsOk_moved`/`absentNone_moved`/`walsNamed_moved`/`dirKeysOk_moved`/`walsAt_moved` take `hun : ∀ d, s.wal !! dir =
     some d → d.named = false`: true of `s'`; check each also holds across `s → s'` (`walsBounded_upd`, `DirsRoots.upd`,
     `walNamesRes_congr`).
  4. **S** as session 7's (the commit lb from `syncDir.spec`'s `osCommitLb n`; `walLeI_bump` again; `AU₂`; `Ls.delete
     dir`; the WAL directory's claim and the tmp halves out to `walAreaRes`'s `cl` tagged `tmpName nm`; `disc := none`).
     Then the program's half of `.only [nm, tmp]` (now holding `nm` absent, `tmp` the directory) merged back into the
     area claim: `walInv_mergeIn`/`walInvBody_merge2` with `T := walUnlockedTokX`, then `area_give` (`CreateArea.lean`).
  5. The proof file, the crash lemma (P5 condition 1), the docstrings naming `DiscardUnsaved`, `gen-link --walfs`, the
     builds: unchanged from the brief.
- **2026-11-25, P6b session 14 (WIP, `etcd-safe-p6b-wip`): tester built, pin bumped, `Discard` specified; state C
  not started.** Ledger "fix B's lemma-level signatures" marked approved (`6413ef7702`). **Tester**: built on fk-lean1
  (the coordinator allowed a seed there: worktree `/home/ubuntu/eg/wt/etcd-safe-p6b-wip`, `FKLEAN_HOST=fk-lean1`)
  at `6413ef7702`: `WalTester...etcd.wal.{Link,Adequacy,TopLevelRobustness}`, 4264 jobs, exit 0, no `sorry`
  (`/shared/tmp/p6b-tester-r1.log`). `etc/gen-link.py --walfs/--durable/--wal-tester --check`: all up to date.
  **Pin bump** (`3793559312`, alone): `etc/goose.py` project `etcd` `rev` → `251a430ce042` (`goose-lean-fmt1c-discardfix`),
  the examples' `go.mod`/`go.sum` (pseudo-version `v3.0.0-20261125101634-251a430ce042`, sums from `go mod download`;
  `go list -mod=readonly -deps ./...` clean in each), `--project etcd` (2 files: `wal.lean`, `etcdserver.lean`), then
  `--check`: every project up to date. No spec or proof names `DiscardUnsaved` (only docstrings: `Ghost.lean`,
  `Inv.lean`, `NameClaims.lean`, `NameLoans.lean`, `Unsaved.lean`'s spec, `etcdserver/{InvCrashImage,CrashInterim}.lean`;
  to reword with C). `bootstrap.wp_proof` is first-start only (`haveWAL = false`) and names neither `Unsaved` nor the
  discard. Post-bump build of the leaves of `etc/importers.py --git 5a1c41d945 --leaves` (644, the 4 `notes.*`
  leaves dropped: not targets) at `d767c73cac` on fk-lean1: 16389 jobs, exit 0, no `sorry`
  (`/shared/tmp/p6b-bump-r3.log`): the bump breaks nothing.
  **`Discard` spec** (`d767c73cac`, `Spec/.../wal/Discard.lean`, lean-checked; ledger 2026-11-25 "wal.Discard",
  pending): the two updates without `walBlank` (the function reads nothing), `Create`'s area resources and
  premises (with `dirDurable r`), post `osPathS ∗ osCallPerm 1 ∗ ∃ d, Q₁ d` and `nil` ⇒ `walAreaRes ∗ walUnlockedTok ∗
  Q₂`, error ⇒ `AU₂` back. P5's three conditions: how each is met is in the ledger entry.
  **Next (state C, then the proof)**, as session 7's plan with these anchors: `walLeI_bump` (Ghost.lean, exists) covers
  R's unnaming and S's deletion (both bump `I`); `walNamesRes` (Inv.lean ~2290) has `st.disc = none` today: C
  relaxes it to "`disc = some dir` ⇒ the WAL at `dir` unnamed, or the area claim still holds the directory at `nm`";
  R's template is `Create`'s cleanup rename (`CleanupAu.lean` `cleanAU`, `CleanupMoved.lean` `movClaims`/`*_moved`,
  target `nm.tmp` in place of `nm.broken.*`); merges by `osNames_merge` (`GooseLang/Ext/Fs/TreeShared.lean:122`);
  the parked tmp state `walTmpParked` (Inv.lean:1789), `walTmpsRes`/`walTmpsHalf` (TmpClaim.lean). New file
  `DiscardSteps.lean` (U/R/S as `walInv`-level lemmas), then `Proof/.../wal/Discard.lean` (`RemoveAll` as `Create`'s
  `os.RemoveAll.specSubS`, U, `os.Rename.specDirSnc` with R, `syncDir.spec` with S, `lg.Info`), the window's crash
  lemma (P5 condition 1) beside `walDiskAt_crash_keep` (Crash.lean), `etc/gen-link.py --walfs`, the builds.
- **2026-11-25, P6b session 13 (WIP, `etcd-safe-p6b-wip` @ `8fc495f329`): fix B done; `wal.Link` builds with no
  `sorry`** (`lake build Proof.go_etcd_io.etcd.server.v3.storage.wal.Link`, 3847 jobs, `/shared/tmp/p6b-build8.log`;
  no `declaration uses 'sorry'`). The three session-12 ledger entries marked approved. Every lookup threads its
  holder's quarter `walIncQ I` (`incOf I dir = i`): `walOpening_incQ`/`walOpenWI_incQ`/`walOpenWCI_incQ` (Ghost),
  `walLockedTokI_incQ`; the close laws (`WalCloseLaw`, `walCloseLaw(U)`) take `walPipeKey` from `pipeLeft` and
  give the reserve to `walInv_unpin(XI)`; `HandleLoans` and the lending laws (`BrokenLend`) take `walIncQ I`, not
  the lock token; the failed handle is `walHandlePI w dir i .failed` (`walInv_failOpening`, `readAll_failWp*`,
  `walFailCommon … i`, `walReadFailed_lockedTokI`); purge (`walPurgeP`/`walPurgeOP … I`, `walInv_walFiles`,
  `walOpenWFI_lend` returns the handle's quarter, `walOpenWF_lend` removed as unused; the tester's `purgeRound`
  threads it through its loop invariant) and the prefix probe (`probeHandles`/`prefixScanState … I`) carry the
  quarter; `Create` passes `UH := createUK …`. One ledger entry for these lemma-level signatures ("fix B's
  lemma-level signatures"). `WalTester/…/purgeRound.lean` checked with `etc/lean-check.py -a` (0 errors), the
  tester's Link not yet built.
  **Next:** build the tester (`etc/gen-link.py --walfs`, the tester's `TopLevelRobustness`), then the brief's
  steps 2-4: the pin bump to upamanyus/etcd `goose-lean-fmt1c-discardfix` @ `251a430ce042` (`DiscardUnsaved` →
  `func Discard(lg, dirpath) error`; `etc/goose.py`, `--project <affected>`, `--check`; the bump alone in one
  commit; report if the bootstrap spec or proof cites `DiscardUnsaved`), state C, the `Discard` spec (ledger
  first) and proof, then `gen-link --walfs` and the builds (wal.Link, the tester, the server WAL consumers, P8's
  crash modules, the leaves of `etc/importers.py --git 5a1c41d945 --leaves`).
- **Resume here (session 1's plan, superseded by the line above)**: the swap, in `Ghost.lean` first (see the design's "Next"); then `HandleAlloc`, `NamedView`,
  `TailSync*`/`TailLenLb`/`CutAuLemmas` (the files that unfold `walGhost` or the facts), then the specs
  bottom-up (`etc/importers.py --uses walSyncedLb ...`), the tester, `Crash.lean`/`CrashS.lean`'s crash
  lemmas and P8's new consumers (`WalRecsCrash`, `WalCrashRead`), then `DiscardUnsaved`.

## START HERE

- **P6b item 1: approved (incarnation = the directory inode `j`); design in `notes/wal-p6b-design.md`,
  not started in Lean.** Found while designing: `walDirKey` (persistent, keyed by `dir`, "fixed for the
  generation") also blocks a re-`Create`, and `walLenLb` reads past states too; the design moves the three
  lower-bound facts to per-incarnation persistent maps so that `absLe`/`walGhost`'s signatures and
  `Crash.lean` stay until the last step (merge `etcd-safe-p8` first there).

- **2026-11-25 (after the re-pin): the WAL builds at `2c17304ea8`** on fk-lean2 (`fklean1-check.sh`,
  targets `wal.Link`, WalTester's `Link`, `Adequacy`, `TopLevelRobustness`: 4260 jobs, exit 0).
  `tcb-report --collection wal-fsext.txt --check` not run (it needs every root up to date: the packet's
  full build). P6b not started in Lean: its facts' signatures change `Crash.lean` (P8's file), so the
  coordinator decides the order first.

- **2026-11-25, session 6 (later): re-pinned to etcd_safe's one pin; P6 stays off `lean`** (coordinator-E, #50:
  P6 goes in the one `etcd_safe` packet; the remote full build and gates not run).
  * **Pin** `upamanyus/etcd` `goose-lean-fmt1c-crashfixes` @ `e94f33b50` (`etc/goose.py`, the examples' `go.mod`
    by `bump-p6.sh`'s method). `server/storage/wal` is **identical** between `2bd3048d7` and `e94f33b50`
    (`git diff --stat`: empty); `2bd3048d7` has nothing `e94f33b50` lacks (the whole diff only adds, but
    bbolt's `go.sum` lines, replaced by the `upamanyus/bbolt` replace). Retranslation (`etc/goose.py
    --project etcd`): 3 files, `Code/.../etcdserver.lean` (`bootstrap`'s backend removal,
    `removeBackendDurably`, `applySnapshot`'s guard from `47d6cdeeb`), `Code/.../storage.lean`
    (`OpenSnapshotBackend`/`RecoverSnapshotBackend`'s `syncDir`), `Code/.../storage/backend.lean`
    (`finishDefrag`'s `syncParentDir`); no `GeneratedProof` change, no WAL change, no bbolt change (project
    `bbolt` is pinned separately and the etcd project translates bbolt names-only). So **no WAL proof
    breaks**. Proofs whose bodies changed (outside the WAL, not fixed here: integration round 2's):
    `Proof/go_etcd_io/etcd/server/v3/etcdserver/{bootstrap,EtcdServer__applySnapshot}.lean`,
    `Proof/go_etcd_io/etcd/server/v3/storage/OpenSnapshotBackend.lean`. `bootstrap`'s unsaved-WAL branch now
    calls `wal.Unsaved` itself (then `removeBackendDurably`, then `DiscardUnsaved`): `Unsaved`'s spec is ready
    for it; P6b/P5 must account for the backend removal.
  * **W1**: the WAL's crash facts rest on W1 alone of the world (`walCrash_pure`'s `hw1`, which enters only
    through `w1G_of_W1`; its docstring now says so). Stale-byte tears are out of scope
    (`nonissues/etcd-wal-record-type-outside-crc.md`). **The torn-Save `Save` writes no frame over stale
    bytes**: it only appends at the tail's write offset, and every byte from there on is zero and synced
    before the first append: a new segment is `alloc`'s `N.tmp` (`O_TRUNC`, preallocated), `Create`'s first a
    new file in its emptied temporary directory (preallocated), and an opened WAL's write-mode `ReadAll`
    zeroes from its end, `pendOff` when an interrupted `Save`'s entry run was dropped, and `Fdatasync`s the
    zeroing before returning (`wal.go` `ReadAll`, at `e94f33b50`). So W1's exclusions in reachable states are
    CRC-32C collisions on the `Data` of zero-backed frames. (`W1.lean`'s header still describes the `Type`
    question as open for review: its text is the statement's vocabulary, not edited here; the packet
    should refresh it.)

- **For the coordinator (2026-11-25, session 6): `Unsaved` done; `DiscardUnsaved` deferred to P6b (the order
  relaxation as approved is unsound); P6 ready for the full build.**
  * `Unsaved`: spec `Spec/go_etcd_io/etcd/server/v3/storage/wal/Unsaved.lean` (`ValidSnapshotEntries`' binders;
    `true` ⇒ `err = nil` and a WAL at `dir` whose history is blank, `walBlank`), proof
    `Proof/.../wal/Unsaved.lean` (the pin at the step after the logger check, every return puts it back at a
    step before it; the first segment's sequence `first` is 0 only when nothing was purged, below `2^64` by the
    step bound, which `walInv_openAll` now also returns), pure core `UnsavedDefs.lean` (`unsaved_blank`,
    `walBlank_take`: every crash image of a blank history is blank; `running_typ`: the `default` arm is
    unreachable). Linked (`walfs.wal.wp_Unsaved`, hypotheses `U.Ok`, `U.SnapCoh`, `WalDecEnvSupply` as
    `ValidSnapshotEntries`'), no axiom, no `sorry`. "Reads `walFresh`" needs, at the server, that no snapshot at
    index 0 has a nonzero term (raft's `IsEmptySnap`): P5/T7's obligation, stated in `UnsavedDefs.lean`'s header.
  * **The relaxation "named → unnamed → absent, lower bounds read while present" is not enough.** `bootstrap`
    re-`Create`s the WAL at the same `dir` in the same generation after `DiscardUnsaved`
    (`bootstrap.go:82`, `haveWAL = false`, then `bootstrapRaft` creates it). The persistent facts
    (`walNamed dir`, `walSyncedLb dir n`, `walPast s` with `dir` in `s`) do not say which WAL they are about, so a
    fact of the discarded WAL reads as one of the new WAL while it is present: `walGhost_raiseNamed`
    (`NamedView.lean`: a past state named ⇒ raise the view to named) would name the new WAL between its rename and
    `Create`'s parent fsync, where a crash may still drop it (`walCrash`), and `walSyncedLb dir n` (n > 0, a
    blank `Save` synced) would bound the new WAL's empty history. No relaxation of `absLe` alone can fix it: the
    transitivity `named(old) ≤ unnamed ≤ absent ≤ fresh-unnamed` is exactly what makes stale facts apply.
  * **Decided (coordinator, 2026-11-25): incarnations, in a follow-up P6b, not this landing.**
    `DiscardUnsaved` stays **unspecified** in P6 (its Go is translated; no spec, no proof, nothing links
    it). `bootstrap` is names-only here; its contract (P5) is what needs `DiscardUnsaved`'s spec, so P5's
    owner waits for P6b. Design and sizes: "P6b" below.
  * **P6's landing is ready for the full build** (the coordinator routes it): `wal.Link` (kernel build),
    no interface step (`interface/` and `etc/gen-interface.py`'s gate were removed on `lean`,
    `761f147a76`), `issues/raft-commit-lost-with-entries-kept.md` now `blocks-proof: yes` (the fork fix,
    `## Fix`), STATUS.md entry. The fork pin change needs Upamanyu's OK before landing (#50 P4 rule).

- **For the coordinator (2026-11-25): no trusted commit made; the `DiscardUnsaved` hard stop was a wrong
  analysis.** The WAL over `fsExt` never executes an `AbsDiskStep`: its abstract state is ghost state of
  the WAL layer (`wal/Ghost.lean`, untrusted: "Nothing of the extension's steps or interpretation is
  used"), and `Create`'s commit and `named := true` are ghost updates there. The only trusted pieces it
  uses are `walCrash`/`walImg` and the crash clause (`walStCrash := absDisk_semantics.crash`), which already
  allow what the discard needs: an unnamed WAL may vanish at a crash, an absent one stays absent. So
  `"WalUnnamed"`/`"WalDiscard"` in `Impl.lean` would be trusted text no proof uses; I did not add them.
  What blocks the discard is **untrusted**: the WAL layer's monotone order on states (`absLe`,
  `walMapLe`, `walDurLe` in `AbsDisk/Specs.lean`'s generic part, and the persistent facts built on it:
  `absPast`, `walNamed`, `walSyncedLb`, `walLenLb`) never lets an entry be deleted or `named` go back to
  `false`. The discard needs that order relaxed (an entry may go `named → unnamed → absent` under the lock
  token, the lower bounds read "while present"), with every consumer of those facts rechecked; no top-level
  statement mentions them (checked: the WAL's and WalTester's specs do, no `TopLevel*` file does). Design
  below ("The hard stop: `DiscardUnsaved`", superseded paragraph kept for the record).

- **Date**: 2026-11-24. **Branch** `etcd-safe-walfix-p6`, worktree `/shared/etcd-grove-p6`.
- **Done before this session**: the fork fix (`goose-lean-fmt1c-tornsave` @ `2bd3048d7`), the retranslation
  (`Code/.../storage/wal.lean`, `etcdserver.lean`), `examples/` go.mod, `etc/goose.py --check` green.
- **This session**: see "Progress" below (kept current at each milestone).
- **State (2026-11-25, session 5, end)**: `wal.Link` builds (real `lake build`, d6aa9cce3a); `#print axioms`
  of its 254 results = the `wal-fsext.txt` baseline, no `sorry` (`etc/tcb-report.py --check` needs a full
  worktree build: not run). E4's `Repair` done ("Repair with a pending run" below); `WAL__Save` fixed (the
  normalized op `wop`/`saveHS`, `stNil` in the entries loop's invariant). **Next: the WalTester consumers of
  `CloneStLaw` (`Adequacy.lean`: `walRaftP_cloneSt`, regenerate its Link with `etc/gen-link.py --durable`);
  `Unsaved`/`DiscardUnsaved` (new Go functions, unsaved.go, no spec yet: spec first); E5.**
- **Build**: every lake command takes `--packages=/shared/tmp/manifest-fce59af7.json`; builds through
  `/shared/tmp/build-slot.sh`; `export TMPDIR=/shared/tmp`.

## P6b (follow-up; not started)

1. **Incarnations in the WAL layer's ghost state** (for `DiscardUnsaved`; untrusted, reaches no
   top-level statement). The past states become pairs `(s, I)`, `I : GMap GoString Nat` the incarnation
   of each WAL directory, ordered by `absLe` on the directories whose incarnation is unchanged and
   `I ≤ I'`; `DiscardUnsaved`'s rename (`named := false`, the files under `wal.tmp`) and its parent fsync
   (the WAL gone) each bump `I !! dir` under the lock token; `Create` inserts at the current incarnation.
   The program's view (`walDirIs dir o`) carries its incarnation (exact: every discard goes through the
   program's update), and the persistent facts take it: `walNamed dir i`, `walSyncedLb dir i n`,
   `walPast`'s pairs (`walLenLb` through its handle, whose directory record gets the incarnation). The
   crash law keeps incarnations (a crash bumps none: a discarded WAL is absent or unnamed, and an
   unnamed one may come back only as the same incarnation's `wal.tmp`, which no reader reads).
   Then `DiscardUnsaved`'s spec (`true` ⇒ `walDirIs dir none` at the next incarnation; `false` ⇒
   unchanged) and proof (`Unsaved`'s, then `RemoveAll(wal.tmp)`, `Rename`, `syncDir`, as
   `Create`'s `renameWAL`).
   * Where: `GooseLang/Ext/AbsDisk/Specs.lean`'s generic `absPastAt`/`absPastAuth` are shared with the
     trusted extension's client vocabulary, so the WAL layer gets copies in `Ghost.lean` (not an edit of
     the generic ones, which would touch the extension). Then `Ghost.lean` (the order, `walGhost_*`),
     `Inv.lean`, `Crash.lean`/`CrashPure.lean`, `NamedView.lean`, the `*Lb` producers (`TailSync*`,
     `TailLenLb`, `CreateNamed*`, `ReadAll{Named,Synced,Commit}`, `Handle*`, `CloseHandle`), the specs
     naming the facts (`Create`, `WAL__Save`, `WAL__Sync`, `WAL__sync`, `WAL__ReadAll`, `Exist`,
     `Open*`, `WalViews`, `WalRecs`), and the tester (`member__save`/`__sync`/`__close`, `MemberRep`,
     `MemberInv`, `SaveAu`, `SnapAu`, its `Crash.lean`/`Inv.lean`, `restartRead`).
   * Refinements (2026-11-25, later): (a) the incarnation can be the WAL directory's **inode** `j`, which
     the layer already keys (`walDirKey dir j X`, `WalGS.γdk`, persistent elements): `Create` makes a fresh
     directory (its temporary one renamed in), so a re-created WAL has a new `j`; the past states then pair
     `s` with the map `dir ↦ j` of its WALs, and the facts take `j` (`walNamed dir j`, ...). (b) **Keep
     `walGhost s`'s and `walGhost_init`'s signatures** (the incarnation map existential inside `walGhost`),
     so that `Crash.lean`/`CrashPure.lean`, which P8 edits (`crashTo_start`/`CrashGood`/`walCrash_pure`'s
     exact-prefix conjunct, `walCrashWal`), need no change; if the crash view's past-state facts must carry
     `j`, tell the coordinator before editing them.
     **Checked: they must.** `Crash.lean`'s crash-view lemmas (lines ~1090-1230: the old generation's
     `walDiskAt`/`walSyncedLb`/`walNamed` carried to the new one through `walPast_ghost_le`) state and
     consume the facts, so their signatures change with the facts'; `CrashPure.lean` needs no change (pure,
     no facts). Asked the coordinator before editing `Crash.lean` (P8 edits `walCrashWal` there).
   * Size: the facts appear 330 times in 114 files (`walSyncedLb|walNamed|walLenLb|walPast|walDirIs|
     walDiskAt|walAbsent`); most uses only thread the new argument. Estimate 1,000-2,000 changed lines,
     of them 300-500 new (the ghost order and its laws, `DiscardUnsaved`'s spec and proof, 300-400);
     2-4 sessions.
2. **The tester without torn images** (P6 of the d6 plan; optional strengthening, deferred from P6: more
   than a session). Go: `walImgs` (`examples/etcd/wal/ref.go:198`) drops its `k` loop (only
   `h[:j]`, `n ≤ j ≤ len h`); retranslate (project `etcd-wal`); rerun the crash tests
   (`kpl_test.go`, `kn_test.go`, `robust_test.go`). Lean: the crash relation the tester sees must say
   prefix-only, so the WAL layer's `walStCrash` (`Ghost.lean`, today the trusted `absDisk_semantics.crash`
   with `walImg`'s torn disjunct) is restated with `walImgS` (`WalNorm.lean`; E2's producer already gives
   `d.H.take j`, `TailCrashW.lean`'s `tailImg_walImg` becomes its `walImgS` form), with its consumers
   (`CrashPure.lean`'s `walCrash` uses, `Abs.lean:941`, `BootPure.lean`); the tester's `tImgs`
   (`Defs.lean:201`), `tTornImgs`/`mem_tImgs`/`tImgs_complete` (`RefLemmas.lean`), `walImgs.lean`
   (337 lines, mostly the torn loop: shrinks), `Check.lean`'s `tHistWf_of_mem_tImgs`, its `CrashPure.lean`.
   Estimate 300-600 changed lines (net negative), 1-2 sessions with the Go crash tests.

## The design (decided in this session; the coordinator's E0-E5 plan)

The fork's Go behavior is `notes/etcd-dist-d6.md` §10. The Lean shape:

1. **Records of a `Save` (E0/E1).** `opDs (.save h es)` = the entry records, then the state record of
   `h` unless `es = [] ∧ hsEmptyP h` (was: unless `hsEmptyP h`). This is what Go writes only when the
   op is *normalized*: `Save(empty, es≠[])` writes `w.state`, the last saved state (`walLastHS` of the
   history before it). `WalNorm.lean`: `normOp p`, `normFrom p`, `normH` rewrite such a `Save` to
   `.save (walLastHS prefix) es`; every reader-side function is invariant (`walRead_normH`,
   `walReadCut_normH`, `walValidSnaps_normH`, `walCutPos_normH`, `walLastIdx_normH`,
   `walFoldChkFrom_normFrom`, ...). The encoding layer's history `histM d` (`wal/Abs.lean`) becomes
   `normH (d.H.map WalOpG.toM)`, so the per-op encoding (`opDs`, `segsDs`, `recsOfSegs`) is untouched in
   shape. `Save`'s append: `normH_snoc` (`histM` grows by `normOp (walLastHS H) o`). The specs of `Save`
   and `ReadAll` (over `d.H`) do not change.
2. **Crash images (E2).** The decoded records of a crash image are no longer the records of a history:
   they are `recsOfSegs` of the segments of `(histM d).take j` *followed by a run of entry records* (a
   prefix of operation `j`'s entries: a torn `Save`, now always followed by a state record that was
   lost). `histCut` (which produced `.save hsZero (es.take k)`) is replaced by "whole ops + trailing
   entry records". The ghost image chosen by the proved crash law is `I = H.take j` (`walImgS`: our own
   definition; `walImgS → walImg`, the trusted `walImg`/`walCrash` vocabulary of
   `GooseLang/Ext/AbsDisk/Impl.lean` untouched). The invariant must then allow, in the last segment, a
   run of entry-record frames after the history's frames (from `lay.z0`): `WalAbsD.tailStop` and
   `CrashTo`'s last clause become "from `z0` the decoder accepts a run of entry records, then stops"
   (`PendStop`), until a write-mode `ReadAll` zeroes from `pendOff = z0` (the old `ZeroToEnd` from
   `LastOffset`, same position).
3. **`ReadAll` (E3).** The Go loop's `pending` buffer: the result is the old fold (`readAllFold`) over
   the decoded records with the trailing run of entry records removed; on the records of a normalized
   history followed by pending entries, that is the old fold over the history's records (a normalized
   history's records never end with an entry record: every `Save` with entries ends with its state
   record). Write mode: the seek offset is `pendOff` (= `z0` when pending is nonempty, else
   `LastOffset`) and the encoder's CRC `pendCRC` (the chain's CRC after the history's records).
4. **E4**: `Repair` keeps the pending frames (it truncates after the last valid record);
   `ValidSnapshotEntries`/`OpenForRead` read past them; `Unsaved`/`DiscardUnsaved` new specs.
5. **E5**: the tester (`WalTester/`) keeps working with `walImgS → walImg`; dropping the torn images
   from Go `walImgs` is a strengthening, optional. `bootstrap.lean` / `MemberGen.lean` as the plan.

## E2 settled (2026-11-24): the crash image with pending entry frames

Checked against the fork's Go (`notes/etcd-dist-d6.md` §10, item 2: write mode zeroes from `pendOff`,
the offset before the first dropped record). No trusted text, no Go change; the shape:

1. **Producer** (`TailCrash.lean`'s `crashTo_tailL`): `tail_decode` gives the decoded `R.take j`, `R` the
   last segment's records `hdr ++ flatMap opDs (lastOps d)`. Split it by `flatMap_histCut`: whole ops
   `histCut Mr (lastOps d) n` and the entry records `histCutRest` (`histCutRest_entry`). The ghost image
   is **`I = d.H.take (segStart + (histCut …).length)`** (not `tailImg`'s `… ++ (histCut …).map toRaw`:
   the normalized ops are not `d.H`'s); `histN_take` gives `histM {d with H := I} = (histM d).take _`,
   and `walImgS_histCut` (compiled) the `walImgS`/`walImg` with `j ≥ d.m`.
2. **`CrashTo`'s last clause and `WalAbsD.tailStop` become `PendStop`**: from `S.length` (`S` the
   image's last-segment stream) the reader accepts the frames of `chainRecs (chainEnd …) ps` for some
   entry-only `ps`, then rejects. `ps = []` is the old clause. Consumers (`CrashPure`, the `ReadAll`
   decode, `Repair`, `ValidSnapshotEntries`) read `ps` as the trailing run that `readAllFoldP_append`
   drops.
3. **`TailPend` (registered tail, not yet zeroed; `TailCrashPend.lean`) and `LenZ`**: with pending frames
   the decoder's zero length word is at the end `e` of the pending run, not at `wr = z0`: `LenZ` moves to
   `e` and `TailPend` says `old` holds the pending frames on `[z0, e)`. A crash in that window, or in
   `ZeroToEnd`'s zeroing (the "zeroing crash"), now needs **W1** (today's `crashTo_tailP` needs none):
   a frame accepted at a pending position is, as of the sync, the pending frame (stamp-0 `old`), or, as
   of the zeroing change, all zeros, whose zero length word the reader rejects. So the accepted frames
   are a prefix of the pending run: `PendStop` again (`ps` a prefix). `W1G` is already a premise of
   `CrashOk`.
4. Appends happen only after a write-mode `ReadAll` zeroed from `pendOff = z0`, so `TailCands`/F-Z
   (`TailZeros` from `z0`) are unchanged for an appending generation.

## Progress

- E0: `Proof/go_etcd_io/etcd/server/v3/storage/WalNorm.lean` (normalization and its invariance lemmas).
- E0/E1 (written, **not yet compiled**; commits `ca99231ff5`, `f9e6cee809` and the stop commit):
  `opDs` (state record after the entries unless `es = [] ∧ hsEmptyP`), `histM d := histN d.H`, the
  scripted `segsOf (histN ·)` rewrite in the handle files, `SaveRecs`/`SaveAbs`/`SavePure`/`HandleAppend`
  over `wop`, `WalEncFold` with the normalization hypotheses (`hNo`; callers in `ReadAllOk` etc. not
  yet updated), `histCut` whole ops + `histCutRest` (`WalEncRecs`, `WalEncSegsImg`, `WalEncSuffix`,
  `ReadAllDecode`), `encodeState.spec`/`specNoErr` and their proofs, `saveState` as a wrapper,
  `walCov_encodeState` (`CalleeCov`). `WAL__Save.lean` not yet changed for the new branch (plan:
  `hs2 := saveHS (walLastHS (h.H.map toM)) hs es`; `hk`/`HI`'s room over `encState hs2`; `hroom1` and
  the `generalize` over `wop h.H`; `finEmpty` takes `⟨rfl, hse⟩`; a `wp_join (Q := executeVal ∗ handle
  at SaveFin ∨ returnVal ∗ err)` `at next` over `if len(ents) > 0 {…encodeState…} else {saveState}`,
  the inner `if IsEmptyHardState(st) { st = w.state }` joined at `∃ hp2, st ↦ hp2 ∗ P.hsIn hp2 hs2`,
  `w.state` from `walHandleIn_state` with `hc.st = walLastHS` by `Hs.st.trans hD.2`).
- E3 started: `Proof/.../storage/WalEncFoldPend.lean` (`raStepP`, `readAllFoldP`, `foldlM_raStepP_eq`,
  `readAllFoldP_append`: over records ending in a non-entry record followed by decodable entry records
  the new read is the old `readAllFold` of the former). Not compiled.

## Session 3 (2026-11-25): E2 done, E3's pure layer

What is proved now (all compile; `wal.Link` build log `/shared/tmp/p6-build4.log`):
- **E2.** `CrashPure`, `CrashStart`, `CutSynced`, `CutLay`, `SaveAbs`, `TailCrash`, `TailCrashW`,
  `TailCrashPend` (its `TailPend` crash is the `es = []` case: `pendStop_nil`), `TailSyncLayP`/`TailSyncWin`,
  `CreateAu`, `CreateHandle`, `CutHdrStream`, `CutAu`, `Append`, `HandleAppend`, `ReleaseTie`.
- **W1 for a pending run** (`TailCrashRep.lean`): `pendStop_transfer` (pure): a pending run of `old` from
  `off` carries over to a crash image that agrees with `old` on the core of every frame its reader accepts
  from `off` (W1) and whose bytes from `off` are `old`'s or zero (the padding: `frame`'s pad is zeros);
  the image's reader accepts a prefix of the run, then stops. `crashTo_tailR` (a repaired tail, `RepOld`)
  uses it: the accepted frame at any `p ≥ wr` is as of the sync (`old`'s) or stamped by a write, which
  `WinCands` excludes past `wr`. `crashTo_tailR`'s `himg` gained the "bytes from `wr` on are `old`'s or
  zero" conjunct (from `crashImg_tail` and `WinCands`, in `crashOkA_tailRep`). Helpers `acceptsFrom_ge`,
  `decStep_core_le`.
- **E3's pure layer.** `walReadFiles_running` (`ReadAllFiles`) and `walReadFiles_running_end`
  (`ReadAllEnd`, now one statement with the records, the end offset `wr + |pending frames|` and the CRC
  `crcAfter … (pendDs es)`), `walDecodeFiles_running_end` and `filesOk_running` (`FilesAtRun`) over a
  trailing run `Y`; `walRepairFile` (`RepairDecode`: the repaired file's records are the last segment's
  then the pending run; its frames end at `wr + |pending frames|`). `readAllFoldP_wal`
  (`WalEncFoldPend`): the new fold (`readAllFoldP`, with `pending`) on the WAL's records from any
  position then a pending run is the old fold on the former (`NoEntLast`, `EntsEnc`). `readAll_success`
  (`ReadAllPure`) now takes the `readAllFoldP` fold. `ReadAllOk` with `hNo`. `ReadAllLoop`'s
  `readFiles_dec`/`readFiles_md`, `ReadAllWFPure`'s `readFiles_hasMd` over the pending run.
- **`VsePure`** (`validSnapshotEntries`): `vseHs_opDs`/`vseHs_ops`/`vseHs_segsDs`/`vseOut_segs` take the
  normalization hypothesis (false otherwise: an op `.save hsZero es` with `es ≠ []` writes a state record
  in the encoding but not in `lhsStep`); `vseOut_pend`: trailing entry records change nothing.
- **Normalization invariance** (`WalNormDisk`): `walReleasePos_normH`, `walOpenPos_normH`,
  `walGuardPos_normH`, `walNameBound_normH`, `walRelGuard_normH`, `walLastSnapPos_normH`.

Left (failing in `wal.Link`'s build, or not yet reached):
1. **`WAL__ReadAll.lean`** (1,901 lines, E3 proper): the retranslated loop has `pending`, `pendOff`,
   `pendCRC` (Code `wal.lean:4927-5740`). The loop invariant `RdLoop` (`ReadAllLoop.lean`) folds `raStep`;
   it must fold `raStepP` (`WalEncFoldPend`) and carry `pendOff`/`pendCRC` (the offset/CRC before the first
   pending record). At the end: success via `readAll_success` (already over `readAllFoldP`); write mode
   seeks to `pendOff` (`= wr` by `walReadFiles_running_end`'s `es ≠ [] → z0 = |S|` and `RepOld`/`TailExact`;
   `LastOffset()` when `pending` is empty) and `ZeroToEnd` from there, and `hzw` (the zero length word) is
   at the decoder's end `wr + |pend|`, not at `pendOff`.
   **Design for `pendOff = wr` (2026-11-25, not started).** Backward reasoning from the end does not
   work (two start offsets can decode `k` records to the same end; decoded frame lengths need not be
   `|recFrames|`: decoding is not canonical). Forward instead: a relation `Reach C s s' n` (`n` accepted
   `goDecode` steps, the CRC through `rdCrc`, no rejected CRC record), deterministic. The loop invariant
   keeps `lastOff, lastCRC = off, c` (Go's `lastOff`/`lastCRC` at the loop head are the decoder's state),
   `Reach (fs₀,0,0) (fs,off,c) |acc|`, and, when `pending ≠ []`, a ghost `fsP` with
   `Reach (fs₀,0,0) (fsP,pendOff,pendCRC) (|acc| - |pending|)`, the last `|pending|` records of `acc`
   entry records decoding to `pending` and the record before them not one. At the end `|acc| - |pending|`
   is the number of the history's records (`readAllFoldP_wal`'s split: the history ends in a non-entry
   record, the pending run is entries), and a new lemma builds `Reach (fs₀,0,0) ([last], wr, tailCrc)`
   over that many records forward from the files' layout (`walDecodeFrom` over known frames, plus the
   step into the next file at a file's end); determinism gives `pendOff = wr`, `pendCRC` the chain's.
   `ReadAllIdx`: `w.enti` is set per applied (flushed) entry, so `raIdx` folds over the applied records.
2. **`TailPend` with a pending run** (`Abs.lean`, `TailCrashPend.lean`): a tail `ReadAll` registers before
   `ZeroToEnd` has `old` = the pending frames on `[z0, e)` and `LenZ` at `e`; its crash needs
   `pendStop_transfer` (the bytes from `z0` are `old`'s or a resize's zero: `WinShape`, writes excluded);
   `walTailsRes_registerPend` and `crashOkA_tailPend` change with it.
3. **E4 `RepairReg.lean`**: `walRepairFile` now gives `∃ rs es` with the frames ending at
   `wr + |pending frames|`; the registration states the tail at the decoder's stop (`(recFrames rs).length`,
   which was `lay'.wr`). Design: `Repair` truncates at `e ≥ wr` and keeps the pending frames; the
   registered layout's `wr`/`z0` stay at the history's stream end, the tail record's offset is `e` (the
   specs `os.File.Truncate.specRepTail`/`fileutil.Fsync.specRepTail` take the stream's length: they need
   the offset `e` with `old`'s bytes on `[wr, e)`). Not started.
4. Failing in the last `wal.Link` build besides `RepairReg`: `ReadAllIdx` (the `raIdx` fold of `w.enti`:
   with `pending`, `enti` counts only applied entries; goes with item 1), `StreamBound.saveStream_le`
   (done 2026-11-25: its bound is on `saveHS (walLastHS …) hs es`, the state written; no users yet), `SavePure.lean:252` (a syntax error in `SaveSt.finState`'s
   record), `WAL__cut.lean:484` (`iframe` of `walStIn … h1.stNil`). Items 1-3 and these are what the
   next session starts on. The spec appliers of `proto.MarshalPb.spec` (`pbutil.MustMarshalMessage*`,
   `encoder__encode`, `RaftModel/*`) build after the non-nil change.
5. Then the `encodeState`/`Save`/`LawsHs*` proofs (edited, unchecked), `ReadAll` provenance and
   `CloneStLaw`, `ValidSnapshotEntries`/`OpenForRead`, `Unsaved`/`DiscardUnsaved`, E5.

## Session 4 (2026-11-25): E3's `ReadAll` loop

- `ReadAllPure.lean`: `walFoldChkFrom_normFrom`, `walReadAt_normH`, `walReadAllOk_normH`/`_histN`
  (`readAll_success1` over `histN`).
- `ReadAllLoopP.lean`: `rdLoopP_flushStep` (one pending entry applied: the folds over `accA ++ accP.take
  (i+1)`), `rdLoopP_flushStart`, `rdLoopP_pend_len`, `rdLoopP_foldP_eof` (success fold `readAllFoldP`
  via `readAllFoldP_append`).
- `ReadAllWFPure.readAll_md_some` takes `recs = acc ++ accP` with `accP` entry records.
- `WAL__ReadAll.lean`: the loop invariant `HI` is `RdLoopP` with `pending`/`pendOff`/`pendCRC`/`lastOff`/
  `lastCRC`; the entry arm appends to `pending` (`rdLoopP_ent`, `pendOff`/`pendCRC` set when `pending` was
  empty); the other arms flush `pending` (an inline `wp_for` over `slice.forRange`, invariant `HF`: the
  index, `ents`, `w.enti`, the folds over `accA ++ accP.take jf`; its body is the old entry arm, the
  `ErrSliceOutOfRange`/reopen returns needing a second `wp_for_post` for the outer loop), then
  `pending = pending[:0]`, `st1`/`ix1` (the flushed state, rewritten into the context), the switch arms on
  `rdLoopP_rec`, `LastOffset`/`LastCRC` after the switch. The write-mode exit: `rdLoopP_eof_wal` gives the
  pending run `es`; `hoffE`/`hcrcE`: `endOff`/`endCRC` (`if pend = [] then LastOffset/LastCRC else
  pendOff/pendCRC`) are `lay.wr` and the chain's CRC in both cases (forward determinism, `DecReach`); the
  two `if len(pending) > 0` joins by `wp_wand`.
- **Item 2 is now the blocker of the write-mode exit**: `walTailP_ofRead` takes the zero length word at
  `wr` (`hzw`), proved only when `pend = []`; with a pending run the bytes at `wr` are its frames
  (`ZeroToEnd` then zeroes them). `hzw`'s `pend ≠ []` case is a `fail` marker in the proof.
- **`w.state`'s provenance** (`iframe … P.hsIn p' st.hs` at the handle, the `walStIn` slot): the
  `CloneStLaw` plan above (Session 3's "Where `walStIn` comes from").

### Item 2 design (session 4, started)

The lent tail (kind `false`) a `ReadAll` with a pending run hands to `ZeroToEnd` has no zero length word at
`wr` (`LenZ` fails: the pending frames are there), so `TailPend` (= `wr = z0 ∧ LenZ`) cannot hold. What the
crash argument needs instead is what a repaired tail already has: `RepOld` (`wr = z0`, the stamp-0
candidates from `wr` on are `old`'s, the segment no longer than `old`), with `crashTo_tailR`/
`crashOkA_tailRep` (W1 + `pendStop_transfer`: every crash image's reader accepts a prefix of the pending
run, then stops). Plan: **`TailPend` becomes `RepOld`** (the registered tail has it: `TailLast.repOld`; the
registered kind-`true` tails already carry `TailZeros ∨ RepOld`), and the `LenZ` uses are replaced:
`crashOkA_tailPend` by `crashOkA_tailRep`, `rzStart_pureP` by `rzStart_pureR` (+ `repOld_rzCands`), the
landing by `repOld_rzLand`, `tailPend_tailLay` (which used that `TailPend` reads only `old`/`z0`/`wr`) by
`RepOld` preservation per step: new lemmas for the growth (`rzGrow`/`rzLandG`: the grown bytes' candidates
are those `pcRun` knew, stamp-0 values kept; size ≤ `k = |old|`), the fdatasync (`syncLayP`: the synced
tail exact, `TailLast.repOld`), and the generic step of `walInvBody_tailW` (`TailAccW.lean:269`: with
`wr' = wr` it kept `TailPend` because `tailLay` keeps `old`; with `RepOld` the caller must supply it: only
resizes and the sync act on a pending lent tail). `ZeroToEnd.specWalTail`/`walTailP_ofRead` then drop the
zero-word premise (`TailLast.repOld` instead of `lenZ_of_tailLast`).

**Refined (same session), being implemented:**
1. `TailPend` := `RepOld`'s formula (done, `Abs.lean`; `tailPend_iff_repOld`). `TailRK (some (_, false))` is
   now `TailZeros ∨ TailPend` (a lent tail's step must keep it; `TailAccW`'s lent `ZerosOk` proof uses it).
   `rzStart_pureK` false case = true case (`rzStart_pureR`). Deleted: `WalAbsD.pendVals`,
   `crashOkA_tailPend` (`TailCrashPend`), `tailPend_tailLay`, `tailCrashStep_rzStartP`, `rzStart_pureP`
   (`TruncSupPend`).
2. The failure path (`ZeroToEnd` fails, `Close` syncs: `syncLayP`, `old` := the synced values from `wr`)
   needs the static `tailStop` of `syncLayP`: a `PendStop` of the handle's values at `wr`. It goes in the
   handle: `TailMetaE` gets `Mr` and the chain CRC (`tailCrc Mr H md cuts`) and its last conjunct becomes
   `PendStop walCodec Mr (bs.map (·.1)) o0 c` (was the zero length word); `walTailPE` gets `Mr`.
   `ZeroToEnd`'s first step derives it from the invariant (exact tail: handle values = `old`; `tailStop`
   with `z0 = wr = |S|`, or F-Z: zero word); its internal states keep it (`pendStop_congr`: values from
   `o0` unchanged, or all zero: `decStep_zeroWord`).
3. `TailSyncLayP`: `hlw` → that `PendStop`; `crashOk_syncP` over `crashTo_tailR` (not `crashTo_tailP`).
4. `GrowSup`: `TailRK (some (k, false))` for the grown layouts: `RepOld` kept by a growth (new lemmas).
5. `specWalTail`'s pre drops the zero word; `walTailP_ofRead` drops `hz`; `WAL__ReadAll`'s marker goes.

## Session 5 (2026-11-25): item 2, `CloneStLaw`, the Link

- **Item 2 done** (`c18dbe98ed`): `TailPend` is `RepOld`'s formula; the failure path's handle carries
  `PendStop` (`TailMetaE Mr c`, `walTailPE Mr`); growth keeps `RepOld` (`repOld_rzGrow`, `repOld_rzLandG`).
  **Removed premise** (ours, proved spec): `ZeroToEnd.specWalTail`'s pre no longer takes the zero length
  word at `wr` (`walTailP … k true TailMetaR`); `walTailP_ofRead` drops `hz`.
- **`CloneStLaw`** (`e1bd2afbaa`): `WalPbIn.CloneStLaw P Mr HsO` (`ReadAllCallees.lean`): `proto.Clone` of
  an owned hard state (`HsO`) gives both pointers frozen at `h`, the clone non-nil and `walStMarsh`. It
  replaces `CloneHsLaw` as `ReadAll`'s hypothesis (`CloneHsLaw` stays, unused by `ReadAll`). Proved for the
  raftpb instance: `walRaftP_cloneSt` (`RaftModel/LawsHsMarshal.lean`) over `proto.ClonePb.spec` and
  `proto.MarshalPb.spec` (the owned source is canonical, `walRaftHsO`). No loop-invariant tracking was
  needed: `HsO` is already canonical. A law hypothesis, no axiom.
- `5054fab591`: `Link.lean` regenerated (`h_WalPbIn_CloneStLaw`, `h_WalPbIn_ZeroStLaw`, `wp_encodeState*`);
  `SavePure:252` was a struct-instance continuation line left of its first field (`checkColGe`);
  `WAL__cut`: `saveState.specPre` takes `P.hsIn` (out of `walStIn`), and `h1.stNil = h.stNil`.

### Repair with a pending run (E4, done 2026-11-25)

`walRepairFile` returns the pending run `es`: `(recFrames rs).length = lay.wr + |pendFrames es|`
(`es ≠ [] → z0 = wr`), and now also the reader's stop at `wr` on the bytes below `LastOffset`
(`PendStop`) and, past `wr`, a nonzero byte of the run's first length word (`frames_nz`). `Repair`
truncates at `tg = |recFrames rs| ∈ [wr, size]` (repair.go:86); the run stays in the file. Done:
1. `repair_register`: the tail record at `lay'.wr` (the stream's end), `wr ≤ tg`, `TailMetaRP Mr (tailCrc …)
   wr tg` (`TailMetaR`, the nonzero byte, the stop) — `RepairTailDefs.lean`.
2. `os.File.Truncate.specRepTail` at target `tg` (pre `TailMetaRP`, post `TailMetaRWP`: `TailMetaRW`,
   `wr ≤ size`, the stop); `walTailPO` no longer carries `LoWr`. Supply `walTail_truncSupR`
   (`TruncSupRep.lean`): the tie `repTie` carries the caller's half of the run's nonzero byte (`repNZ`), which
   with F-Z contradicts `WalAbsD.zeroPast`; `RepOld` starts via `rzStart_pureRT` (`RzRep.lean`); the state
   property `RepP` (size `S0` or `tg`, `LoWr` at `tg = wr`), so `os.File.Truncate.specAu`'s closure was
   widened (`m'.size = m.size ∨ m'.size = sz`, ours, proved).
3. `fileutil.Fsync.specRepTail`: over `wp_tailFsyncPE`/`walInvBody_syncPE` (`syncLay_anyE`: F-Z, or
   `TailPend` = `RepOld` with `syncLayP`), generalized over the token's kind; the post gives the pending token
   back (`∃ k'`), not the key (no F-Z past a run).
4. `walInv_repairPut` (moved to `UnregLent.lean`) unregisters by the token (`walInvBody_untailL`).
   `walInvBody_untailR` (`RepairPut.lean`) and `RepairSync.lean` became unused: both files deleted.

## The hard stop: `DiscardUnsaved` needs two abstract-disk steps (2026-11-25, open)

`wal.DiscardUnsaved` (fork `unsaved.go:97`) renames `dir` to `dir.tmp` and fsyncs the parent, so its spec's
success post must be "no WAL at `dir`" (`walDirIs dir none`, what `wal.bootRes`'s "no WAL, possibly
`wal.tmp`" is built from). The trusted abstract disk (`GooseLang/Ext/AbsDisk/Impl.lean`) cannot reach that
state:
* no `AbsDiskStep` removes an entry of `s.wal` (`"WalCreate"` inserts; every other step goes through
  `absDiskUpd`, which keeps the entry);
* a crash keeps an absent WAL absent (`absDisk_semantics.crash`'s last clause), and `walCrash` lets a WAL
  vanish only when `named = false`, which no step sets (`"WalNamed"` only sets it `true`).
Between the rename and the parent's fsync a crash may keep the WAL at `dir` (the rename lost) or lose it
(the rename durable): the abstract WAL must be one that "may vanish" there, and absent after the fsync.

**Proposed** (superseded the same day, see START HERE: not needed, the fsExt WAL uses no step): two steps, mirroring `Create`'s rename/fsync pair in reverse:
`"WalUnnamed"` of `dir` (`named := false`, at the rename: `walCrash`'s first disjunct then covers the
rename made durable, its second the rename lost) and `"WalDiscard"` of `dir` (the entry deleted, at the
parent's fsync, after which the rename is durable). No change to `walCrash`, `walImg` or the crash clause.

1. **Minimal program that needs it**:
   ```go
   w, _ := wal.Create(lg, dir, md); w.Close()    // a WAL that holds nothing a Save wrote
   if ok, err := wal.DiscardUnsaved(lg, dir); err == nil && ok && wal.Exist(dir) {
       panic("discarded WAL still there")
   }
   ```
   Its proof needs `walDirIs dir none` after `DiscardUnsaved` (`Exist`'s spec answers from `walDirIs`). With
   the existing steps the abstract entry of `dir` stays `some d` (no step deletes it), while the WAL
   invariant (`WalsOk`) ties every entry to a directory at `dir` holding its segments, which the rename
   removes: no state of the invariant fits after the rename. Searched: `AbsDisk` is this repository's
   extension (Perennial has no WAL model); its `Specs.lean` has no removal lemma, and none can exist since
   the steps are the only transitions.
2. **The real code has it**: etcd fork `goose-lean-fmt1c-tornsave` (`2bd3048d7`),
   `server/storage/wal/unsaved.go:97` `DiscardUnsaved` (`os.Rename(dir, dir+".tmp")`, then
   `syncDir(filepath.Dir(dir))`), called by `server/etcdserver/bootstrap.go:82` `bootstrap` before
   `bootstrapBackend`, `haveWAL = !discarded`.

`Unsaved` (read-only, a decode loop like `validSnapshotEntries`) needs no semantics change. Proposed spec
(not yet written): `ValidSnapshotEntries`'s binders; post `b = true → err = nil ∧ ∃ d, o = some d ∧
∀ op ∈ d.H.map WalOpG.toM, walOpBlank op` (`walOpBlank`: `.save h []` with `hsEmptyP h`, or `.snap m _` with
index 0: what Go accepts), with a pure lemma that every crash image `H.take j` of such a history is blank
(prefix-closed). "Reads `walFresh`" (server level, P5) needs in addition that no `SaveSnapshot` at index 0
carries a nonzero term (raft never saves an empty snapshot: `IsEmptySnap`), a server-side fact.

## The hard stop: `proto.Marshal` of an empty hard state (needs a trusted-spec change)

**Resolved 2026-11-25:** Upamanyu approved the change (#8, 00:38Z). `proto.MarshalPb.spec`'s post now has
`⌜l ≠ null → d ≠ slice.nil⌝` (no new premise); `proto.MarshalPbNonNil.law` is deleted, and
`walRaftP_marshSt`/`walRaftP_zeroSt`/`walSrvP_zeroSt` take `proto.MarshalPb.spec`. The axiom
`proto.MarshalPb.wp_proof` keeps its name (the tcb baseline lists names). What follows is the history.

`Save(st, ents)` with `ents ≠ []` and `st` empty now writes `encodeState(w.state)`, and `w.state` can
be the empty hard state (a WAL with no state record yet: `Save` sets `w.state = &raftpb.HardState{}`,
wal.go:1345-1347). `encodeState` marshals it: `pbutil.MustMarshalMessage(s)` = `proto.Marshal(s)`
(pbutil.go:53-58), and builds `&walpb.Record{Type: …, Data: b}`. `walpb.Record` is proto2 with
`optional bytes data = 3` (record.proto:1,11): a nil `Data` is not encoded, a non-nil empty one is
(field 3, length 0). The frame bytes therefore depend on whether `b` is nil.

1. **Minimal program and the failed proof.**
   ```go
   st := &raftpb.HardState{}
   b, _ := proto.Marshal(st)                         // non-nil empty in protobuf-go
   out, _ := proto.Marshal(&walpb.Record{Type: proto.Int64(3), Data: b})
   if len(out) != 4 { panic("Data's presence") }    // 2 bytes for Type, 2 for an empty Data
   ```
   The `encodeState` proof needs `d ≠ slice.nil` for `recBytes v.Data' (some [])` (`encRecIn`,
   `walpb/PbRecord.lean:97`); for a non-empty state `MarshalHsLaw` gets it from the encoding's length.
   `proto.MarshalPb.spec`'s post is `d ↦* pbEncC I c ∗ ownSliceCap w8 d (DFrac.own 1)`, which a nil
   slice satisfies when the encoding is empty (Perennial's `ownSlice_nil`, `ownSliceCap_nil`,
   `Golang/Theory/Slice.lean:118,326`); no other `proto` spec here says more (`Spec/google_golang_org/
   protobuf/proto/`). Its docstring already claims "an empty encoding is a non-nil empty slice".
2. **The real code.** protobuf-go v1.36.11 `proto/encode.go:119-146`: `Marshal` returns
   `emptyBytesForMessage(m)` for an empty encoding, `emptyBuf[:]` (non-nil) for a valid message, nil
   only for an invalid one (a nil `*T`). etcd: `server/storage/wal/wal.go` `(*WAL).encodeState` called
   from `(*WAL).Save` at fork `2bd3048d7` with `st = w.state` (non-nil pointer, possibly empty).

**Proposed change (for the coordinator / Upamanyu):** `proto.MarshalPb.spec`'s post gains
`⌜l ≠ null → d ≠ slice.nil⌝` (or the premise `l ≠ null` and `⌜d ≠ slice.nil⌝`), axiom
`proto.MarshalPb.wp_proof` in `etc/tcb-baseline.txt`; then `WalPbIn.MarshalHsLaw` drops `¬ hsEmptyP hs`
for `hp ≠ null` (proved in `RaftModel/LawsHsMarshal.lean` from the stronger post). Alternative without
the trusted change: none found (the encoding layer must know whether the empty state's `Data` is
present; a `Save` spec premise excluding an empty `w.state` would add a premise up to the top-level
theorems).

### Coordinator's answer (2026-11-24) and what it implies

(2) approved: keep going with the non-nil fact as an undischarged hypothesis, one `abbrev … .law : Prop`
in a defs module; never edit `proto.MarshalPb.spec` or the tcb baseline. (1) is with Upamanyu (#8).

**Finding while designing it: `MarshalHsLaw` without `¬ hsEmptyP` is false for the instance.**
`walHsIn` (`RaftModel/Pb.lean:106`) admits, for an empty state, any content of that model: raft's
`Ready.HardState` is `⟨some 0, some 0, some 0⟩` when empty (`walHsIn_of_hsOptC`, `RaftModel/Srv.lean`),
whose encoding is not `[]` (explicit zero fields). Such a pointer is never written (`saveState` skips
it, `Save` replaces it by `w.state`), but a law over every `hsIn` pointer would claim its encoding is
`encState hsZero = []`. What is true is narrower: **`w.state`'s content is canonical** (all-absent when
empty): it is assigned only `&HardState{}` (wal.go:1346, :542 then `proto.Clone`, :747), a state decoded
from a record (canonical: our records are canonical encodings or `[]`), or a non-empty `st`
(`encodeState`, canonical by `walHsIn`).

Design (to implement): the handle holds, for `w.state`, `walStIn P Mr sp h.st := P.hsIn sp h.st ∗
walStMarsh Mr sp h.st` in the slot of `P.hsIn sp h.st` (one hypothesis, so `walHandleIn`'s `icases`
patterns do not change), where `walStMarsh Mr sp hs` is the persistent triple "`MustMarshalMessage(sp)`
returns a non-nil slice of `Mr.encState hs`". `encodeState` takes `walStIn` of its argument (no marshal
law); `saveState` builds it from `MarshalHsLaw` (non-empty); `Save`'s fresh `&HardState{}` and
`ReadAll`'s `proto.Clone` of the empty/zero state build it from one new WalPbIn law, proved for the
instance from `proto.MarshalPbNonNil.law` (the strengthened `Marshal` spec as an `abbrev`, the single
place the approval discharges).

**Where `walStIn` comes from (worked out 2026-11-24, partly implemented):**
- `Handle.lean`: `walStMarsh`, `walStIn` (`P.hsIn ∗ (sp ≠ null → walStMarsh)`), `walStIn_null`; the
  handle's `w.state` slot is `walStIn` (`Handle.lean`, `CloseHandle.lean`, `SaveHandle.lean`'s
  `walHandleIn_state`, `CreateHandle.lean`'s premise; `Create.lean` builds it from `NilLaw` with
  `walStIn_null`: `Create` leaves `w.state` nil). Not compiled yet.
- `saveState(s)` (non-empty `s`, also `cut`'s `saveState(w.state)`): `walStMarsh` from `MarshalHsLaw`
  (its post already says non-nil). No new law.
- `Save`'s `w.state = &HardState{}`: a new law `WalPbIn.ZeroStLaw P Mr` (as `ZeroLaw.2` with
  `walStMarsh Mr p hsZero` added), discharged for the instance from `proto.MarshalPb.spec` (non-nil since 2026-11-25).
- `ReadAll`'s `w.state = proto.Clone(state)`: **needs provenance tracking** in the loop. `proto.Clone`
  copies the content with its presence bits, and `walHsIn` admits non-canonical empty contents, so a
  law over any `hsIn` pointer is false. True: `state` is `&HardState{}` or `MustUnmarshalState(d)` of a
  record's data, and on the ok path the last state record's data is `Mr.encState (walLastHS …)`
  (records = the history's). Plan: the loop invariant keeps `bsSt : Option (List w8)` (the data
  `state` was unmarshalled from, `none` = the zero alloc) and the unmarshal law's post adds
  `⌜bs = Mr.encState h⌝ -∗ canonical`; at the end `bsSt` is the last state record's data, which
  the decoding lemmas equate to `Mr.encState`; a `CloneStLaw` carries `walStMarsh` through `Clone`.
  Both laws discharged in `RaftModel/` from `proto.MarshalPb.spec` (and the unmarshal model).

**Second finding: `encodeState(w.state)` needs `w.state ≠ nil`, which the handle forgets.** `Save`
checks `w.state == nil` at its top, but the loop over the entries closes the handle, whose `w.state`
slot is existential: when the entries are done and `Save` loads `w.state` again, nothing says it is
not nil (and `encodeState(nil)` would marshal to a nil slice, a record without `Data`). `Create` leaves
`w.state` nil, so the slot cannot just say non-nil. Planned: the slot becomes `walStIn P Mr sp h.st ∗
⌜sp ≠ null ∨ ∀ o ∈ h.H, o is a snapshot⌝` (one hypothesis, a def `walStH P Mr sp h`); only the proofs
that change `h.H` re-prove it (`walHandleIn_append`: a `Save` needs `sp ≠ null`, which `Save` has from
its nil check; `SaveSnapshot` keeps the disjunct; `Create`: only snapshots; `ReadAll`: `CloneStLaw`
gives a non-nil clone). In progress in `WAL__Save.lean` (the `w.state == nil` join now carries
`walStIn` and `sp' ≠ null`; the `len(ents) > 0` branch not yet written).

**Implemented (2026-11-24, still uncompiled at this point):** `WalHS.stNil : Bool := false` (only `createHS`
sets it); `walStIn P Mr sp hs nil` (`hsIn ∗ (sp ≠ null → walStMarsh) ∗ (nil = false → sp ≠ null)`) in the
handle slot as `walStIn P Mr sp h.st h.stNil`, with `walStIn_null/_intro/_set/_nn`; `walHandleIn_stateNil`
(`SaveHandle.lean`: back with a new flag); `Save` clears it at its nil check and keeps `hc.stNil = false`
in the entries loop (`Hnil` in `HI`); the `len(ents) > 0` branch (`wp_join (Q := …) at next`, the
inner `IsEmptyHardState` join at `walStIn hp2 (saveHS …)`), `saveState` otherwise. New hypotheses of
`Save.wp_proof`: `wp_encodeState`, `wp_encodeStateNE`, `wp_marshal` (`MarshalHsLaw`), `hzst`
(`ZeroStLaw`). Laws: `proto.MarshalPb.spec` (non-nil post, approved 2026-11-25), `walRaftP_zeroC` (`LawsHs`), `walRaftP_marshSt`/`walRaftP_zeroSt`/`walSrvP_zeroSt`
(`LawsHsMarshal`). Still to do there: `ReadAll`'s provenance and `CloneStLaw` (above), the Links.
