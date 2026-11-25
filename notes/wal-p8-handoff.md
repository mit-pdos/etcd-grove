# P8 (etcd_safe #50, D6-T5): the WAL after a crash, giving `srvFiles` and `walReadFacts` — handoff

## START HERE

- **Date**: 2026-11-25 (session 2). **Branch** `etcd-safe-p8`, worktree `/shared/etcd-grove-p8`; P6's
  re-pin (`etcd-safe-walfix-p6` @ `2c17304ea8`) merged (`97cfd9142a`).
- **Build**: the remote hosts (`FKLEAN_HOST=fk-lean2 /shared/tmp/fklean1-check.sh /shared/etcd-grove-p8
  etcd-safe-p8 TARGETS`; the branch's worktree lives on the host it was seeded on, so keep the host). fk-lean1
  has too little disk to seed (37 GB free, 2026-11-25). Locally: `export TMPDIR=/shared/tmp`,
  `--packages=/shared/tmp/manifest-fce59af7.json`, `/shared/tmp/build-slot.sh`.
- **Commits** (each revertible on its own):
  - (1) `8244ae66c1` + fix `1dce32d84a`: `CrashPure`'s `crashTo_start`/`CrashGood`/`walCrash_pure`
    return the whole-operation image `walImgS` (`walStCrashS`); `walCrashWal` is over `walStCrashS`, so
    `walInv_crash` gives it, and **`walInv_crashS.law` is gone** (`walCrashWalS` too: `CrashS.lean` keeps
    `walImgS_mono` and `walDiskAt_crash_keepS` over `walCrashWal`). Coordinator's decision (1).
  - (2) `cb9d0ce180`, a proposal to coordinator-E: `InvCrashImage.lean`/`CrashInterim.lean` (copied from
    `etcd-safe-crash/2026-11-24` @ `05926dc6af`) with `srvFilesC` in `srvCrashImageAt`,
    `bootstrapCrashContract`'s pre and C-I2.
  - (3) `64aa0b94eb`, a proposal to coordinator-E: `WalRecsH.lean`, `InvWalCrash.lean`,
    `InvWalCrashLaws.lean` (copied from `etcd-safe-d6t2/2026-11-24` @ `efd5966fe4`, T2's WIP) with
    `walRecsH_crash`, `HistReadOk` in `rnDurBodyK`, the crash law's callback returning `j` and a wand on
    `walRead (Hs.take j) = some σ`, and `walReadFacts σ` in its post.
  - (2) and (3) carry copies of the D6 branches' files: integrating them with those branches is an add/add
    conflict per file; take this branch's version or reapply the diff of the commit.
- **State / Next**: see "Progress" and "Left".

## What T5 delivers, and to whom

The consumers (none of their statements is fixed; all on unlanded D6 branches):

- **T2** (P5, #51, branch `etcd-safe-d6t2/2026-11-24`, `InvWalCrash.lean`): `rnDurK_crash.law` takes a
  callback that, given the WAL's records with their history (`walRecsH h σr Hs true`, T2's
  `storage/WalRecsH.lean`) and a synced mark `walSyncedLb h.dir n`, gives them back with a crash prefix
  `j` (`n ≤ j ≤ |Hs|`), its read `walRead (Hs.take j) = some σ` and the caller's `Φ σ`.
- **T4** (P2, `etcd-safe-d6t4b/2026-11-24`, `InvCrashImage.lean`, `NewServerCrash.lean`): the crash image
  `srvCrashImageAt` carries `srvFiles dd id σ D` and `walReadFacts σ` (in `wal.crashImage`), and
  `bootstrapCrashContract` takes both.
- **T7** (`dist/crash/MemberCrash.lean`, not started): assembles `memberGen_crash.law` from
  `walInv_crash`, T2's crash law, the backend's A1 and T6.

What this branch provides (all proved; no axiom, no `sorry`):

| file | what |
|---|---|
| `Proof/.../storage/WalCrashRead.lean` (pure) | I1-I4 of any read `walRead I = some σ` (`walRead_wf`, `walRead_last_le` from `walIdxLe B I`, `walRead_b_le_commit`, `walRead_commit_le_last` from `walCommitLe I`, `walRead_snapBase`); the two history conditions pass to prefixes (`walIdxLe_take`, `walCommitLeFrom_take`, `walCommitLe_take`) |
| `Proof/.../storage/wal/CrashPure.lean`, `Crash.lean` (P6's, edited by decision (1)) | `walStCrashS` (`walStCrash` and every new history a prefix `walImgS` at the old synced mark); `walCrashWal` over it, so `walInv_crash` gives whole-operation images |
| `Proof/.../storage/wal/CrashS.lean` | `walImgS_mono`, `walDiskAt_crash_keepS` |
| `Proof/.../storage/WalRecsH.lean` (T2's, commit (3)) | `walRecsH_crash`: `walFilesC_crash` on the unfolded `walRecsH` |
| `Proof/.../storage/WalRecsCrash.lean` | `walFilesC` (the files a crash left: `walFiles` without the synced mark), `walFiles_walFilesC`, **`walFilesC_crash`** |
| `Proof/.../etcdserver/SrvCrash.lean` | `walReadFacts_of_read`, `walReadFacts_of_take`; `srvFilesC`, `srvFiles_srvFilesC`, `srvFilesC_dataDir_len` |

How T7 composes them: `walInv_crash` gives `walCrashWal W W'` (now with whole-operation images),
`walUnlockedTok (W := W')`; the program's boot gives the directory's call permission half. T2's
callback is `walRecsH_crash h W' σ Hs n id cid hmd` (commit (3)), with `Φ σ := walFilesC {h.toWalA with W := W'} id cid σ
true ∗ …`; `walReadFacts σ` from `walReadFacts_of_take` once T2's invariant keeps the two history
conditions (`HistReadOk`, commit (3)).

## Proposals to the consumers (made on this branch: 1 = commit (2), 2 and 3 = commit (3); for coordinator-E)

1. **`srvFilesC` in the crash image** (T4's `srvCrashImageAt`, `bootstrapCrashContract`'s pre, C-I2's
   law): `srvFiles` → `srvFilesC`. Why: `walFiles` says every operation of the history is synced
   (`walSyncedLb a.dir |H|`), what `Close` leaves; a crash keeps the abstract synced mark (`walCrash`: `m`
   unchanged), so the new generation's state is synced only to the old mark, though every byte on disk
   is durable. Nothing on the restart path needs the mark (`Open`/`ReadAll` take none; write-mode
   `ReadAll` syncs and returns `walSyncedLb dir |H|`), so the contract over `srvFilesC` is as true of Go
   as over `srvFiles`, and the graceful image is an instance (`srvFiles_srvFilesC`). The alternative
   (keep `srvFiles`) needs a WAL ghost step at boot raising the mark to `|H|` (the start layout is
   durable: `WalAbsD.synced` holds at `m = |H|` since `so = z0 =` the stream's end, but the invariant's
   crash condition `CrashOk` must be re-proved at the higher mark: P6-depth work in `walInv_alloc`'s
   start; not attempted).
2. **T2's crash law's callback**: `walRead (Hs.take j) = some σ` cannot come from the WAL (a prefix's read
   may fail: `readEnt` out of range); it comes from T2's own `CrashReadsHold Hs n`. `walFilesC_crash`
   returns `∃ j, ⌜n ≤ j ≤ |H|⌝ ∗ ∀ σ, ⌜walRead … = some σ⌝ -∗ walFilesC …`, so T2's callback should return
   `∃ j, ⌜n ≤ j ≤ |Hs|⌝ ∗ ∀ σ, ⌜walRead (Hs.take j) = some σ⌝ -∗ Φ σ` (the law then picks `σ` from
   `CrashReadsHold`), or take `CrashReadsHold` as the callback's premise.
3. **T2's invariant keeps the two history conditions**: `walIdxLe (2^61 - 1) Hs` (raft's room: every
   saved entry and snapshot index) and `walCommitLeFrom walFresh Hs` (every `Save`'s hard state has
   `commit ≤ last` of the records after it: raft's `committed ≤ lastIndex`). `walReadFacts_of_take` then
   gives `walReadFacts σ` of every crash prefix whose eager fold has `b ≤ commit` (StorageHolds' `σ.b ≤
   σ.commit` is of the read, not of the eager fold; with `walRead_of_fold` the two agree when the eager
   fold has it). Alternatively T2 keeps `walCommitLe (Hs.take j)` for each `j ≥ n` beside
   `CrashReadsHold`, and `walReadFacts_of_read` applies directly.

## The P6 change (done, commit (1))

`crashTo_start` returns `walCrash d (some d') ∧ walImgS d.H d.m d'.H`; `CrashGood`'s first conjunct carries
`∀ d', o.map Prod.fst = some d' → walImgS d.H d.m d'.H`; `walCrash_pure` returns `walStCrashS s s'`
(defined in `CrashPure.lean`); `walCrashWal` is over `walStCrashS`, and its `_keep` lemmas take `hc.1`
(`walCrash_view_keep` still returns `walStCrash`). No trusted text: `walImg`/`walCrash`
(`GooseLang/Ext/AbsDisk/Impl.lean`) unchanged.

## `HistReadOk` (commit (3)): why per prefix

`HistReadOk Hs n := walIdxLe (2^61-1) Hs ∧ ∀ j, n ≤ j → j ≤ |Hs| → walCommitLe (Hs.take j)`, not
`walCommitLeFrom walFresh Hs`: a received snapshot's `SaveSnap` precedes the `Save` that covers it, so between
the two the eager fold has `b > commit`, so `walCommitLe_of_fold` (whose premise is the fold's `b ≤ commit`)
cannot turn the eager form into the reader's there, though every prefix's read is fine. (Corrected by P5,
2026-11-25: `walCommitLeFrom` itself, `commit ≤ last` along the eager fold, does not fail there: every `SaveSnap`
keeps it, `walSaveSnap_commitLe`, `walCommitLeFrom_snoc_snap`; what fails is `b ≤ commit`.) T2
must keep `HistReadOk` in its step proofs (each `Save`/`SaveSnap` appends; the crash point only grows) and
prove it at allocation (`rnDurK_alloc.law` takes it as a premise).

## Progress

- 2026-11-25 (session 1): read the D6 design and T2/T4's statements, then wrote the four files above. A
  targeted `lake build` of the four modules succeeds (`/shared/tmp/p8-build1.log`); `import-all-check` and
  `tier-check --check` pass (all four are defs tier). No axiom and no `sorry`: `walInv_crashS.law` is an
  `abbrev` that nothing uses yet. Coordinator, 2026-11-25: P6 re-pins to fork `goose-lean-fmt1c-crashfixes`
  @ `e94f33b50`; merge it when pushed. The WAL crash facts rest on W1 only; stale-byte tears are out of scope.

- 2026-11-25 (session 2): coordinator decisions (1)-(3) made as commits (1)-(3) above. The first remote build
  (fk-lean2) found two source errors in (1) (a header comment, a projection), fixed in `1dce32d84a`. Pushed up to
  `1dce32d84a` first, for P6b (who adds an incarnation argument to `Crash.lean`'s crash-view lemmas) to merge.
  The copies in (2)/(3) needed adapting to the merged base: `envVerifyOff` → `⌜EtcdVerifyOff⌝` (InvCrashImage,
  CrashInterim), and in `rnDurK_crash_law_holds` `iunfold rnTakenK`, `hE2 p hp` and `dsimp only [durOf]`
  per case. Remote build on fk-lean2 (fresh seed): `wal.Crash`, `wal.CrashS`, WalTester's `wal.Crash`,
  `WalRecsCrash`, `WalRecsH`, `SrvCrash`, `InvCrashImage`, `CrashInterim`, `InvWalCrash`,
  `InvWalCrashLaws` all build; no axiom, no `sorry`; `import-all-check`, `tier-check --check` pass.

## Left

- T2: maintain `HistReadOk` in the step proofs and at allocation (commit (3)).
- Integration of (2)/(3) with the D6 branches (add/add).
- T7 wiring (the coordinator's C8) over these lemmas.
