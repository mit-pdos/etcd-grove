# P8 (etcd_safe #50, D6-T5): the WAL after a crash, giving `srvFiles` and `walReadFacts` — handoff

## START HERE

- **Date**: 2026-11-25. **Branch** `etcd-safe-p8`, worktree `/shared/etcd-grove-p8`, based on P6's
  `etcd-safe-walfix-p6` @ `5960660fb8` (merge P6's later commits: `git fetch /shared/etcd-grove-p6
  etcd-safe-walfix-p6 && git merge FETCH_HEAD`).
- **Build**: `export TMPDIR=/shared/tmp`; every lake command takes
  `--packages=/shared/tmp/manifest-fce59af7.json`; builds through `/shared/tmp/build-slot.sh lake
  --packages=… build TARGETS`; `etc/lean-check.py` for the edit loop.
- **State**: see "Progress" (kept current). **Next**: see "Left".

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

What this branch provides (all statements proved but the one law):

| file | what |
|---|---|
| `Proof/.../storage/WalCrashRead.lean` (pure) | I1-I4 of any read `walRead I = some σ` (`walRead_wf`, `walRead_last_le` from `walIdxLe B I`, `walRead_b_le_commit`, `walRead_commit_le_last` from `walCommitLe I`, `walRead_snapBase`); the two history conditions pass to prefixes (`walIdxLe_take`, `walCommitLeFrom_take`, `walCommitLe_take`) |
| `Proof/.../storage/wal/CrashS.lean` | the crash view with whole operations `walCrashWalS` (`walStCrashS`: `walStCrash` and every new history a prefix `walImgS` at the old synced mark), `walCrashWalS_weak`, `walDiskAt_crash_keepS`; **`walInv_crashS.law`** (statement only: `walInv_crash` with `walCrashWalS`) |
| `Proof/.../storage/WalRecsCrash.lean` | `walFilesC` (the files a crash left: `walFiles` without the synced mark), `walFiles_walFilesC`, **`walFilesC_crash`** |
| `Proof/.../etcdserver/SrvCrash.lean` | `walReadFacts_of_read`, `walReadFacts_of_take`; `srvFilesC`, `srvFiles_srvFilesC`, `srvFilesC_dataDir_len` |

How T7 composes them: `walInv_crashS.law` (in place of `walInv_crash`) gives `walCrashWalS W W'`,
`walUnlockedTok (W := W')`; the program's boot gives the directory's call permission half. T2's
callback is `walFilesC_crash h.toWalA W' d n id cid …` on the unfolded `walRecsH` (T2's module
`import all`s `WalRecs`; a ten-line wrapper there), with `Φ σ := walFilesC {h.toWalA with W := W'} id cid σ
true ∗ …`; `walReadFacts σ` from `walReadFacts_of_take` once T2's invariant keeps the two history
conditions (below).

## Proposals to the consumers (statements not fixed yet; for the coordinator)

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

## The P6 change P8 needs (`walInv_crashS.law`)

`walInv_crashS.law` is `walInv_crash` with the crash view `walCrashWalS`. Its proof is
`walInv_crash`'s once the pure crash returns the whole-operation images, which P6's proof already
constructs and then weakens (`CrashPure.lean`, P6's file, not edited here):

1. `crashTo_start`: conclusion `walCrash d (some d')` → `walCrash d (some d') ∧ walImgS d.H d.m d'.H`
   (in the proof: `himg : walImgS d.H d.m I`, `d'.H = I`).
2. `CrashGood`: `walCrash d (o.map Prod.fst)` → `… ∧ ∀ d', o.map Prod.fst = some d' → walImgS d.H d.m
   d'.H`; `crashGood_exists` passes it from `crashTo_start` (on `walFullD d …`, same `H` and `m`).
3. `walCrash_pure`: `walStCrash s s'` → `walStCrashS s s'` (move `walStCrashS` from `CrashS.lean` to
   `CrashPure.lean` or `Ghost.lean`).
4. `Crash.lean`: `walCrashWal` over `walStCrashS` (then `walCrashWalS` = `walCrashWal` and the law is
   `walInv_crash` itself; the `_keep` lemmas take `hc.1`), or `walInv_crash` builds `walCrashWalS`.

No trusted text: `walImg`/`walCrash` (`GooseLang/Ext/AbsDisk/Impl.lean`) stay as they are.

## Progress

- 2026-11-25 (session 1): read the D6 design and T2/T4's statements, then wrote the four files above. A
  targeted `lake build` of the four modules succeeds (`/shared/tmp/p8-build1.log`); `import-all-check` and
  `tier-check --check` pass (all four are defs tier). No axiom and no `sorry`: `walInv_crashS.law` is an
  `abbrev` that nothing uses yet. Coordinator, 2026-11-25: P6 re-pins to fork `goose-lean-fmt1c-crashfixes`
  @ `e94f33b50`; merge it when pushed. The WAL crash facts rest on W1 only; stale-byte tears are out of scope.

## Left

- `walInv_crashS.law`'s discharge: the P6 change above (P6's owner, or P8 after P6 lands).
- T7 wiring (the coordinator's C8) over these lemmas.
