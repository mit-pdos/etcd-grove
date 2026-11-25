# P6b item 1: per-incarnation WAL facts (design, 2026-11-25)

## State C, keys (2026-11-25, P6b session 17; approved by the coordinator)

`walDirKeysAuth` records keys only at incarnations up to the current one (`⌜∀ dir i x, Kall !! (dir, i) = some x →
i ≤ incOf I dir⌝`, internal invariant, no spec change), so a bump of `dir`'s incarnation (`Discard`'s rename and
fsync) leaves no key at the new incarnation and the authority's map becomes `K.delete dir`
(`walDirKeysAuth_bump`, `keys_bump`).

## v2.1 (2026-11-25, P6b session 2; approved by the coordinator): supersedes v2 below where they differ

1. **Facts can be retired.** `walIncFact I dir i P := (incOf I dir = i ∧ P) ∨ i < incOf I dir`: a fact of
   incarnation `i` holds of the WAL at `dir` while `i` is current and says nothing once it is retired. Needed
   because handle records are keyed by `GName`: a stale record of the same `Loc` cannot be excluded, so `Sync`
   with a stale `walLenLb` must still yield a (retired) `walSyncedLb`. All three facts take the incarnation:
   `walSyncedLb dir i n`, `walNamed dir i`, `walLenLb w dir i n`.
2. **Step lemmas hand out facts from an earlier past state.** A step lemma that hands out a fact takes a past
   `walPastI (s0, I0)` and returns the fact at `incOf I0 dir` (`walNamed_of_le`, `walSyncedLb_of_le`: current
   or retired), so no such lemma needs the caller's quarter (pattern: `walInvBody_named`/`walInv_named`).
3. **The lock's quarter lives inside `walLockedTokI I`** (`walLockedTok := ∃ I, walLockedTokI I`);
   `walOpenWI w dir i` is the handle's record with `⌜incOf I dir = i⌝` of that quarter. `walHandleInc` is
   dropped: the handle's state carries `WalHS.inc`. The program view's share is the quarter `walIncQ`.
4. **Lemmas that conclude "still present"** from a past state with the WAL (`walInv_register`, `CreateSteps`,
   `ReadAllNamed`, `TailLenLb`) take the lock token's quarter and agree it with the ghost
   (`walGhostI_lockedI_agree`); `walLeI`'s fourth conjunct at equal incarnations then gives the WAL.
5. **`walDirKey` keyed by `(dir, i)` is deferred** until a re-`Create` needs it (`DiscardUnsaved` followed by
   `bootstrap`'s re-`Create` will: do it then).
6. **Specs** (approved): `Create` takes a `∀ i` parameter, its atomic update over `walDirIsI dir i`, its success
   post `walOpenWFI … i ∗ walNamed dir i ∗ walLenLb w dir i 0 ∗ walSyncedLb dir i 0`; `WalShN` gains
   `inc : Nat`, so `Save`'s update is over `walDiskAtI dir γ.inc`. Ledger entry
   (`notes/specs-only/ledger.md`) before the spec edits.

## v2 (2026-11-25, P6b session 1): supersedes "Proposed shape" below where they differ

Implementing v1 found three gaps; v2 closes them. Nothing trusted changes (the crash clause already lets
an unnamed WAL vanish; `walImg`/`walCrash` untouched).

1. **The incarnation is a ghost counter, not the directory inode `j`.** With `j`, a fact of the discarded
   incarnation `(dir, j_old)` revives if `Create`'s new directory gets `j_old` again. The Fs model never
   reuses an inode (`nextIno` only grows, kept by a crash), but no client spec of the Fs extension says so
   (mkdir's post names a new inode, not one never seen), and the old directory is deleted (`Create`'s
   `RemoveAll(dir.tmp)`) before the new one is made, so no claim the WAL layer holds tells them apart.
   Proving freshness would need a new Fs spec. A counter needs nothing: `I : GMap GoString Nat`,
   `incOf I dir` (absent = 0), bumped by the discard, never lowered; a new generation starts at `∅`.
2. **The program's view must carry the incarnation.** v1 said `walDirIs dir o` needs none. But the
   facts' consumers combine a view with a fact (`walDiskAt_crash_keep{,S}`: `walDiskAt dir d ∗
   walSyncedLb dir n ∗ walNamed dir`; `walGhost_raiseNamed`): to use `walSyncedLb dir i n` they need the
   view's WAL to be incarnation `i`. So the program owns a share of `I` with its map (`walOwnI M I`), and
   the views take `i`: `walDiskAtI dir i d := ∃ M I, walOwnI M I ∗ ⌜walOptLe (some d) (M !! dir) ∧ incOf I dir = i⌝`.
   Keep `walDiskAt dir d := ∃ i, walDiskAtI dir i d` (and `walDirIs`, `walAbsent` likewise), so that only the
   clients that use facts (the tester, `WalRecs*`, `WalViews`, the crash lemmas) switch to the `I` forms.
3. **The handles must know their incarnation is current** (`TailSync*`/`TailLenLb`: `walLenLb` to
   `walSyncedLb` needs the handle's `i` = the present `incOf I dir`). Through the lock: the discard needs
   the free lock token, every handle holds the taken one. `γI` is split in three: half in `walGhost`, a
   quarter in `walOwn` (the program's view), a quarter in the lock token (`walUnlockedTok` when free,
   the handle predicates when taken). The handle's record gets `i` (`γhd : GName ↦ (Loc × GoString × Nat)`,
   set at `walHandle_alloc` from the lock's quarter), and the sealed handle predicates (`walOpenW`,
   `walHandleP`, `walOpening`, `walReadFailed`) say `incOf I dir = i` of their quarter: `I` changes only
   with all three shares, so it cannot change under an open handle. `walHandleInc w dir i` (persistent:
   the record) is what a spec names to tie a handle's facts to the client's view (`Sync`: pre
   `walHandleInc w dir i ∗ walLenLb w dir n`, post `walSyncedLb dir i n`).
4. **`walDirKey`** ("fixed for the generation", 22 `walDirKey_lookup` sites) is keyed by `(dir, i)`:
   `walDirKey dir i j X`; the authority's current map is `K` at `(dir, incOf I dir)`; a lookup takes the
   holder's `i`, current by 3.

**The past states** become pairs `(s, I)` (`walPastI`, `WalGS.γpi`), ordered by `walLeI`: area and durable
directories kept, every incarnation at least as high, a WAL whose incarnation is unchanged kept and grown
(`absLe`'s clause). `walPast s := ∃ I, walPastI (s, I)` keeps the area and `dirDurable` users unchanged. The
facts: `walSyncedLb dir i n`, `walNamed dir i` (a past pair with `incOf I dir = i` and the WAL there synced
to `n` / named), `walLenLb w dir n` (through the handle's record, its signature unchanged). A crash maps
incarnation `i` of the old generation to `0` of the new one (the new generation's `I` is `∅`;
`walCrashWal` gives `walOwnI W' s'.wal ∅ ∗ walPastI W' (s', ∅)`, so `walGhost_init` returns those).

**Done (P6b session 1, Ghost.lean, additive, nothing uses it yet):** `WalGS.γI`, `WalGS.γpi` (allocated
in `walGhost_init`), `incOf`, `walLeI` (+ `_refl`, `_trans`, `_of_absLe`, `_discard`), `walPastI`,
`walPastIAuth`, `walPastI_le`/`_grow`/`_snap`. **Next**: the swap (`walGhost`'s body over `walPastIAuth`
and the `γI` half; `walOwn`/views/lock tokens with their quarters; handle records with `i`; the facts'
new definitions; then the producers and specs bottom-up).

---

## v1 (the previous session's; superseded where v2 differs)

Goal: `wal.DiscardUnsaved` (`true` ⇒ the program's view `walDirIs dir none`), with `bootstrap` then
re-`Create`ing the WAL at the same `dir` in the same generation (`bootstrap.go`, fork `e94f33b50`:
`Unsaved`, `removeBackendDurably`, `DiscardUnsaved`, later `bootstrapRaft`'s `Create`). Agreed with the
coordinator: the incarnation is the WAL directory's inode `j`.

## What is persistent and keyed by `dir` alone today (each must become per-incarnation)

1. `walPast s` and the order `absLe` (`AbsDisk/Specs.lean`, generic): "no WAL disappears", "named stays
   named", "length/mark grow". The facts read from past states:
   `walSyncedLb dir n`, `walNamed dir`, `walLenLb w dir n` (`Ghost.lean:264-290`), and
   `walPast_ghost_le` users (`ReadAllSynced`, `ReadAllNamed`, `TailLenLb`, `NamedView`, `CreateNamedStep`,
   `CreateSplit`, `Append`, `WAL__Sync`, `Crash.lean`'s crash view).
2. `walDirKey dir j X` (`Ghost.lean:511`, `γdk`, persistent map elements keyed by `dir`): "fixed for the
   generation" — a second `Create` at `dir` cannot insert a new `(j', X)`. Key it by `(dir, j)` (or keep
   the persistent map keyed by `dir` but valued by a list of incarnations, the current one last).

## Proposed shape (the least churn found)

Keep `AbsDiskState`, `absLe`, `walGhost s`'s and `walGhost_init`'s signatures (trusted vocabulary and
P8's `Crash.lean`/`CrashPure.lean` untouched until the last step). Move the three lower-bound facts off
the past states onto **per-incarnation persistent maps** in `WalGS` (new ghost names, allocated in
`walGhost_init`), held by `walGhost`'s existential part:

* `γsy : GMap (GoString × Ino × Nat) Unit` — `walSyncedLb dir j n := (dir, j, n) ↪[γsy]□ ()`;
* `γnm : GMap (GoString × Ino) Unit` — `walNamed dir j := (dir, j) ↪[γnm]□ ()`;
* `walLenLb w dir n`: through the handle, whose directory record gets `j`
  (`γhd : GName ↦ (Loc × GoString × Ino)`), and a map `γln : GMap (GoString × Ino × Nat) Unit` as `γsy`.

`walGhost s` gains (inside its existential, signature unchanged) the WALs' current incarnations
`J : GMap GoString Ino` (`J !! dir = some j` iff `s.wal !! dir = some d`; set by `Create`'s commit and by
`ReadAll`'s pin, which already know `lay.j`) and the coherence: every `(dir, j, n) ∈ Fsy` with
`J !! dir = some j` has `n ≤ d.m`; every `(dir, j) ∈ Fnm` with `J !! dir = some j` has `d.named`; likewise
`Fln` with `d.H.length`. A fact of a retired incarnation constrains nothing. Then:

* `absLe` may drop `dir` (the discard) — only the per-incarnation coherence is needed by the facts' users;
  `absLe`'s other users (`walPast_ghost_le` for the area and durable directories) are unaffected. The
  relaxation is a WAL-layer copy of `absLe` (`walLe`: area kept, dirs kept, a WAL kept or removed, kept ones
  growing), with `absPastAt`/`absPastAuth` copied into `Ghost.lean` over it (the generic ones stay for the
  trusted extension's vocabulary).
* `DiscardUnsaved`'s rename sets `named := false` (a real step the order must allow: named → unnamed only
  with the lock token, the program's view exact), and the parent fsync removes the WAL and `J !! dir`.
  `Create` then inserts a new `j` (a fresh directory inode), and none of the old facts apply to it.
* The program's view `walDirIs dir o` needs no incarnation if the discard and `Create` both go through
  the program's update (`walOwn`), which they do.

## Ripple (estimate unchanged: 1,000-2,000 lines, 2-4 sessions)

The facts' signatures gain `j`: specs `Create`, `CreateFresh`, `WAL__Save`, `WAL__SaveSnapshot`, `WAL__Sync`,
`WAL__sync*`, `WAL__cut*`, `WAL__Close`, `WAL__ReleaseLockTo`, `WAL__ReadAll`, `ReadAllTailCallees`,
`storage__{Save,SaveSnap,Sync,Release,Close}`; the tester's `member__{save,sync,close}`, `restartRead`, its
`MemberRep`/`MemberInv`/`SaveAu`/`SnapAu`/`Crash`/`Inv`. Their producers: `TailSync*`, `TailLenLb`,
`CreateNamed*`, `ReadAll{Named,Synced,Commit}`, `Handle*`, `CloseHandle`, `NamedView` (`walGhost_raiseNamed`:
needs `J !! dir = some j`, from the view's exact pin). Last: `Crash.lean`'s crash view (old generation's facts
to the new one's, `walPast_ghost_le` at lines ~1090-1230), after merging P8's `walCrashWal` change.

Then `DiscardUnsaved`'s spec (pre as `Unsaved`'s plus the parent directory's resources for `RemoveAll`/
`Rename`/`syncDir`, as `Create`'s `renameWAL`; post `b = true → Q none`-style commit to `walDirIs dir none`,
`false` unchanged) and proof (`Unsaved`'s, then the three calls).

## Order

1. `Ghost.lean`: the new maps, `walGhost`'s coherence, the facts' new definitions and their laws
   (`walSyncedLb_mono`, `walOpenW_lenLb`, `walGhost_raiseNamed`, the producers' update lemmas).
2. Producers and specs bottom-up (`etc/importers.py --uses walSyncedLb ...`), each file through
   `etc/lean-check.py`.
3. The tester.
4. Merge `etcd-safe-p8`; `Crash.lean`.
5. `DiscardUnsaved`.

## Two layouts never share a directory (session 19, decided by the coordinator)

S's crash facts for the other WALs need `lay'.j ≠ lay.j` for every other layout. The coordinator's order: the
fraction argument first, an internal invariant fact only if it does not follow. It follows, with no change to the
invariant: with the lock free (`walParked`'s `o.T = []`), `walTmpParked0` holds `walTmpsRes J` per layout
directory, `qTmp` (¾) of `J`'s `0.tmp` claim each, so two layouts on one `J` contradict `qTmp_two`
(`walTmpParked0_inj`, `DiscardSInv.lean`). (`walTmpHalves`' `qTmpI` quarters with one parked `qTmp` would also do.)
