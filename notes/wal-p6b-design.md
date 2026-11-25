# P6b item 1: per-incarnation WAL facts (design, 2026-11-25; not started in Lean)

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
