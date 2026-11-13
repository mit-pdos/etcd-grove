# Rung 3, R3-3 / R3-4: the bbolt arm of the abstract disk (Freeze package)

2026-11-12, crash-rung3 for etcd-grove-81. **Hard stop: trusted texts.** Nothing below is in Lean yet;
the texts are the proposed Lean, to be reviewed before R3-4 writes them. Worktree
`/shared/etcd-grove-rung3`, branch `crash-rung3` (lean `b4f0711091` + the R3-0 tester).

Pins: bbolt fork `ea4cab5` (`B/` = `/root/go/pkg/mod/github.com/upamanyus/bbolt@v0.0.0-20261111214215-ea4cab526797`),
etcd fork `c90b03b56` (`S/` = `.../upamanyus/etcd/server/v3@v3.0.0-20261111235821-c90b03b56bd2`), as
`examples/go.mod` replaces them. Scope: `/shared/tmp/crash-rung3/scope.md` (§2.3, §2.4, decisions).
W4a's extension: `GooseLang/Ext/AbsDisk/{Impl,Paths,Specs}.lean`, `notes/decisions.md` "WAL W4a" (five
entries), `/shared/tmp/wal-spec/w4/freeze-w4a.md`.

## 0. Summary

1. **The arm.** `AbsDiskState` gets the field `bolt : GMap GoString BoltFile` that W4a's docstring
   reserves: the bbolt files the abstract disk *tracks*, fixed at the start (no step adds or removes a
   key). A tracked file is `absent` or `file f`, `f : BoltDur = ⟨last, flight, named⟩`. Four steps
   (`"BoltOpen"`, `"BoltBegin"`, `"BoltSync"`, `"BoltNamed"`), and the crash conjunct `boltCrash` per
   tracked file, which covers a power loss, a kill, and their sequences in one relation (§2).
2. **What a crash leaves** (`boltImg`, the Scope's): the last returned commit or the one in flight.
   **What the next `Open` reads** (`boltRead f = f.flight.getD f.last`, new): after a power loss the
   image; after a kill the page cache, which holds the in-flight meta if it was written. The kill case
   keeps the old commit possible on the disk (`⟨last, some D⟩`) until the fixed `Open` syncs: this is
   where §1.6's bug (kill, restart, power loss) lives, and why `Open`'s spec has a step.
3. **The axioms.** Three new trust-boundary specs for *tracked* databases (`Open_kv_trk`,
   `Tx.Commit_kv_trk`, `DB.Close_kv_trk`; the Scope's two atomic updates in `Commit`, one in `Open`),
   and a **weakening of today's three** (`Open_kv` gives a persistent `dbUntracked db`, which today's
   `Tx.Commit_kv` and `DB.Close_kv` then require). Why today's axioms must change at all (§3.1): a
   commit that does not move the arm is false of a tracked file, so today's `Commit_kv` must not apply
   to one. The change is additive for every proof above the backend; the backend's two proofs that call
   bbolt (`newBackend`, `batchTx.commit`) and `backend.Close` carry the witness.
4. **The tester's trusted function** `syncDir(dir)`: its model performs `"BoltNamed"`.
5. **Paths.** A tracked file lies outside the WAL area and its last element is hidden (starts with
   `.`), so the durable extension's reserved mode, `TouchDirAll` and the WAL's footprint never touch
   it, with no change to W4a's texts (§2.4). This moves the tester's file to `root/data/member/snap/.db`
   (decision D2; the alternative touches W4a's `"WalCreate"`).
6. **Go evidence** (§5): the R3-0 matrix over the goose-translatable tester (posix, ordered, each with
   and without P4 garbage on unsynced sectors, kill, and kill-then-power-loss chains) at `ea4cab5`, and
   the same tester against the unfixed bbolt `743299d8` as the negative control; plus the Scope's
   experiments A-C. The controls of §5.2 run the final tester (a multi-page db, option (b), and the
   consistent index loaded where `bootstrapBackend` loads it): the unfixed bbolt shows the
   kill-then-power corruption, the D7 fork does not.
7. **Decisions requested** (§7): D1 the shape (tracked axioms + today's weakened), D2 the hidden-name
   path rule, D3 two option fields in the backend's `OptsM`, D4 the `fileHolds` gate for rung 4.

A correction to the Scope: §1.1 step 2 says etcd runs with `NoFreelistSync = false`. It runs with
`true` (`S/storage/backend/config_linux.go:29-32`, `boltOpenOptions`): commits write no freelist, and
`Open` rebuilds it from the chosen meta (`freepages`). The argument of §1.4 is unaffected (a page
reachable from the chosen meta is never free), and `Open`'s one-commit branch (`B/db.go:157`,
`!NoFreelistSync && !hasSyncedFreelist`) is still not etcd's case. The experiments ran with etcd's
options (the real backend), so they cover `true`.

## 1. What the trusted text must say (from the Go)

Commit (`B/tx.go:171-283`), in order: rebalance and spill to pages free in the current meta `N`
(copy-on-write); `db.grow` (`:236`; `ftruncate`, then `fsync` unless `NoGrowSync`, `B/db.go:1312-1340`);
`tx.write()` (`:526-597`: every dirty page by `pwrite`, `:551`, then `fdatasync`, `:574`, unless
`NoSync`); `tx.writeMeta()` (`:601-630`: the meta page by one `pwrite` at slot `txid % 2`, `:613`, then
`fdatasync`, `:621`). An error after the meta's `pwrite` returns an error although the meta may be
durable; etcd `Fatal`s on any commit error (`S/storage/backend/batch_tx.go:291-303`).

Open (`B/db.go:182-340`): create or open, `flock`; `init` of an empty file or zero metas (synced,
`:702-760`); `mmapUnlocked` validates both metas and fails only if both are invalid; `db.meta()` takes the
valid meta with the higher txid; in write mode, **`fdatasync` unless `NoSync`** (`:322-333`, the fork's
`c5a6065`/`ea4cab5`: on an error it closes the database and returns the error); no directory fsync
after a create.

Close (`B/db.go:784`): unmaps, unlocks, closes; writes nothing (etcd's options).

| Crash during commit `N+1` (after `N` returned) | What a power loss leaves (P1, P4, P5) | What a kill leaves (the page cache) |
|---|---|---|
| before the meta's `pwrite` | `N` (only pages free in `N` written) | `N` |
| after the `pwrite`, before its `fdatasync` returns | `N` or `N+1` (a torn meta fails FNV-64a, P5) | `N+1`, while the disk may still hold `N` |
| after the meta's `fdatasync` | `N+1` | `N+1` |

So a power loss leaves `last` or `flight`; a kill leaves a page cache reading `flight` (or `last`) over a
disk that may still revert to `last`. After a kill the next process reads `N+1` and, without the
fork's sync, builds on it (§1.6 of the Scope).

## 2. The arm in `absDiskExt` [trusted text, `GooseLang/Ext/AbsDisk/Impl.lean`]

### 2.1 State

```lean
/-- A bbolt database's data: its top-level buckets (the backend's `Data`, `InvBbolt.lean`, is this
type: etcd has no nested buckets). -/
abbrev BoltData := GMap GoString (GMap GoString GoString)

/-- **A tracked bbolt file's durable state.** `last`: the data of the last commit whose meta's
fdatasync returned (or that the last `Open` synced, or `∅` for a file `Open` just created).
`flight`: the commit begun since (`Tx.Commit` from its start to its meta's fdatasync; kept after an
error, whose meta may be durable), or, after a kill, what the page cache holds above `last`.
`named`: the file's directory entry is durable (bbolt never fsyncs the directory). -/
structure BoltDur where
  last : BoltData
  flight : Option BoltData
  named : Bool

/-- A tracked bbolt file: none at its path, or one. A file with zero length or zero metas reads as
`∅` (`init`, `B/db.go:702-760`, re-initializes it), as `absent` does. -/
inductive BoltFile where
  | absent
  | file (f : BoltDur)

/-- **What a power loss can leave of the file** (the Scope's `boltImg`): the last returned commit,
or the one in flight. P1 (fdatasync), P4 (synced bytes survive a write elsewhere; unsynced bytes
arbitrary), P5 (no FNV-64a collision on a torn meta): table above. -/
def boltImg (f : BoltDur) (D : BoltData) : Prop := D = f.last ∨ f.flight = some D

/-- **What `Open` reads** of the file: the in-flight data if any (after a kill whose meta reached the
page cache: the valid meta with the higher txid), else the last. -/
def boltRead : BoltFile → BoltData
  | .absent => ∅
  | .file f => f.flight.getD f.last

/-- The file after the fixed `Open`'s fdatasync (`B/db.go:322-333`): what it read, durable; a file
`Open` created is `∅`, its entry not yet durable. -/
def boltOpened : BoltFile → BoltFile
  | .absent => .file ⟨∅, none, false⟩
  | .file f => .file ⟨f.flight.getD f.last, none, f.named⟩

/-- **The crash relation of one tracked file** [trusted]. A file whose entry is not durable may
vanish. Otherwise the disk keeps an image `D` (`boltImg`), and either a power loss made it the whole
state (`⟨D, none⟩`), or a kill left `D` in the page cache over a disk that may still hold `last`
(`⟨last, some D⟩`: the next `Open` reads `D`, a later power loss leaves `last` or `D`). A kill that
leaves `last` is the case `D = last`. `named` is kept: a kill keeps an unsynced entry unsynced. -/
def boltCrash : BoltFile → BoltFile → Prop
  | .absent, f' => f' = .absent
  | .file f, f' => (f.named = false ∧ f' = .absent) ∨
      ∃ D, boltImg f D ∧ (f' = .file ⟨D, none, f.named⟩ ∨ f' = .file ⟨f.last, some D, f.named⟩)
```

`AbsDiskState` gets `bolt : GMap GoString BoltFile` (W4a's docstring already announces it; the
`Inhabited` instance gets `∅`).

### 2.2 Steps (new cases of `AbsDiskStep`)

```lean
  | "BoltOpen" => ∃ p : GoString, v = #p ∧
      s' = { s with bolt := match s.bolt !! p with
                            | some b => <[p := boltOpened b]> s.bolt
                            | none => s.bolt }
  | "BoltBegin" => ∃ (p : GoString) (S : BoltData), v = PairV (#p) (#(walCode S)) ∧
      s' = { s with bolt := match s.bolt !! p with
                            | some (.file f) => <[p := .file { f with flight := some S }]> s.bolt
                            | _ => s.bolt }
  | "BoltSync" => ∃ (p : GoString) (S : BoltData), v = PairV (#p) (#(walCode S)) ∧
      s' = { s with bolt := match s.bolt !! p with
                            | some (.file f) => if f.flight = some S
                                then <[p := .file { f with last := S, flight := none }]> s.bolt
                                else s.bolt
                            | _ => s.bolt }
  | "BoltNamed" => ∃ dir : GoString, v = #dir ∧ s.dirs !! dir = some () ∧
      s' = { s with bolt := boltNameIn dir s.bolt }
```

`boltNameIn dir B` sets `named := true` on every `file` of `B` whose key is `dir ++ "/" ++ c` with `c` a
path element (the entries an `fsync(dir)` makes durable). `"BoltNamed"` needs `dir`'s own entry and its
ancestors' durable (`s.dirs`, W4a's `"DirDurable"`, which `TouchDirAll` performs): an fsync of a
directory that may itself vanish makes nothing survive. Every bolt step is a no-op on an untracked path
(`none`), so a body may perform it on any file. `walCode` needs `Pos.Countable BoltData` (a `GMap` of
`GMap`s of strings; derived from `Pos.Countable (List (GoString × List (GoString × GoString)))` by
`toList`, injective on `GMap`).

### 2.3 Crash and start

```lean
  crash s s' := s'.area = s.area ∧ s'.dirs = s.dirs ∧ (W4a's WAL conjuncts) ∧
    (∀ p b, s.bolt !! p = some b → ∃ b', s'.bolt !! p = some b' ∧ boltCrash b b') ∧
    (∀ p, s.bolt !! p = none → s'.bolt !! p = none)

def absDiskInitOk (s : AbsDiskState) : Prop :=
  (W4a's three conjuncts) ∧ (∀ p b, s.bolt !! p = some b → boltPathOk s.area p)
```

### 2.4 Paths [trusted, `Paths.lean`]

```lean
/-- **A tracked bbolt file's path**: clean, absolute, outside the WAL area, and hidden (its last
element starts with `.`, so the durable extension never names it in its reserved mode,
`durableNameOk`), but neither `TouchDirAll`'s probe `.touch` nor a durable temporary `.durable-*`. -/
def boltPathOk (area p : GoString) : Prop :=
  cleanAbsPath p ∧ ¬ underDir area p ∧
  ∃ q c, p = q ++ go!"/." ++ c ∧ W8 47 ∉ c ∧ c ≠ go!"touch" ∧ ¬ (go!"durable-" <+: c)
```

Who else names paths, and why none reaches a tracked file:
- **WAL** (W4a): its footprint is `walCreateRegion` of area directories, the area's and its parent's
  fsyncs, and `Create`'s mkdir of missing ancestors of the area; a tracked file is not under the area
  and is a file, so never in a region and never an ancestor of the area (an ancestor is a directory;
  a file at an ancestor's path only makes `Create`'s mkdir fail).
- **durable** (reserved mode, which the WAL functions and `TouchDirAll` already require): names
  are not hidden (`durableHidden`); its temporaries are `dir/.durable-*`, excluded above.
- **`TouchDirAll(d)`**: `d` not under the area; its mkdir on a tracked file's path (absent) would make
  `bolt.Open` fail (an error arm, `¬ dbOpenOk`), never change a file; its probe `d/.touch` is
  excluded above.
- **bbolt itself**: one file per database, no temporaries; `flock` on the file's own descriptor.
- **`syncDir`**: fsync only.

The world assumption "Paths" (approved, W4a) covers paths at or below the data directory: a tracked
file must lie there (the tester's `root/data/member/snap/.db` does). Gate (D4): rung 4's etcd layout
(`member/snap/db`, not hidden, under the area once the WAL is at `member/wal`) needs C6's WAL-name
restriction (W4a's own gate: "C6 must restrict WAL names or exempt the WAL's named siblings").

### 2.5 The tester's `syncDir` [trusted model, `TrustedCode/.../examples/etcd/mvcccrash.lean`]

The model chooses its result, because Go's `syncDir` can return false (an `os.Open`, `Sync` or `Close`
error), including after an fsync that took effect:

```lean
syncDir.impl := λ dir, if: nondet then (ExternalOp absDiskExt.name "BoltNamed" #dir ;; #true) else #false
```

Its spec (proved in R3-4 from `wp_BoltNamed`; an atomic update, not a post fact):

```lean
{{ dirDurable dir ∗ AU <{ ∃∃ B, boltOwn B }> @ ⊤, ∅ <{ boltOwn (boltNameIn dir B), COMM Q }> }}
  syncDir #dir
{{ (b : Bool), RET #b; (⌜b = true⌝ ∗ Q) ∨ (⌜b = false⌝ ∗ AU <{ … }> <{ … , COMM Q }>) }}
```

The `true` branch commits the update at the step and returns; the `false` branch never opens it and
hands it back. A failure after a real fsync is then modeled as "no step": `named` stays false, which
only allows more crash images (the file may vanish), so the model covers Go. `dirDurable dir` (W4a's
persistent fact of `"DirDurable"`, `TouchDirAll`'s post) is a precondition, read through
`absPast`/`absLe` (`dirs` only grows), never produced here.

## 3. The axioms [trusted text, `Spec/go_etcd_io/bbolt/`, `Proof/.../storage/backend/InvBbolt.lean`]

### 3.1 Why today's axioms change (the soundness argument)

A tracked file's arm must move at every commit: if a commit could run without its `"BoltBegin"`/
`"BoltSync"`, the arm would keep `⟨D, none⟩` while the file holds `S`, and the crash relation would
promise `D` after a crash that leaves `S`. Today's `Tx.Commit_kv` moves nothing and asks nothing, and
by the frame rule a client holding the arm's ghost across it keeps it unchanged: so it is **false** for a
tracked file, and must not apply to one. Three ways out:

- **(U) recommended: an untracked witness.** Today's `Open_kv` (from `fileHolds path D`) also gives a
  persistent `dbUntracked db`; today's `Commit_kv` and `DB.Close_kv` require it. The tracked axioms
  give and take `dbTracked db path` instead. Weakening `Commit_kv`/`Close_kv` (a stronger premise) is
  safe; `Open_kv`'s stronger post says "the file was given as `fileHolds`, so it is not tracked", true
  as long as **no `fileHolds` names a tracked path** (D4's gate: today `fileHolds` is minted only by the
  crash-free start, `goose_adequacy_start_files`, by `DB.Close_kv` from an untracked database, and by
  the server's snapshot and rename axioms; a crash theorem uses `goose_crash_adequacy`, which mints
  none, so in `etcd_mvcccrash_adequate` no `fileHolds` exists at all). Ripple: `newBackend` keeps the
  witness, `InvBackend` gets it as a persistent conjunct beside `dbFile`, `batchTx.commit` and
  `backend.Close` pass it, `axiomcx/bboltnan` passes it. No backend spec statement changes.
- **(S) separate worlds, no change to today's axioms.** The tracked axioms only; a gate that no closed
  theorem's trust base holds both today's and the tracked `Open`/`Commit`/`Close` (W4a's Option B
  precedent). The pair is then false together in one world, and only the gate keeps them apart; and
  the backend's two proofs need tracked copies anyway. Weaker than (U) for the same work.
- **(M) mandatory everywhere.** Replace today's axioms by the tracked ones; `fileHolds` retires,
  every program's start hands the arm. Principled, but it moves every closed theorem's start and
  extension list (server, mvccfull, mvccrand): out of rung 3's scope (the coordinator's "additive").

### 3.2 New vocabulary [trusted, `InvBbolt.lean`]

```lean
/-- (rung 3) The open database `db`'s file is not one the abstract disk tracks: its commits need not
move the arm (persistent). `Open_kv` gives it. -/
axiom dbUntracked (db : Loc) : IProp GF
/-- (rung 3) The open database `db` is the tracked file at `path` (persistent). `Open_kv_trk` gives it;
`Tx.Commit_kv_trk` and `DB.Close_kv_trk` take it. -/
axiom dbTracked (db : Loc) (path : GoString) : IProp GF
(+ Persistent and Timeless instances)
```

And proved ghost vocabulary (`GooseLang/Ext/AbsDisk/Specs.lean`, R3-4, not trusted): `boltOwn B`
(half of a ghost variable of the whole bolt map with a token, as `walOwn`), `boltFileAt p b :=
∃ B, boltOwn B ∗ ⌜B !! p = some b⌝` (holds the whole map, as `walDiskAt`: one database per program
here), and the step specs.

### 3.3 Today's axioms, weakened

```lean
-- Open_kv: post's success arm adds
       ∗ dbUntracked db
-- Tx.Commit_kv and DB.Close_kv: pre adds
       ∗ dbUntracked db
```

### 3.4 `Open_kv_trk` (new)

```lean
/-- `bolt.Open(path, mode, opts)` of a tracked file (rung 3): in write mode with syncing options,
`Open` reads `boltRead b` and fdatasyncs the file before it returns (`B/db.go:322-333`): the atomic
update commits there (`"BoltOpen"`), after which the file is `boltOpened b`. An error only where the
environment does not cooperate (`¬ dbOpenOk`), with the update committed or not. -/
abbrev bbolt.Open_kv_trk.spec : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 29)]
    (path : GoString) (mode : w32) (opts : Loc) (dq : DFrac) (o : OptsM) (Q : BoltData → IProp GF),
  {{ isPkgInit pkg_id.go_etcd_io.bbolt ∗ optsAt opts dq o ∗ ⌜o.ok ∧ o.noSync = false ∧
       o.noGrowSync = false⌝ ∗ (⌜o.logger = GoInterface.nil⌝ ∨ boltLogger o.logger) ∗
     AU <{ ∃∃ b : BoltFile, boltFileAt path b }> @ ⊤, ∅
        <{ boltFileAt path (boltOpened b), COMM Q (boltRead b) }> }}
    Open path mode opts
  {{ (db : Loc) (err : GoInterface), RET (PairV #db #err); optsAt opts dq o ∗
      (⌜err ≠ GoInterface.nil ∧ ¬ dbOpenOk⌝ ∨
       (⌜err = GoInterface.nil⌝ ∗ ∃ (γ : DBNames) (D : BoltData), Q D ∗ ownDB db γ D ∗ wrTok γ ∗
          isDB db ∗ dbFile db path ∗ dbTracked db path)) }}
```

(`noSync`/`noGrowSync`: D3, two fields added to the backend's `OptsM`, set by `newBackend` from
`UnsafeNoFsync`.) The update is mandatory: without it no body could perform `"BoltOpen"` on a tracked
file.

### 3.5 `Tx.Commit_kv_trk` (new; the Scope's two atomic updates)

```lean
/-- `tx.Commit()` of a tracked database's write transaction (rung 3). The first update commits at
the call, before any page is written (`"BoltBegin"`: a crash from here on may leave `S`); the second
at the meta page's fdatasync (`"BoltSync"`, `B/tx.go:621`). Success: both committed, `S` committed.
An error: the first committed, the second not (the meta may be durable: the flight is kept);
the database is then unusable (no `ownDB`, no `wrTok`), as etcd stops on a commit error. -/
abbrev bbolt.Tx.Commit_kv_trk.spec : Prop :=
  ∀ (db tx : Loc) (γ : DBNames) (D S : BoltData) (path : GoString) (Q₁ Q₂ : IProp GF),
  {{ isPkgInit pkg_id.go_etcd_io.bbolt ∗ ownDB db γ D ∗ txDB tx db ∗ ownWTx tx γ D S ∗
     dbTracked db path ∗
     AU <{ ∃∃ f : BoltDur, boltFileAt path (.file f) ∗ ⌜f.last = D ∧ f.flight = none⌝ }> @ ⊤, ∅
        <{ boltFileAt path (.file { f with flight := some S }), COMM Q₁ }> ∗
     (Q₁ -∗ AU <{ ∃∃ f : BoltDur, boltFileAt path (.file f) ∗ ⌜f.flight = some S⌝ }> @ ⊤, ∅
        <{ boltFileAt path (.file { f with last := S, flight := none }), COMM Q₂ }>) }}
    tx.Commit()
  {{ (err : GoInterface), RET #err; txDone tx ∗
      ((⌜err = GoInterface.nil⌝ ∗ ownDB db γ S ∗ wrTok γ ∗ Q₂) ∨ (⌜err ≠ GoInterface.nil⌝ ∗ Q₁)) }}
```

Notes: (a) the first update's binder requires `last = D, flight = none`: the client's invariant ties the
arm to `ownDB`'s data between commits; (b) `Commit` of an unchanged transaction still writes a meta
(`S = D`: harmless); (c) `grow`'s `ftruncate`/`fsync` before the pages are written changes only the
size beyond `N`'s pages; (d) the second update is under `Q₁ -∗`, so the client can only give it after
the first.

### 3.6 `DB.Close_kv_trk` (new)

```lean
/-- `db.Close()` of a tracked database: writes nothing (etcd's options), so the arm is untouched;
`nil`, or an environment error (`¬ dbCloseOk`). -/
abbrev bbolt.DB.Close_kv_trk.spec : Prop :=
  ∀ (db : Loc) (γ : DBNames) (D : BoltData) (path : GoString),
  {{ isPkgInit pkg_id.go_etcd_io.bbolt ∗ isDB db ∗ dbFile db path ∗ dbTracked db path ∗ ownDB db γ D }}
    db.Close()
  {{ (err : GoInterface), RET #err; ⌜err = GoInterface.nil⌝ ∨ ⌜¬ dbCloseOk⌝ }}
```

A reopen after `Close` goes through `Open_kv_trk` again, from the arm (the client keeps `boltFileAt`).

### 3.7 Why a body exists (the consistency argument)

For each axiom, a body that performs the steps: `Open_kv_trk`: today's `Open` behaviour (which
`Open_kv` describes), with `ExternalOp "BoltOpen" path` at the fdatasync, the AU opened around it with
`wp_BoltOpen`. `Commit_kv_trk`: `ExternalOp "BoltBegin" (path, walCode S)` first, then today's commit,
then `ExternalOp "BoltSync" (path, walCode S)` at the meta's fdatasync (the AU's binder gives `flight =
some S`, so the step's `if` takes its first branch). Today's `Open_kv`/`Commit_kv` bodies may perform
the same steps: on an untracked path they are no-ops (§2.2), and `dbUntracked` says the path is untracked.
`Close_kv_trk`: no step. The steps' values: `S` coded by `walCode` (computable from the heap
representation by a loop, as W4a's argument for WAL operations).

### 3.8 The bodies, step by step (the coordinator's 2026-11-12 standard, after W4a.1's review)

W4a.1's review found that a fact given in a post *after* an atomic update commits (a sync mark, a
`named` raised by a parent fsync) cannot be produced by any body, since `atomic_acc`'s commit hands the
resource to the client; and an exact field committed false beside a past-state fact saying it rose
derives `False` at a crash. The bolt arm is built so that neither can happen: **no bolt axiom's post
gives a past-state fact**, and every step a body performs is either the commit of an update the
client gave it, or nothing. `named`, the only bolt field that only rises, is raised only by
`"BoltNamed"`, the commit of `syncDir`'s update, so the client's exact `boltFileAt` and the state never
disagree (no lower-bound copy is needed; if R3-4 wants one for composability, it is proved ghost state,
not trusted text). The bodies:

- **`Open_kv_trk`** (one update `U` over `boltFileAt path b`):
  1. today's `Open` up to the meta read (`flock`, `init` if needed, `mmapUnlocked`, `loadFreelist`):
     no step (the creation of an absent file and `init`'s synced writes are not modeled: a crash before
     step 2 leaves `absent` or a file reading `∅`, which `Open` reads alike);
  2. at the fdatasync (`B/db.go:322-333`): open `U` (`atomic_acc`), learn `b`, `ExternalOp "BoltOpen"
     path` via `wp_BoltOpen` (state `boltOpened b`), **commit** with `Q (boltRead b)`;
  3. return `db` with `ownDB db γ (boltRead b)`, `wrTok`, `isDB`, `dbFile`, `dbTracked db path` (today's
     `Open_kv` resources; `D = boltRead b` because step 1 read the same file the arm describes: the
     client held `boltFileAt`, so no step moved it in between).
  On an error before step 2: `U` is never opened, returned as dropped (post: `¬ dbOpenOk` only); after
  step 2 (the sync failed or later): `Q` dropped. No step after the commit.
- **`Tx.Commit_kv_trk`** (updates `U₁`, and `Q₁ -∗ U₂`):
  1. at the call, before rebalance: open `U₁`, `ExternalOp "BoltBegin" (path, walCode S)` via
     `wp_BoltBegin`, **commit** `U₁`, receiving `Q₁`;
  2. apply the pre's wand to `Q₁`: the body now holds `U₂` (a fresh update, given by the client in the
     pre, so no reuse of a committed update);
  3. today's commit: rebalance, spill, `grow`, pages, their fdatasync, the meta's `pwrite`: no step;
     an error here returns `err ≠ nil` with `Q₁`, `U₂` dropped (the meta may be durable; the flight
     stays);
  4. at the meta's fdatasync return (`B/tx.go:621`): open `U₂`, learn `f.flight = some S`,
     `ExternalOp "BoltSync" (path, walCode S)` via `wp_BoltSync` (the `if` takes its first branch),
     **commit** `U₂`, receiving `Q₂`; an fdatasync error instead: return with `Q₁` (`U₂` dropped);
  5. `tx.close()`, return `nil` with `ownDB db γ S`, `wrTok γ`, `Q₂`. No step after the last commit.
- **`DB.Close_kv_trk`**: today's `Close`; no step, no update.
- **`syncDir`** (§2.5): `true`: open, `"BoltNamed"`, commit, return; `false`: no step.
- **Today's `Open_kv`, `Tx.Commit_kv`, `DB.Close_kv`**: a body may perform the same steps; on the
  untracked path that `dbUntracked` (resp. `fileHolds`) stands for, each is a no-op on the state
  (§2.2), so no ghost state is needed to justify it.

Composability (W4a.1's second finding: a plain triple over the whole-map resource loses it at a crash
during the call): `Open_kv_trk`, `Tx.Commit_kv_trk` and `syncDir` take the arm only through atomic
updates, so the client keeps `boltOwn` in its crash invariant across the calls; `DB.Close_kv_trk` does
not take the arm at all.

## 4. How it composes with the WAL arm

- **One extension, one state, two arms**: the `bolt` field beside `wal`; the steps are disjoint by name
  (`"Bolt*"`), and each touches one field (`"BoltNamed"` reads `dirs`, which W4a's `"DirDurable"`
  writes). The crash relation is the conjunction of the arms' (each per key); W4a's `area`/`dirs`
  conjuncts unchanged.
- **Ghost state** (R3-4, proved): `boltOwn` is a second ghost variable with its own token, beside
  `walOwn`; the interpretation holds both halves; `absDiskStart` hands `boltOwn s0.bolt` too, and
  `absDiskCrashStart` the old and new halves with `boltCrash` between them (lemma `boltFileAt_crash`:
  `boltFileAt p b` in the old generation gives `∃ b', ⌜boltCrash b b'⌝ ∗ boltFileAt p b'` in the new).
  The WAL's handles, lock token and purge rights are untouched; nothing of the bolt arm is per handle
  (bbolt's own `flock` blocks a second `Open` of a live database forever, `Timeout = 0`, and a dropped
  `*DB` holds no buffered data: bbolt writes at commit).
- **Durable's reservation**: unchanged; a tracked file is hidden, which the reserved mode never names
  (§2.4).
- **Gates recorded** (W4a's list, extended): (G1) `fileHolds` never names a tracked path (D4: rung 4's
  `OpenSnapshotBackend` renames a snapshot file onto `member/snap/db`, so C6 must convert at the rename);
  (G2) rung 4's layout needs C6's WAL-name restriction and a non-hidden tracked name; (G3) a trusted
  model performing a bolt step is reviewed against the step specs (today: the three axioms and
  `syncDir`).
- **W4a.1** (in progress on `wal-w4a1`): this package touches no WAL axiom and no WAL step; it adds cases
  and a field to `Impl.lean`, so the merge is textual only. If W4a.1 edits `absDiskInitOk` or the crash
  instance, R3-4 rebases on it.

## 5. Go evidence, per clause

| Clause | Evidence |
|---|---|
| `boltImg` (power loss: last or in flight) | Scope exp. A: 8,000 images of random bbolt commits (etcd's options), every one opened to the last returned commit or the in-flight one (671 in flight), `tx.Check` and a post-recovery stress passed. R3-0 matrix: posix and ordered images of the tester (real backend, cindex, mvcc), with and without P4 garbage on unsynced changed sectors: 0 violations (§5.1). |
| kill: `⟨last, some D⟩`, `boltRead` reads the flight | Scope exp. B: inc 2 opened the killed commit's meta from the page cache (`vis = st1[j1+1]`) in the images where inc 1 had written it. R3-0 kill images and kill-then-power-loss chains: 0 violations at `ea4cab5`. |
| `Open`'s step (`boltOpened`) | Scope exp. B: 10/1,160 violations without the sync, 0 with it; `issues/bbolt-open-unsynced-meta-kill-then-power-loss.md` (12/1,160 at upstream). R3-0 negative controls: the same tester at the unfixed `743299d8` (§5.1, §5.2: the corruption shows once the db spans several pages and the consistent index is loaded as `bootstrapBackend` does; 0 at the D7 fork). The tester records `ciLast := ci` after the open, so a revert below what the open read is a violation even without corruption. |
| `Commit`'s two updates; the error arm keeps the flight | Code: `tx.go:171` (start), `:551/574` (pages), `:613/621` (meta). Exp. A's images at every event of the commit; an error after `:613` is the "in flight" row. |
| `named`, vanish, `"BoltNamed"` | Scope exp. A without the directory sync: "db file missing" 2/120; exp. C without it: 66/1,800 "db missing" after commits returned; with it: 0. R3-0: `syncDir` at every boot, 0 "db missing" after a returned commit. |
| `BoltOpen` on absent / zero-length file reads `∅` | `B/db.go:702-760` (init re-runs on zero metas; `nonissues/bbolt-init-not-crash-safe.md`); exp. C: "db absent before any commit returned" 31 images opened to the empty state. |
| Paths (§2.4) | by construction (names); no experiment. |

### 5.1 The R3-0 matrix

40 chains x 6 recorded incarnations x 30 images, seed 11 (`r0-matrix-s11.log`, `r0-negctl-unfixed.log`):

| bbolt | images | violations | posix / ordered / posix+g / ordered+g / kill | ci above ciLast | backend ahead of WAL mark | power loss after a kill | db absent |
|---|---|---|---|---|---|---|---|
| fork `ea4cab5` | 7,200 | **0** | 1611 / 1414 / 1376 / 1424 / 1375 | 5,273 | 6,442 | 2,218 | 18 |
| unfixed `743299d8` (kill prob. 0.8) | 7,200 | 2 (`failed to open database`) | 1576 / 1371 / 1405 / 1444 / 1404 | 5,149 | 6,341 | 3,365 | 51 |

**Two caveats** (the first is resolved in §5.2). (1) The negative control did **not** hit §1.6's kill-then-power corruption: the
driver picks power-loss images uniformly over the incarnation, and the bug needs the window before
the restarted incarnation's first sync (exp. B targeted it: 10/1,160). A targeted image mode (half the
images of an in-place incarnation before its first sync) is the next driver change. (2) Its two
violations are a **new finding** at both pins: a power loss inside the fork's `init`, between its two
fdatasyncs, with garbage in an unsynced meta sector (P4), leaves a file no `Open` accepts
(`nonissues/bbolt-fork-init-garbage-meta.md`, test reproduced at `ea4cab5`; the fixed run did not draw
such an image). `Open_kv_trk`'s error arm is `¬ dbOpenOk`, so the theorem would rest on a false
premise for those runs: **a fork fix is needed before R3-3's text can stand** (D7).

### 5.2 Controls with the targeted mode (40 x 6 x 30, seed 11, kill 0.8)

Targeted images: in an incarnation run in place after a kill or exit, a share (`-target`) of its images
is taken before its first fdatasync of the db file; `-killdb` kills only at a db sync, `-window` starts
the targeted images at the incarnation's first db write.

**Before option (b)** (the tester as in §5.1; target 0.6):

| bbolt | log | images | violations |
|---|---|---|---|
| unfixed `743299d8` | `r0-ctl-unfixed-743299d8.log` | 7,200 (2,431 targeted) | 2, both `failed to open database` (the init finding, chains 1 and 39) |
| fork `ea4cab5` (before D7) | `r0-ctl-fork-ea4cab5.log` | 7,200 (2,431 targeted) | 1, `failed to open database` (the init finding, chain 18) |
| fork `4f08974e` (D7) | `r0-ctl-fork-d7-b{0,10,20,30}.log` | 7,200 | **0** |
| unfixed, `-killdb -window -target 0.8`, 10 chains | `r0-pilot-unfixed-window.log` | 1,800 (913 targeted) | 0 |

None of these showed the kill-then-power corruption (§1.6). **Two causes**, both in the tester, not in
bbolt or the driver:

1. *One leaf.* The db fit in one leaf page, rewritten alternately at pages 2 and 3 (trace
   `verbose.log`): a reused page held a well-formed later state. Option (b) (etcd-grove-81): 100 keys,
   values 64-511 B (`fb7350d4e0`); the key bucket then has depth 2, a branch and 4+ leaves (`dbstat` on
   an image). Alone this still showed 0 (unfixed, `-killdb -window`, 4 chains: 0/720,
   `mp-pilot-unfixed.log`; standard mode, 40 chains: 7,110 images, 4 violations, 3 the init finding and 1 hung recorded incarnation, no corruption: `r0-ctl-unfixed-mp-b*.log`).
2. *Boot order.* Every restart that opened an existing db issued an fdatasync of it before any write
   (29 of 29, trace `mp-verbose2.log`): `mvcc.New`'s `ForceCommit` had no dirty page, because the
   pre-commit hook writes the consistent index only once it is loaded (`UnsafeUpdateConsistentIndex`
   skips 0), and the tester loaded it only after `mvcc.New`. That fdatasync makes the page cache's meta
   durable before any page is reused, so the window was empty. etcd's `bootstrapBackend` loads it right
   after `SetBackend` (`S/etcdserver/bootstrap.go:273`, the "restore consistentIndex" log), so etcd's
   next commit rewrites the meta bucket's page before its fdatasync. The tester now does the same
   (`bdecad79b8`, one call; the checks and Boot's statement are unchanged; goose translates it).
   Without this the tester was less faithful to etcd's bootstrap than intended, and hid the bug.

**After option (b) and the boot-order fix** (the tester at `bdecad79b8`):

| bbolt | mode | log | images | violations |
|---|---|---|---|---|
| unfixed `743299d8` | `-killdb -window -target 0.8` | `r0-ctl-unfixed-mpciw-b{0,10,20,30}.log` | 7,110 (3,359 targeted) | **127**: 116 kill-then-power corruption, 2 check crashes without a panic line, 8 the init finding, 1 hung recorded incarnation |
| fork `4f08974e` (D7) | `-killdb -window -target 0.8` | `r0-ctl-d7-mpciw-b{0,10,20,30}.log` | 7,200 (3,405 targeted) | **0** |
| unfixed `743299d8` | standard, target 0.6 | `r0-ctl-unfixed-mpci-b{0,10,20,30}.log` | 7,020 (2,359 targeted) | **16**: 11 kill-then-power corruption, 4 the init finding, 1 hung recorded incarnation |
| fork `4f08974e` (D7) | standard, target 0.6 | `r0-ctl-d7-mpci-b{0,10,20,30}.log` | 7,200 (2,431 targeted) | **0** |

The corruption signatures (unfixed, both modes): `assertion failed: Page expected to be: P, but self
identifies as N` (81: `Open` or a read follows the durable meta's tree into a page the restart
overwrote), `freepages: failed to get all reachable pages` (37: multiple references, keys out of
order under the branch), `invalid revision length: 3` (6: mvcc reads a leaf element from another
bucket), and the tester's own checks (3: `the consistent index is below a durable one`, `a revision
has a wrong key or value`). All are images of an incarnation run in place after a kill, in its window
before the first db fdatasync, mostly with P4 garbage (unsynced sectors of pages the restart reused).
The init finding (`failed to open database`, images early in a fresh db's first incarnation) is D7's,
absent at the fork. The 3 hung incarnations (unfixed runs only this time; the first D7 run had one
too) are a ptrace artifact: threads spinning in tracing stop, the same incarnation runs untraced in
under a second (`repro-hang/`); they were killed by hand after 6 minutes and count as "recorded
incarnation failed". The 2 crashes without a panic line are check incarnations that exited with no
`panic:` on stderr (the driver keeps only that line; images not kept).

Scope exp. B (`TestBoltKillThenPower`, bbolt-level: 10/1,160 without the sync, 0 with it) stays as
further evidence for the clause. The unfixed rows also support the Impact paragraph of
`issues/bbolt-open-unsynced-meta-kill-then-power-loss.md`: with `bootstrapBackend`'s order, etcd's
first commit after a restart writes pages before its first fdatasync. (This assumes the backend's
batch timer does not commit between `CreateMetaBucket` and that read, microseconds apart against a
100 ms default interval; if it did, that empty commit would sync first, as in the tester before
`bdecad79b8`.)

## 6. What R3-4..R3-7 build on this (not trusted)

- R3-4: the arm's ghost state, step specs (`wp_BoltOpen`, `wp_BoltBegin`, `wp_BoltSync`,
  `wp_BoltNamed`), the crash interpretation lemma, `syncDir`'s spec; Go: the tester's db path `.db`
  (if D2).
- R3-5: `newBackend`/`batchTx.commit`/`backend.Close` over both modes (the witness, or `dbTracked` with
  `boltFileAt` in `InvBackend` and the client's commit-point predicate); `bDisk` law.
- R3-6: `mvccImage_commit.law`, `srvBackendImg`.
- R3-7: the tester's proof and `etcd_mvcccrash_adequate`/`_safe`.

## 7. Decisions (2026-11-12, etcd-grove-81 under the user's delegation)

D1 (U), D2 (hidden name; the tester's db moves to `root/data/member/snap/.db`), D3, D4, D5, D6: **yes, as
recommended**. D7: **yes**: the fork's `Open` re-runs `init` when no meta validates and the file is exactly
init's four pages (local fork commit on `upamanyus/bbolt` `goose-lean-v2`, translation, pin move of both
bbolt projects and the go.mod pins, Open's proof re-checked; in progress, `notes/wal-crash-handoff/rung3-handoff.md`).
Upstream (main `622eada1`) has the gap too, as a case of bbolt#567 (closed as a documented known issue),
so the finding stays in `nonissues/` (its Notes say why). Controls: the driver's targeted mode (images of
an in-place incarnation before its first fdatasync of the db file, `-target`), rerun at `743299d8`
(unfixed), `ea4cab5` (before D7) and the D7 pin: §5.2.

## 7a. The decisions as requested

| # | Decision | Recommendation |
|---|---|---|
| D1 | The shape: tracked axioms (`Open_kv_trk`, `Tx.Commit_kv_trk`, `DB.Close_kv_trk`) and today's three weakened by `dbUntracked` (U), vs. separate worlds (S) or mandatory everywhere (M) (§3.1) | (U) |
| D2 | Tracked paths outside the WAL area with a hidden last element (§2.4): no change to W4a's texts; the tester's db becomes `root/data/member/snap/.db` (vs. tracked files under the area, which needs a `"WalCreate"` guard on bolt keys and a WAL-axiom change) | hidden name |
| D3 | `noSync`, `noGrowSync` fields in the backend's `OptsM` (`optsAt`'s model; `newBackend` sets them from `UnsafeNoFsync`) for `Open_kv_trk`'s premise | yes |
| D4 | Gate G1 (`fileHolds` never names a tracked path) recorded for rung 4/C6 | yes |
| D5 | `syncDir`'s model nondeterministic in its result, its spec an atomic update (§2.5) | yes |
| D7 | Fork fix for the init finding: `Open` re-runs `init` when no meta validates and the file is exactly init's four pages (no data to lose), with a test; pin move; Open's proof re-checked | yes, before R3-4 |
| D6 | No bolt axiom post gives a past-state fact; every step is the commit of a client update (§3.8, the coordinator's W4a.1 standard) | yes |
