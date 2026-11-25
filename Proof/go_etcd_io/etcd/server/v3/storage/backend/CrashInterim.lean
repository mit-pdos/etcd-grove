/- Lean-first (no Rocq counterpart).

# C-I1: bbolt's file after a power loss, at the backend's interface (interim axiom, etcd-dist D6)

`notes/etcd-dist-d6.md`, "Crash interim axioms" (A1 of §7). **Trusted**: six laws over two opaque
predicates (`dbOpts`, `dbCrashKeep`) and the crash premise `BoltCrashWhole`, retired by a crash proof of bbolt over the file extension (`osfs/bboltfs`'s minibolt is the
start: `DBCrash.lean`, `BootP1.lean`). No proof uses them yet: the member's crash law
(`memberGen_crash.law`, task T7) is their consumer.

**The predicates.**
* `dbOpts γ` (persistent, `DbOpts.lean`): the database `γ` was opened with `NoSync = false` and
  `NoGrowSync = false`; produced by `storage.OpenBackend`'s post when the configuration's
  `UnsafeNoFsync` is `false` (etcd's default), so the laws below are usable for etcd's backend.
* `BoltCrashWhole I` (a crash premise, a definition, `dbCrash`'s hypothesis on the run's crash relation
  `Q`): a meta page of a file of `I` with no size change since its last sync that validates after a
  crash is not a torn mix (FNV-64a, probabilistic). The crash's size is the file extension's rule
  (`CrashFile`: an `ftruncate`'s target exactly, so whole pages for bbolt's files).
* `dbCrashKeep γ i0 Dl Dn pd` (exclusive): the crash record of the open database `γ`, whose file is the
  inode `i0`: `Dn` is its committed data (the commit invariant's half, `dbHalf γ Dn`, is inside it), `Dl` the
  data its file falls back to if the commit that made `Dn` did not reach the disk; `pd` the commit
  announced in flight (`dbCrashKeep_announce`), whose new meta may be on disk before its commit point. It holds the half and
  no claim on any name (restated 2026-11-25 for T10, `notes/axiom-review/c-i1-nopath.md`: the snapshot
  install renames onto `db` while the old backend still commits); `dbCrashKeep_half` lends the half,
  `dbCrashKeep_close` gives it back.

**Why the laws are true of bbolt (fork `upamanyus/bbolt` at `ca88bb6a`, `etc/goose.py`'s pin) over the
file extension's crash (`OsCrash`, `GooseLang/Ext/Fs/Impl.lean`).**
* A write transaction holds `rwlock`; `Tx.Commit` writes the dirty pages and the freelist, `fdatasync`s,
  writes the meta page at slot `txid % 2` (its commit point: the update of the committed data,
  `Tx.Commit.spec`), `fdatasync`s again (`tx.go:572`, `:619`, both under `!db.NoSync`), then returns.
  Under `FsNoErrAll` (the run's file semantics: no file step fails) a commit that reached its commit
  point returns only after both syncs. So while one holds a fresh write transaction at the committed data
  `D` (`dbCrashKeep_new`), the last commit returned and the file on disk is `D`'s.
* Between a commit point and its second sync, the file on disk holds the new meta page whole, not at all,
  or torn (the crash keeps each byte of the unsynced range independently, `CrashFile`). The other meta
  slot holds the previous commit's meta, synced; the pages the new meta points at are synced (the first
  `fdatasync`) and the previous tree's pages are not overwritten (bbolt frees a commit's pages only for
  transactions after it: the pages the in-flight commit writes were free at the previous commit). `Open`
  validates both metas (magic, version, checksum) and takes the valid one with the larger txid: the new
  one if whole, else the previous one. So the file holds `Dn` or `Dl`.
* The size: bbolt never shrinks its file; `DB.grow` (in `Commit`, before any page is written) truncates
  it up to a page-aligned size and `fsync`s (`!NoGrowSync`); the file extension's crash leaves a size
  among those since the last sync, an `ftruncate`'s exactly (`CrashFile`'s `szCrash`), so a page-aligned
  size at least the synced high-water mark's (`fileHoldsM`'s whole pages).
* `dbCrashKeep_half`'s put-back: a change of the committed data (`S ≠ Dn`) is a commit point (the half
  combines with `ownDB`'s into `boltState γ 1`, which only bbolt's `Commit` updates), so the fallback
  becomes the previous committed data `Dn`; a put-back of the same data (a reader's access, an empty
  commit, whose meta records the same data) keeps the fallback.
* The name: `dbCrash` speaks of `γ`'s inode `i0` and asks that the crashed durable tree still name it;
  which inode the database's path names after the crash is the file extension's own crash fact (a name is durable only
  after a directory sync; the fork `goose-lean-crashfixes` syncs after defrag's and the snapshot install's
  renames, `nonissues/etcd-backend-rename-without-dir-sync.md`). The record holds no name: a rename onto
  or away from the database's path leaves the record true of its inode (a rename does not change an inode's
  bytes), and `dbCrash` is usable only when the crashed tree still names `i0` (`Named`); measured on
  configuration C across the snapshot install's rename window (`notes/axiom-review/c-i1-nopath.md`).
* **Restricted to files past `init`** (`issues/bbolt-init-not-crash-safe.md`): a record exists only for
  an opened database (`dbCrashKeep_new` takes a write transaction, which `Open` gives only after `init`'s
  two syncs). The fork's `needsInit` recognizes a crash before `init`'s first sync, but a crash between
  its two syncs can tear both meta pages under the file extension's per-byte crash (each byte of the
  unsynced metas zero or new), after which `Open` finds no valid meta and fails (etcd's `newBackend`
  then panics). That window is outside this axiom; the member's first start must handle it (C-I3).

**Known limits.** The torn-meta checksum collision is the crash premise `BoltCrashWhole`'s; the size a
crash leaves inside `DB.grow` is the file extension's (an `ftruncate`'s target exactly, 2026-11-25:
until then a second clause of the premise; reviews in `notes/axiom-review/c-i1-bbolt-crash.md`). The receipt inside
`fileHoldsM` (`fileRcpt`, the txid's time receipt) is asserted at the new generation: sound only if
receipts persist across generations (not checked by the review). A kill without `sync`
(`nonissues/bbolt-restart-reuses-pages-of-unsynced-commit.md`) is outside the model.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBbolt
public import GooseLang.Ext.Fs.CrashTok
public import GooseLang.Ext.Fs.Tests
public import Spec.hash.fnv.Model
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.DbOpts

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace backend

open Iris Iris.BI Classical

section preds
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors}

/-- A little-endian number. -/
def leNat (l : List w8) : Nat := l.foldr (fun b acc => b.toNat + 256 * acc) 0

/-- What bbolt's `Meta.Validate` checks of the 64 bytes `r` of a meta (the page's bytes 16 to 80, after
its header, `Page.Meta()`): the magic `0xED0CDAED`, the version `2`, and the checksum (bytes 56 to 64)
the FNV-64a of the first 56 (`Meta.Sum64`; bbolt's model `Model/Meta.lean`'s `metaValid`, stated here on
the raw little-endian bytes so as not to import bbolt's internals). -/
def boltMetaValidates (r : List w8) : Prop :=
  leNat (r.take 4) = 0xED0CDAED ∧ leNat ((r.drop 4).take 4) = 2 ∧
    leNat (r.drop 56) = (hash.fnv.fnv64a (r.take 56)).toNat

/-- (C-I1) **The crash premise: a meta page that validates after a crash is not torn** (a premise on
the run's crash relation, `dbCrash`'s `hQ`; trusted, a probabilistic assumption on FNV-64a). For each
file `i` of `I` (`dbCrash`: the open database's inode) whose size has not changed since its last
successful sync and which has no change in flight past its end (bbolt's file at every moment but
`DB.grow`'s window between its `Truncate` and its `Sync`, during which no meta page has been written
since the sync), at a crash from `st` to `st'`: if meta page `j < 2` of the crash image, as its page
cache holds it, validates (`boltMetaValidates`: magic, version, and the FNV-64a checksum of the meta's
first 56 bytes, `Meta.Validate`), then those 56 bytes are the slot as of one change `n` (each its value as of
`n`, `valAt`). The file extension's crash (`CrashFile`) keeps each byte any one of its candidates,
independently (measured on Linux: a page can reach the disk torn mid-sector, or any mix of two writes,
`notes/axiom-review/fs-v2-r6/e2e/`), so a crash can tear a meta page being written; the premise says
only that a torn mix does not collide on its checksum, bbolt's own assumption (its `Open` takes the
valid meta with the larger txid). bbolt writes a meta page with one page-aligned `WriteAt` of the
whole page (`Tx.writeMeta`) and the extension's writes land page-aligned prefixes, so each state "as
of one change" of a slot is a whole meta that bbolt wrote (or the synced one). The size a crash
leaves is not part of the premise: the extension's own rule gives it (`CrashFile`'s `szCrash`: an
`ftruncate`'s target exactly, so `DB.grow`'s page-aligned truncate leaves a page-aligned size,
`examples/osfs/semantics/data_truncate_size_exact.go`). Satisfiable from every reachable state with a
crash (`boltCrashWhole_exists`); the same as minibolt's P1 (`BootP1.lean`) on bbolt's meta layout,
restricted to `I` and to files with no size change since their last sync (reviews 2026-11-24/25,
`notes/axiom-review/c-i1-bbolt-crash.md`). -/
def BoltCrashWhole (I : Fs.Ino → Prop) (st st' : Fs.OsState) : Prop :=
  ∀ (i : Fs.Ino) (f f' : Fs.OsFile), I i → st.fs.files !! i = some f → st'.fs.files !! i = some f' →
    f.sizeLo = f.size → f.sizeHi = f.size →
    (∀ t c, st.proc.inflight !! t = some c → c.ino = i → c.target ≤ f.size) →
    ∀ j < 2, 4096 * j < f'.size →
      boltMetaValidates ((List.range 64).map fun k => f'.cache (4096 * j + 16 + k)) →
      ∃ n, ∀ k < 56, f'.cache (4096 * j + 16 + k) = Fs.valAt (f.cand (4096 * j + 16 + k)) n

/-- **`BoltCrashWhole` is never vacuous at a crash**: from every reachable state (`CacheOk`) with a
machine crash, the crash that leaves every named file as of its last sync (`Tests.durCrash`) is a
crash satisfying it (every byte its candidate of stamp 0). -/
theorem boltCrashWhole_exists (I : Fs.Ino → Prop) {st st' : Fs.OsState} (hok : Fs.Tests.CacheOk st)
    (hc : Fs.MachineCrash st st') : ∃ st'', Fs.OsCrash st st'' ∧ BoltCrashWhole I st st'' := by
  refine ⟨Fs.Tests.durCrash st st', Fs.Tests.durCrash_machine hok hc, ?_⟩
  intro i f f' _ hf hf' _ _ _ j _ hsz _
  refine ⟨0, fun k _ => ?_⟩
  rw [Fs.Tests.durCrash_files, hf] at hf'
  split at hf'
  · simp only [Option.map_some, Option.some.injEq] at hf'
    subst hf'
    simp only [Fs.Tests.durFile, Fs.OsFile.ofDisk] at hsz ⊢
    rw [Fs.diskByte, if_pos]
    simp only [Fs.pageIn, decide_eq_true_eq]
    omega
  · cases hf'

/-- (C-I1) **The crash record of the open database `γ`, whose file is the inode `i0`** (exclusive): its
committed data `Dn` (with the commit invariant's half), the data `Dl` its file falls back to, and the
commit announced in flight `pd` (see the file header). It claims no name. -/
opaque dbCrashKeep [hG : HeapGS hlc GF] (γ : DBNames) (i0 : Fs.Ino) (Dl Dn : Data)
    (pd : Option Data) : IProp GF := iprop(False)

end preds

section laws
attribute [local instance] GooseGlobalGS.gooseInvGS
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors}

/-- (C-I1, trusted) **A crash record from a fresh write transaction**: with the database opened syncing
(`dbOpts`), its file the inode `i0` (`boltIno`), the commit invariant's half at the
committed data `D` and a live write transaction begun at `D`, the record at `(D, D)` with nothing announced
(no claim on the file's name: the argument is about the inode, which a rename does not change).
Why the file on disk is `D`'s: the transaction excludes a commit in flight; the last commit of this opening
returned only after both its syncs (under `FsNoErrAll`, which `dbHalf`'s and `txLive`'s `onFs` carry); and
`Open` itself `fdatasync`s before it returns when `!NoSync` (fork `db.go:326`, `c5a6065d`), which covers a
file whose last commit was made by another opening with `NoSync` (defrag's temporary database). -/
axiom dbCrashKeep_new [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] (γ : DBNames)
    (i0 : Fs.Ino) (D : Data) (tx : Loc) :
    ⊢ dbOpts (hlc := HasLC.hasLC) (GF := GF) γ -∗ onFs (GF := GF) iprop(bbolt.boltIno γ i0) -∗
      dbHalf γ D -∗ txLive tx γ 1 (bbolt.TxView.wr D) ==∗
      dbCrashKeep γ i0 D D none ∗ txLive tx γ 1 (bbolt.TxView.wr D)

/-- (C-I1, trusted) **A commit announced**: holding the write transaction begun at the committed `Dn`
with contents `S`, the record announces `S` (any earlier announcement was of a commit that did not take
effect: the transaction excludes another writer). To be applied before `Commit` (review 2026-11-24: the
new meta's bytes are crash candidates from its `pwrite`'s start, before the commit point). -/
axiom dbCrashKeep_announce [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] (γ : DBNames)
    (i0 : Fs.Ino) (Dl Dn S : Data) (pd : Option Data) (tx : Loc) (G : GoString → Nat) :
    ⊢ dbCrashKeep γ i0 Dl Dn pd -∗ txLive (GF := GF) tx γ 1 (wView Dn S G) ==∗
      dbCrashKeep γ i0 Dl Dn (some S) ∗ txLive (GF := GF) tx γ 1 (wView Dn S G)

/-- (C-I1, trusted) **The record lends the commit invariant's half for one atomic step**: the half at
the committed data `Dn`, to an update (one mask-changing step: at most one commit point, `Commit`'s
atomic update) that gives it back at `Dn` or at the announced `S`, with `R`; a change moves the fallback
to `Dn` and clears the announcement. (Review 2026-11-24: a put-back wand kept across two commits was
unsound; a change to an unannounced value is not allowed.) -/
axiom dbCrashKeep_half [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] (γ : DBNames)
    (i0 : Fs.Ino) (Dl Dn : Data) (pd : Option Data) (E : CoPset) (R : Data → IProp GF) :
    ⊢ dbCrashKeep γ i0 Dl Dn pd -∗
      (dbHalf γ Dn ={E}=∗ ∃ S, dbHalf γ S ∗ ⌜S = Dn ∨ pd = some S⌝ ∗ R S) ={E}=∗
      ∃ S, dbCrashKeep γ i0 (if S = Dn then Dl else Dn) S (if S = Dn then pd else none) ∗ R S

/-- (C-I1, trusted) **An announcement cleared**: holding a fresh write transaction at the committed `Dn`
(no change made, so no commit in flight), the announcement is dropped. -/
axiom dbCrashKeep_clear [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] (γ : DBNames)
    (i0 : Fs.Ino) (Dl Dn : Data) (pd : Option Data) (tx : Loc) :
    ⊢ dbCrashKeep γ i0 Dl Dn pd -∗ txLive (GF := GF) tx γ 1 (bbolt.TxView.wr Dn) ==∗
      dbCrashKeep γ i0 Dl Dn none ∗ txLive (GF := GF) tx γ 1 (bbolt.TxView.wr Dn)

/-- (C-I1, trusted) **The record closed**, with nothing announced and holding a live write transaction
begun at the committed `Dn` (any pending changes `S`: no commit is in flight while it is live, it holds
`rwlock` and `Commit` consumes it; reviews 2026-11-25: closing with a stale announcement, or without the
transaction, inside `Commit`'s atomic update after the new meta's `pwrite` started, would let a commit of
an unannounced change land while the record claimed less): the half back (to close the database), and the
transaction. (Restated 2026-11-25: it no longer gives back a claim on the name, which the record no longer
holds.) -/
axiom dbCrashKeep_close [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] (γ : DBNames)
    (i0 : Fs.Ino) (Dl Dn S : Data) (G : GoString → Nat) (tx : Loc) :
    dbCrashKeep γ i0 Dl Dn none ∗ txLive (GF := GF) tx γ 1 (wView Dn S G) ⊢
      dbHalf γ Dn ∗ txLive (GF := GF) tx γ 1 (wView Dn S G)

/-- (C-I1, trusted) **bbolt's file after a power loss**: under the crash premise `BoltCrashWhole` for the
database's inode `i0`, from the old generation's record `(i0, Dl, Dn, pd)`, its `crashed`, and the file
system's crash rest (with the files `Dx` other crash lemmas took, not `i0`) of a crash whose durable tree
still names `i0` (`Named`: the caller learns which inode a name holds from the file extension's own crash
facts; a name not made durable by a directory sync may name another inode, review 2026-11-24): the inode
`i0` holds a database with the data `Dl`, `Dn` or the announced commit's (bbolt's `fileHoldsM`: whole,
every byte durable), and the crash rest with `i0` taken. Open item (review 2026-11-24): `fileHoldsM`'s
receipt of the in-flight meta's txid is asserted here; the record should carry it (`announce` taking it). -/
axiom dbCrash [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt] [G : GooseGlobalGS HasLC.hasLC GF]
    (Q : Fs.OsState → Fs.OsState → Prop) (L L' : GooseLocalGS GF) (γ : DBNames)
    (i0 : Fs.Ino) (Dl Dn : Data) (pd : Option Data)
    (hQ : ∀ st st', Q st st' → BoltCrashWhole (· = i0) st st')
    (Dx : List Fs.Ino) (hi : i0 ∉ Dx) (V' : Fs.Hist) (hN : Fs.Named V'.now i0) (E : CoPset) :
    ⊢ dbCrashKeep (hG := ⟨G, L⟩) γ i0 Dl Dn pd -∗ crashed (hC := L.goose_crashGS) -∗
      Fs.crashRest Q (Fs.gooseOsGS (L := L)) (Fs.gooseOsGS (L := L')) Dx false V' ={E}=∗
      ∃ D' : Data, ⌜D' = Dl ∨ D' = Dn ∨ pd = some D'⌝ ∗
        bbolt.fileHoldsM (hG := ⟨G, L'⟩) i0 D' ∗
        Fs.crashRest Q (Fs.gooseOsGS (L := L)) (Fs.gooseOsGS (L := L')) (i0 :: Dx) false V'

end laws

end backend
end EtcdGrove
end Perennial
