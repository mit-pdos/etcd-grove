/- Lean-first (no Rocq counterpart).

# C-I1: bbolt's file after a power loss, at the backend's interface (interim axiom, etcd-dist D6)

`notes/etcd-dist-d6.md`, "Crash interim axioms" (A1 of §7). **Trusted**: three laws over two opaque
predicates, retired by a crash proof of bbolt over the file extension (`osfs/bboltfs`'s minibolt is the
start: `DBCrash.lean`, `BootP1.lean`). No proof uses them yet: the member's crash law
(`memberGen_crash.law`, task T7) is their consumer.

**The predicates.**
* `dbOpts γ` (persistent; formerly `dbSyncs`, whose name-durability part is gone: `dbCrash` now speaks of
  the inode, and the caller reads the name from the file extension's crash facts): the database `γ` was opened with `NoSync = false` and
  `NoGrowSync = false` (etcd's backend: `UnsafeNoFsync = false`, `backend.go:227-228`; not defrag's
  temporary database, opened with `NoSync = true`), and nothing about names. Its producer is not stated yet (tied to bbolt's persistent fields and the
  directory sync, to be reviewed with T7); until then nothing produces it and the laws below cannot be
  used (they hold vacuously).
* `BoltCrashWhole` (a crash premise, opaque, `dbCrash`'s hypothesis on the run's crash relation `Q`):
  bbolt files come back at whole-page sizes and with no checksum-validating torn meta.
* `dbCrashKeep γ path i0 Dl Dn pd` (exclusive): the crash record of the open database `γ`, whose file is at
  `path`: `Dn` is its committed data (the commit invariant's half, `dbHalf γ Dn`, is inside it), `Dl` the
  data its file falls back to if the commit that made `Dn` did not reach the disk; `pd` the commit
  announced in flight (`dbCrashKeep_announce`), whose new meta may be on disk before its commit point. It holds the claim on
  the name (`bPath γ path`) and the half; `dbCrashKeep_half` lends the half, `dbCrashKeep_close` gives
  both back.

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
* `dbCrashKeep_half`'s put-back: a change of the committed data (`S ≠ Dn`) is a commit point (the half
  combines with `ownDB`'s into `boltState γ 1`, which only bbolt's `Commit` updates), so the fallback
  becomes the previous committed data `Dn`; a put-back of the same data (a reader's access, an empty
  commit, whose meta records the same data) keeps the fallback.
* The name: `dbCrash` speaks of `γ`'s inode `i0` and asks that the crashed durable tree still name it;
  which inode `path` names after the crash is the file extension's own crash fact (a name is durable only
  after a directory sync; the fork `goose-lean-crashfixes` syncs after defrag's and the snapshot install's
  renames, `nonissues/etcd-backend-rename-without-dir-sync.md`). The record holds `bPath`, so a rename onto
  `path` closes it first (`dbCrashKeep_close`); a crash with the record closed is not covered by these laws.
* **Restricted to files past `init`** (`nonissues/bbolt-init-not-crash-safe.md`): a record exists only for
  an opened database (`dbCrashKeep_new` takes a write transaction, which `Open` gives only after `init`'s
  two syncs). The fork's `needsInit` recognizes a crash before `init`'s first sync, but a crash between
  its two syncs can tear both meta pages under the file extension's per-byte crash (each byte of the
  unsynced metas zero or new), after which `Open` finds no valid meta and fails (etcd's `newBackend`
  then panics). That window is outside this axiom; the member's first start must handle it (C-I3).

**Known limits.** The torn-meta checksum collision and the torn `Truncate` are the crash premise
`BoltCrashWhole`'s (review 2026-11-24, `notes/axiom-review/c-i1-bbolt-crash.md`). The receipt inside
`fileHoldsM` (`fileRcpt`, the txid's time receipt) is asserted at the new generation: sound only if
receipts persist across generations (not checked by the review). A kill without `sync`
(`nonissues/bbolt-restart-reuses-pages-of-unsynced-commit.md`) is outside the model.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBbolt
public import GooseLang.Ext.Fs.CrashTok

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

/-- (C-I1) **The database `γ` syncs** (persistent by its form): `γ` was opened with `NoSync = false` and
`NoGrowSync = false` (bbolt's fields `db.NoSync`, `db.NoGrowSync`, fixed at `Open`, `Inv/Bolt.lean`; etcd's
backend: `UnsafeNoFsync = false`, `backend.go:227-228`; never defrag's temporary database, opened with
`NoSync = true`). Producer pending: `Open`'s postcondition behind γ's ghost names (not an entailment from
persistent field cells, which a fresh heap could satisfy), with `UnsafeNoFsync = false` from the Go
configuration; until then every result over these laws is vacuous. -/
opaque dbOptsRaw [hG : HeapGS hlc GF] (γ : DBNames) : IProp GF := iprop(False)

/-- (C-I1) `dbOptsRaw`, persistent. -/
def dbOpts [hG : HeapGS hlc GF] (γ : DBNames) : IProp GF := iprop(<pers> dbOptsRaw γ)

/-- (C-I1) **A crash premise under which the files `I` come back whole enough for bbolt** (a world premise
on the run's crash relation, opaque until defined, as the WAL's `W1`; for the owner's packet, which needs
it written out with a check that some `Q` refining `OsCrash` satisfies it, and a configuration-C example in
`examples/osfs/semantics/`): a machine crash leaves each file of `I` at a size it had at a sync, or the
target of a `Truncate` completed or in flight (the file extension's `CrashFile` allows any size in range:
`DB.grow`'s `Truncate`); and a meta page (bbolt's pages 0 and 1) that validates (magic, version, FNV-64
checksum) equals, on its checksummed bytes, the contents of one write (old or new): torn meta pages happen
on Linux and stay allowed; only a torn mixture that validates is excluded (a probabilistic assumption on
FNV-64). Only while the file is an open bbolt database with no extending write since its last sync (a
received snapshot file before its rename grows by appends: not covered); the meta clause then reads "equals
the page's page-cache contents at some moment since the last sync" (a meta page split across two `pwrite`s).
The size part is a kernel fact that belongs in the file extension's `CrashFile` (an extending `ftruncate`
crashes to the old or the target size), leaving here only the FNV-64 clause. Reviews 2026-11-24/25. -/
opaque BoltCrashWhole : (Fs.Ino → Prop) → Fs.OsState → Fs.OsState → Prop := fun _ _ _ => False

/-- (C-I1) **The crash record of the open database `γ`, whose file is at `path`** (exclusive): its
committed data `Dn` (with the commit invariant's half), the data `Dl` its file falls back to, and the
commit announced in flight `pd`; its file is the inode `i0` (see the file header). -/
opaque dbCrashKeep [hG : HeapGS hlc GF] (γ : DBNames) (path : GoString) (i0 : Fs.Ino) (Dl Dn : Data)
    (pd : Option Data) : IProp GF := iprop(False)

end preds

section laws
attribute [local instance] GooseGlobalGS.gooseInvGS
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors}

/-- (C-I1, trusted) **A crash record from a fresh write transaction**: with the database opened syncing
(`dbOpts`), its file the inode `i0` (`boltIno`), the claim on its name, the commit invariant's half at the
committed data `D` and a live write transaction begun at `D`, the record at `(D, D)` with nothing announced.
Why the file on disk is `D`'s: the transaction excludes a commit in flight; the last commit of this opening
returned only after both its syncs (under `FsNoErrAll`, which `dbHalf`'s and `txLive`'s `onFs` carry); and
`Open` itself `fdatasync`s before it returns when `!NoSync` (fork `db.go:326`, `c5a6065d`), which covers a
file whose last commit was made by another opening with `NoSync` (defrag's temporary database). -/
axiom dbCrashKeep_new [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] (γ : DBNames) (path : GoString)
    (i0 : Fs.Ino) (D : Data) (tx : Loc) :
    ⊢ dbOpts (hlc := HasLC.hasLC) (GF := GF) γ -∗ onFs (GF := GF) iprop(bbolt.boltIno γ i0) -∗
      bPath (GF := GF) γ path -∗ dbHalf γ D -∗ txLive tx γ 1 (bbolt.TxView.wr D) ==∗
      dbCrashKeep γ path i0 D D none ∗ txLive tx γ 1 (bbolt.TxView.wr D)

/-- (C-I1, trusted) **A commit announced**: holding the write transaction begun at the committed `Dn`
with contents `S`, the record announces `S` (any earlier announcement was of a commit that did not take
effect: the transaction excludes another writer). To be applied before `Commit` (review 2026-11-24: the
new meta's bytes are crash candidates from its `pwrite`'s start, before the commit point). -/
axiom dbCrashKeep_announce [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] (γ : DBNames)
    (path : GoString) (i0 : Fs.Ino) (Dl Dn S : Data) (pd : Option Data) (tx : Loc) (G : GoString → Nat) :
    ⊢ dbCrashKeep γ path i0 Dl Dn pd -∗ txLive (GF := GF) tx γ 1 (wView Dn S G) ==∗
      dbCrashKeep γ path i0 Dl Dn (some S) ∗ txLive (GF := GF) tx γ 1 (wView Dn S G)

/-- (C-I1, trusted) **The record lends the commit invariant's half for one atomic step**: the half at
the committed data `Dn`, to an update (one mask-changing step: at most one commit point, `Commit`'s
atomic update) that gives it back at `Dn` or at the announced `S`, with `R`; a change moves the fallback
to `Dn` and clears the announcement. (Review 2026-11-24: a put-back wand kept across two commits was
unsound; a change to an unannounced value is not allowed.) -/
axiom dbCrashKeep_half [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] (γ : DBNames) (path : GoString)
    (i0 : Fs.Ino) (Dl Dn : Data) (pd : Option Data) (E : CoPset) (R : Data → IProp GF) :
    ⊢ dbCrashKeep γ path i0 Dl Dn pd -∗
      (dbHalf γ Dn ={E}=∗ ∃ S, dbHalf γ S ∗ ⌜S = Dn ∨ pd = some S⌝ ∗ R S) ={E}=∗
      ∃ S, dbCrashKeep γ path i0 (if S = Dn then Dl else Dn) S (if S = Dn then pd else none) ∗ R S

/-- (C-I1, trusted) **An announcement cleared**: holding a fresh write transaction at the committed `Dn`
(no change made, so no commit in flight), the announcement is dropped. -/
axiom dbCrashKeep_clear [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] (γ : DBNames)
    (path : GoString) (i0 : Fs.Ino) (Dl Dn : Data) (pd : Option Data) (tx : Loc) :
    ⊢ dbCrashKeep γ path i0 Dl Dn pd -∗ txLive (GF := GF) tx γ 1 (bbolt.TxView.wr Dn) ==∗
      dbCrashKeep γ path i0 Dl Dn none ∗ txLive (GF := GF) tx γ 1 (bbolt.TxView.wr Dn)

/-- (C-I1, trusted) **The record closed**, with nothing announced (review 2026-11-25: closing with a stale
announcement would let a commit of an unannounced change land while the record claimed the announced
one): the claim on the name and the half back (to close the database, or to rename another file onto
`path`). -/
axiom dbCrashKeep_close [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] (γ : DBNames) (path : GoString)
    (i0 : Fs.Ino) (Dl Dn : Data) :
    dbCrashKeep γ path i0 Dl Dn none ⊢ bPath (GF := GF) γ path ∗ dbHalf γ Dn

/-- (C-I1, trusted) **bbolt's file after a power loss**: under the crash premise `BoltCrashWhole` for the
database's inode `i0`, from the old generation's record `(i0, Dl, Dn, pd)`, its `crashed`, and the file
system's crash rest (with the files `Dx` other crash lemmas took, not `i0`) of a crash whose durable tree
still names `i0` (`Named`: the caller learns which inode a name holds from the file extension's own crash
facts; a name not made durable by a directory sync may name another inode, review 2026-11-24): the inode
`i0` holds a database with the data `Dl`, `Dn` or the announced commit's (bbolt's `fileHoldsM`: whole,
every byte durable), and the crash rest with `i0` taken. Open item (review 2026-11-24): `fileHoldsM`'s
receipt of the in-flight meta's txid is asserted here; the record should carry it (`announce` taking it). -/
axiom dbCrash [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt] [G : GooseGlobalGS HasLC.hasLC GF]
    (Q : Fs.OsState → Fs.OsState → Prop) (L L' : GooseLocalGS GF) (γ : DBNames) (path : GoString)
    (i0 : Fs.Ino) (Dl Dn : Data) (pd : Option Data)
    (hQ : ∀ st st', Q st st' → BoltCrashWhole (· = i0) st st')
    (Dx : List Fs.Ino) (hi : i0 ∉ Dx) (V' : Fs.Hist) (hN : Fs.Named V'.now i0) (E : CoPset) :
    ⊢ dbCrashKeep (hG := ⟨G, L⟩) γ path i0 Dl Dn pd -∗ crashed (hC := L.goose_crashGS) -∗
      Fs.crashRest Q (Fs.gooseOsGS (L := L)) (Fs.gooseOsGS (L := L')) Dx false V' ={E}=∗
      ∃ D' : Data, ⌜D' = Dl ∨ D' = Dn ∨ pd = some D'⌝ ∗
        bbolt.fileHoldsM (hG := ⟨G, L'⟩) i0 D' ∗
        Fs.crashRest Q (Fs.gooseOsGS (L := L)) (Fs.gooseOsGS (L := L')) (i0 :: Dx) false V'

end laws

end backend
end EtcdGrove
end Perennial
