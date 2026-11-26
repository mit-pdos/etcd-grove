/-
bbolt as the backend sees it: a key-value contract over the **proved** bbolt's API
(`Spec/go_etcd_io/bbolt/Api.lean`; stage S1 of `notes/bbolt-integration-plan.md`, D-I1 and D-I2,
2026-11-17). Until then the predicates below were axioms (the trust boundary, as the btree's
`ownBTree` was before the btree was verified; `notes/decisions.md`, "The backend: the buffers,
bbolt as a key-value contract, the locks and the views"); now each is a definition over bbolt's
sealed predicates, and the `_kv` specs (`Spec/go_etcd_io/bbolt/*_kv*.lean`) are corollaries of
bbolt's proved specs; since S3e (2026-11-17) `Open_kv` and `DB.Close_kv` too, over bbolt's
error-free `Open` and `Close` in the tree's shared mode, and the file predicates are definitions.

**The file extension's instances, packed (D-I1).** bbolt's API and specs are stated over the Linux
file extension (`[ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]`); the backend and its clients take
no such binders. `FsCtx` bundles the three (with the `os` structs' field facts and, since S3e,
`FsNoErrAll`: the semantics' steps do not fail on files, the premise of bbolt's error-free `Open` and
`Close`); `HasExt.sem_eq` pins the semantics to the program's, so
`FsCtx` is a subsingleton (`FsCtx.eq`) and `theFs` names its one value, if any (a classical
choice). Every predicate is `onFs` of bbolt's, at `theFs` (`False` where there is none); with the
instances in scope, `theFs_eq` rewrites `theFs` to them (`onFs_eq`).

**Data.** A database is its top-level buckets' contents (`Data`, etcd has no nested buckets);
a bucket's cursor order is its sorted entry list (`bktEnts`, bbolt's by `bktEnts_eq`).

**Predicates** (over bbolt's, whose names `γ : DBNames := bbolt.BoltName` are):
- `ownDB db γ D`: the open database `db` (`isBolt`) with committed data `D`, half of it
  (`boltState γ (1/2) D`; the other half, `dbHalf γ D`, is the backend's commit invariant's:
  backend-snapshot B1, 2026-11-20), and (S3e) what it keeps of its file (`dbRestF γ`: since S5 the inode and the
  closer token only); `wrTok γ`: `emp` (bbolt's writer needs no token: `Begin(true)` waits for
  its lock); `isDB db γ`: `db` is the database `γ` (persistent).
- `txLive tx γ q T`: the transaction `tx` of `γ`, live, with the view `T` (`boltTx`; fractional;
  not timeless, `txLive_later`). A read transaction over the snapshot `D` is `txLive tx γ q
  (TxView.ro D)`; each bucket of a view holds fewer than `2 ^ 61` entries (`txLive_size`).
  `txBytes tx γ s b` (persistent): `s` holds `b` while `tx` is live (`txBytes_acc`).
- `ownWTxG tx γ D S G`: the write transaction, begun at the committed `D`, contents `S` now,
  each bucket name `n` at generation `G n`: `txLive` at the view `wView D S G`; `ownWTx tx γ D S`
  is it at some generations. `wBkt tx γ b n g` (persistent): `b` is `tx`'s handle of the bucket
  named `n` at generation `g` (`boltBkt`: of the write transaction, or of a read transaction, whose
  generations are `0`); the write transaction owns its handles' `FillPercent` field
  (`ownWTxG_fill`: any value but a NaN). `DeleteBucket` bumps the name's generation, so a handle of
  a deleted bucket is not current: `Put`/`Delete`/`Cursor` take a handle at the current generation
  only (`nonissues/bbolt-deleted-bucket-handle.md`).
- `ownCur tx γ c T es pos`: a cursor of `tx`, made at the view `T`, over the entries `es`, at
  `pos` (`none`: not positioned; `some i`: at the `i`-th, `es.length` past the end).
- `txDone tx` (persistent): `tx` was committed or rolled back (its `Stats` can be read);
  `txDB tx γ db` (persistent): `tx`'s database.
- `fileHolds path D` (S3e; an axiom until then): the database file at `path` holds `D` (what
  `bolt.Open` reads; what `DB.Close` gives back): `path` is `d/b`, with the path of the directory
  `d`, a share of the call permission and the whole claim on the name `b` in the tree's shared mode,
  and `b` naming a file that holds `D` (bbolt's `fileHolds`) or nothing and `D = ∅` (`nameHolds`).
- `dbFile db γ path` (S3e; an axiom until then, without `γ`; persistent): the open database `db`
  named `γ` is the file at `path`: `γ.ns = dbNs path` (`Open_kv` opens it in that namespace).
- (S5, 2026-11-18) `bPath γ path` (exclusive): the claim on the name `path`, naming the open
  database `γ`'s inode, which `New` gives its caller (until S5 kept in `ownDB`), so that the caller
  may rename another file onto the name while the database is open; `bClosed γ D`: the closed
  database's inode holding `D`, what `Close` gives back; `bPath_join` makes the two the file at the
  name again (`fileHolds`), by the inodes' agreement (`bbolt.boltIno_agree`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBuffer
public import Spec.go_etcd_io.bbolt.Api
public import Spec.go_etcd_io.bbolt.ApiS
public import Spec.go_etcd_io.bbolt.ApiIno
public import GooseLang.Ext.Fs.TreeSharedRes
public import GooseLang.Ext.Fs.FilteredSem
public import GooseLang.Ext.Fs.PathFitsLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace backend

open Iris Iris.BI Iris.ProofMode

/-- A bucket's contents. -/
abbrev BktData := GMap GoString GoString

/-- A database's data: its top-level buckets by name. -/
abbrev Data := GMap GoString BktData

/-- A bucket's entries in cursor order: sorted by key. -/
def bktEnts (m : BktData) : List Ent := m.toList.mergeSort entLe

/-- bbolt's `MaxKeySize`. -/
def maxKeySize : Nat := 32768

/-- bbolt's `MaxValueSize`. -/
def maxValueSize : Nat := 2 ^ 31 - 2

/-- The first index of a sorted entry list whose key is not below `k` (`Cursor.Seek`). -/
def seekIdx (es : List Ent) (k : GoString) : Nat :=
  (es.takeWhile (fun e => decide (strLt e.1 k))).length

/-- The backend's cursor order is bbolt's. -/
theorem bktEnts_eq (m : BktData) : bktEnts m = bbolt.bktEnts m := rfl

/-- The backend's `seekIdx` is bbolt's. -/
theorem seekIdx_eq (es : List Ent) (k : GoString) : seekIdx es k = bbolt.seekIdx es k := rfl

/-- **bbolt's `Close` succeeds** (opaque, a named premise about the program's environment; D22
receiver epochs, S8d, W7, 2026-10-25): `db.Close()` does not fail for the environment's reasons
(unmapping the file, releasing its lock, closing it: I/O). `DB.Close_kv`'s axiom gives
`¬ dbCloseOk` on an error; `storage.snapOpensOk` excludes it (`applySnapshot`'s goroutine closing
the old backend panics on an error, `server.go:1137`). (S3e, 2026-11-17) `DB.Close_kv` is a theorem
now, with no error case (the semantics' steps do not fail on files, `FsNoErrAll`): nothing gives
`¬ dbCloseOk` any more, and it is `True` (a definition): the specs that still state it as a premise
or an error case are unchanged, their premise trivial and their error case `False`. -/
def dbCloseOk : Prop := True

/-- **bbolt's `Open` succeeds** (opaque, a named premise about the program's environment, as
`dbCloseOk`; 2026-11-08, the user's decision for mvccrand's closed theorem: "an assumption that the
backend opening doesn't panic"): `bolt.Open(path, …)` of the program's database files does not fail
for the environment's reasons (the file's creation, lock, `mmap` of the initial size, reads and the
first meta pages' writes: I/O, address space, another process holding the lock). `Open_kv`'s axiom
gives `¬ dbOpenOk` on an error, so `backend.New`, which panics on one (`backend.go:236`), panics
only under `¬ dbOpenOk`. The server's `storage.dbOpensOk` (`InvOpen.lean`) states the same of
the files `storage.OpenBackend` opens, for its own axiom. (S3e, 2026-11-17) `Open_kv` is a theorem
now, with no error case: nothing gives `¬ dbOpenOk` any more, and it is `True` (a definition), as
`dbCloseOk`. -/
def dbOpenOk : Prop := True

/-- The ghost names of a database: bbolt's (D-I2; until S1 a structure of two names). -/
abbrev DBNames := bbolt.BoltName

/-! ## The file extension's instances (D-I1) -/


section fsctx
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} (GF : BundledGFunctors) [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

open Fs in
/-- **The file system does not fail** (S3e, 2026-11-17): the steps of the semantics satisfy
`NoIoErr` and `NoMapLockErr` for an `IoSet` covering every file and every path (the premises of
bbolt's error-free `Open` and `Close`, `Open_sharedNoErr.spec`, `DB.Close_ownNoErr.spec`). A class
(a proposition), so that `FsCtx` stays a subsingleton. -/
class FsNoErrAll [ExtSemantics fsExt] : Prop where
  ok : ∃ Sio : IoSet, (∀ st i, Sio.ino st i) ∧ (∀ p, Sio.path p) ∧
    FsStepSat (NoIoErr Sio) ∧ FsStepSat (NoMapLockErr Sio)

open Fs in
/-- **The Linux file extension's instances**, packed: its semantics, the model's facts about it,
its place in the program's extensions (with the global `fs_interp`). (Until 2026-11-24 it also held
the field facts of the then trusted `os.file` and `os.fileStat`, `os.file.FieldAssumptions`; Go-model
overlays S5 made both translated layouts; `GF` stays a parameter, now unused, so that its uses
are unchanged.) -/
structure FsCtx (GF : BundledGFunctors) where
  S : ExtSemantics fsExt
  ok : @FsSemOk S
  has : @HasExt _ _ _ fsExt S fs_interp
  ne : @FsNoErrAll S

/-- **There is at most one `FsCtx`**: `HasExt.sem_eq` pins the semantics to the program's (the
position of `fsExt` in the list of extensions is a proof of a proposition), and the other
fields are proofs. -/
theorem FsCtx.eq (a b : FsCtx GF) : a = b := by
  obtain ⟨S1, ok1, h1, _⟩ := a
  obtain ⟨S2, ok2, h2, _⟩ := b
  have hS : S1 = S2 := h1.sem_eq.symm.trans h2.sem_eq
  subst hS
  rfl

instance FsCtx.subsingleton : Subsingleton (FsCtx GF) := ⟨FsCtx.eq GF⟩

open Classical in
/-- **The program's file-extension instances**, if it has them (a classical choice of the one
value of `FsCtx`). -/
def theFs : Option (FsCtx GF) :=
  if h : Nonempty (FsCtx GF) then some (Classical.choice h) else none

open Fs in
/-- With the instances in scope, `theFs` is them. -/
theorem theFs_eq [S : ExtSemantics fsExt] [ok : FsSemOk] [has : HasExt fsExt]
 [ne : FsNoErrAll] :
    theFs GF = some ⟨S, ok, has, ne⟩ := by
  unfold theFs
  rw [dif_pos ⟨⟨S, ok, has, ne⟩⟩]
  exact congrArg some (FsCtx.eq GF _ _)

end fsctx

section preds
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

open Fs

/-- **A proposition over the file extension's instances, at the program's** (`False` if it has
none). -/
def onFs (f : ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt], IProp GF) : IProp GF :=
  match theFs GF with
  | some c => @f c.S c.ok c.has
  | none => iprop(False)

/-- `onFs` with the instances in scope. -/
theorem onFs_eq [S : ExtSemantics fsExt] [ok : FsSemOk] [has : HasExt fsExt]
 [FsNoErrAll]
    (f : ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt], IProp GF) :
    onFs f = @f S ok has := by
  unfold onFs; rw [theFs_eq]

theorem onFs_some {c : FsCtx GF} (h : theFs GF = some c)
    (f : ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt], IProp GF) :
    onFs f = @f c.S c.ok c.has := by
  unfold onFs; rw [h]

theorem onFs_none (h : theFs GF = none)
    (f : ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt], IProp GF) :
    onFs (GF := GF) f = iprop(False) := by
  unfold onFs; rw [h]

/-! ### The database files (S3e) -/

/-- **The namespace of the database opened at `p`** (S3e): `Open` is called with it, so that a
database's names (`γ.ns`) record its path (`dbFile`). -/
def dbNs (p : GoString) : Namespace := ndot (ndot nroot "etcdBackendDb") (p.map (fun c : w8 => c.toNat))

theorem dbNs_inj {p p' : GoString} (h : dbNs p = dbNs p') : p = p' := by
  unfold dbNs ndot at h
  have h1 := (List.cons.inj h).1
  have h2 := Pos.encode_inj h1
  exact (List.map_inj_right (fun a b hab => BitVec.eq_of_toNat_eq hab)).mp h2

theorem dbNs_osN (p : GoString) : (↑(dbNs p) : CoPset) ## ↑osN := by
  unfold dbNs osN
  apply ndot_preserve_disjoint_l
  exact ndot_ne_disjoint nroot (show ("etcdBackendDb" : String) ≠ "osfs" by decide)

/-- **The file at `path` holds a database with the data `D`**, at the instances: `path` is
`d/b`, the name `b` of the directory `d` (`osPathS`, a share of the call permission of `d`'s root
(`callKey R d`: per root since wal-link L4), the whole claim on `b`, in the shared mode of the tree), and `b` names a file holding `D` or nothing with
`D = ∅` (bbolt's `nameHolds`): what bbolt's `Open_sharedNoErr.spec` takes. -/
def fileHoldsF [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] (path : GoString) (D : Data) :
    IProp GF :=
  iprop(∃ (R : Roots) (d b : GoString) (dq : DFrac) (j : Ino) (qc : Qp) (h : NamesH),
    ⌜path = child d b ∧ NameOk b ∧ PathFits path⌝ ∗ osInv ∗ osSharedInv R ∗ osPathS R d dq j ∗
    osCallPerm (callKey R d) qc ∗ osNames j (.only [b]) (DFrac.own 1) h ∗ bbolt.nameHolds h b D)

/-- **What an open database keeps of its file** (S3e; S5, 2026-11-18: the inode only), at the
instances: the inode `Open` opened (`boltIno γ i`, which `Close` needs to give the file back), and
the right to close it (`boltCloser`, S3f). The claim on the file's name is no longer here: `New`
gives it to its caller (`bPath`), so that a client may rename another file onto the name while the
database is open (the server's snapshot install). -/
def dbRestF [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] (γ : DBNames) : IProp GF :=
  iprop(∃ i : Ino, bbolt.boltIno γ i ∗ bbolt.boltCloser γ)

/-- `db` is the open database `γ` with committed data `D`: half of bbolt's `boltState` (the other
half is the backend's commit invariant's, `cmtInv`, through which a commit fires bbolt's update and a
snapshot reads the committed data without the batch lock: backend-snapshot B1, 2026-11-20; until
then all of it), and what it keeps of its file (`dbRestF`, S3e). -/
def ownDB (db : Loc) (γ : DBNames) (D : Data) : IProp GF :=
  onFs iprop(bbolt.isBolt db γ ∗ bbolt.boltState γ (1 : Qp).half D ∗ dbRestF γ)

/-- **The other half of the committed data's `boltState`** (backend-snapshot B1): what the
constructor puts in the backend's commit invariant (`cmtInv`) beside `ownDB`'s half, and what
`Close` takes back out of it. -/
def dbHalf (γ : DBNames) (D : Data) : IProp GF :=
  onFs iprop(bbolt.boltState γ (1 : Qp).half D)

instance dbHalf_timeless (γ : DBNames) (D : Data) : Timeless (dbHalf (GF := GF) γ D) := by
  unfold dbHalf onFs; split <;> infer_instance

/-- **The claim on the name `path`, which names the inode `i`** (S5), at the instances: `path` is
`d/b`, with the path of `d`, a share of the call permission, and the whole claim on `b`, whose
current entry is the file `i` (`fileHoldsF` without the file's contents). -/
def nameAtF [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] (path : GoString) (i : Ino) :
    IProp GF :=
  iprop(∃ (R : Roots) (d b : GoString) (dq : DFrac) (j : Ino) (qc : Qp) (h : NamesH),
    ⌜path = child d b ∧ NameOk b ∧ h.cur !! b = some (.file i) ∧ PathFits path⌝ ∗ osInv ∗ osSharedInv R ∗
    osPathS R d dq j ∗ osCallPerm (callKey R d) qc ∗ osNames j (.only [b]) (DFrac.own 1) h)

/-- **The file at `path` holds `D`, a file** (S5), at the instances: `fileHoldsF`'s case of a file
(the claim on the name naming the inode `i`, whose file holds a database with the data `D`). -/
def fileAtF [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] (path : GoString) (D : Data) :
    IProp GF :=
  iprop(∃ i : Ino, nameAtF path i ∗ bbolt.fileHoldsM i D)

/-- **The name `path` is free** (S5), at the instances: the whole claim on it (with the path's spine
and a share of the call permission), naming nothing. -/
def fileFreeF [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] (path : GoString) : IProp GF :=
  iprop(∃ (R : Roots) (d b : GoString) (dq : DFrac) (j : Ino) (qc : Qp) (h : NamesH),
    ⌜path = child d b ∧ NameOk b ∧ h.cur !! b = none ∧ PathFits path⌝ ∗ osInv ∗ osSharedInv R ∗
    osPathS R d dq j ∗ osCallPerm (callKey R d) qc ∗ osNames j (.only [b]) (DFrac.own 1) h)

/-- **The file at `path` holds `D`, and is a file** (S5; exclusive): what a received snapshot's file
is (`snapDirInv`'s files), what `os.Rename` moves. -/
def fileAt (path : GoString) (D : Data) : IProp GF := onFs (fileAtF path D)

/-- **The name `path` is free** (S5; exclusive): the claim on a name no file has, what `SaveDBFrom`
saves a snapshot's file under. -/
def fileFree (path : GoString) : IProp GF := onFs (fileFreeF path)

/-- **The open database `γ`'s file is at `path`, the name the caller's** (S5, 2026-11-18;
exclusive): the claim on `path`, which names `γ`'s inode. `New` gives it; the caller keeps it while
the database is open, and either joins it with what `Close` gives back (`bPath_join`: the file at
`path` again) or renames another file onto `path` (`os.Rename`), the open database keeping its
inode. Until S5 the claim was in `ownDB`. -/
def bPath (γ : DBNames) (path : GoString) : IProp GF :=
  onFs iprop(∃ i : Ino, bbolt.boltIno γ i ∗ nameAtF path i)

/-- **The closed database `γ`'s file holds `D`** (S5): its inode (`boltIno γ i`) holds a database
with the data `D` (`fileHoldsM`), named or not: what `Close` gives back. -/
def bClosed (γ : DBNames) (D : Data) : IProp GF :=
  onFs iprop(∃ i : Ino, bbolt.boltIno γ i ∗ bbolt.fileHoldsM i D)

/-- The right to begin the write transaction: nothing (bbolt's `Begin(true)` waits for its lock;
until S1 an exclusive token). -/
def wrTok (_γ : DBNames) : IProp GF := iprop(emp)
/-- `db` is the database `γ` (persistent). -/
def isDB (db : Loc) (γ : DBNames) : IProp GF := onFs (bbolt.isBolt db γ)
/-- The transaction `tx` of `γ` is live, with the view `T`, at fraction `q`. -/
def txLive (tx : Loc) (γ : DBNames) (q : Qp) (T : bbolt.TxView) : IProp GF :=
  onFs (bbolt.boltTx tx γ q T)
/-- The slice `s` holds `b` while `tx` is live (persistent). -/
def txBytes (tx : Loc) (γ : DBNames) (s : GoSlice) (b : GoString) : IProp GF :=
  onFs (bbolt.txBytes tx γ s b)
/-- The write transaction's view: begun at `D`, contents `S`, generations `G`. -/
def wView (D S : Data) (G : GoString → Nat) : bbolt.TxView :=
  { rw := true, base := D, cur := S, gen := G }
proj_simps wView
theorem wView_setBkt (D S : Data) (G : GoString → Nat) (n : GoString) (m : BktData) :
    (wView D S G).setBkt n m = wView D (S.insert n m) G := rfl
theorem wView_dropBkt (D S : Data) (G : GoString → Nat) (n : GoString) :
    (wView D S G).dropBkt n = wView D (S.delete n) (fun x => if x = n then G n + 1 else G x) := rfl
theorem wView_wr (D : Data) : bbolt.TxView.wr D = wView D D (fun _ => 0) := rfl
/-- The write transaction, begun at `D`, contents `S`, generations `G`. -/
def ownWTxG (tx : Loc) (γ : DBNames) (D S : Data) (G : GoString → Nat) : IProp GF :=
  txLive tx γ 1 (wView D S G)
/-- `b` is `tx`'s handle of the bucket `n` at generation `g` (persistent). -/
def wBkt (tx : Loc) (γ : DBNames) (b : Loc) (n : GoString) (g : Nat) : IProp GF :=
  onFs (bbolt.boltBkt tx γ b n g)
/-- A cursor of `tx`, made at the view `T`, over `es`, at `pos`. -/
def ownCur (tx : Loc) (γ : DBNames) (c : Loc) (T : bbolt.TxView) (es : List Ent)
    (pos : Option Nat) : IProp GF :=
  onFs (bbolt.boltCur tx γ c T es pos)
/-- `tx` was committed or rolled back (persistent). -/
def txDone (tx : Loc) : IProp GF := onFs (bbolt.txDone tx)
/-- `tx` is a transaction of the database `db` named `γ` (persistent). -/
def txDB (tx : Loc) (γ : DBNames) (db : Loc) : IProp GF := onFs (bbolt.txDB tx γ db)
/-- **The database file at `path` holds `D`** (S3e: until then an axiom): `fileHoldsF` at the
program's instances. What `bolt.Open` reads, and what `DB.Close` gives back. -/
def fileHolds (path : GoString) (D : Data) : IProp GF := onFs (fileHoldsF path D)

/-- (2026-11-04, R2b-3c, the user's approval) **The open database `db`, named `γ`, is the file at
`path`** (persistent): `Open_kv` gives it, `DB.Close_kv` gives the file back (`fileHolds path D`).
(S3e: until then an axiom, without `γ`.) The database's names record its path (`dbNs`); the claim
on the name is the caller's (`bPath`, S5; until then in `ownDB`'s `dbRestF`). -/
def dbFile (_db : Loc) (γ : DBNames) (path : GoString) : IProp GF := iprop(⌜γ.ns = dbNs path⌝)
@[instance] theorem dbFile_persistent (db : Loc) (γ : DBNames) (path : GoString) :
    Persistent (dbFile (GF := GF) db γ path) := by
  unfold dbFile; infer_instance
@[instance] theorem dbFile_timeless (db : Loc) (γ : DBNames) (path : GoString) :
    Timeless (dbFile (GF := GF) db γ path) := by
  unfold dbFile; infer_instance

/-- **A closed database's file, at the name the caller kept, is the file at that name** (S5):
the inodes agree (`bbolt.boltIno_agree`). -/
theorem bPath_join (γ : DBNames) (path : GoString) (D : Data) :
    bPath (GF := GF) γ path ∗ bClosed γ D ⊢ fileHolds path D := by
  rcases hfs : theFs GF with _ | ⟨S, ok, has, ne⟩
  · simp only [bPath, onFs_none hfs]
    iintro ⟨H, -⟩; iexfalso; iexact H
  · simp only [bPath, bClosed, fileHolds, onFs_some hfs]
    iintro ⟨⟨%i, #Hi, Hn⟩, ⟨%i', #Hi', Hf⟩⟩
    ihave %he := bbolt.boltIno_agree γ i i' $$ [Hi Hi']
    · iframe #
    subst he
    unfold nameAtF fileHoldsF
    icases Hn with ⟨%R, %d, %b, %dq, %j, %qc, %h, %hp, #Hinv, #Hsh, Hp, Hcp, Hnm⟩
    obtain ⟨hp, hb, hi, hf⟩ := hp
    iexists R, d, b, dq, j, qc, h
    iframe Hinv Hsh Hp Hcp Hnm
    isplitr
    · ipureintro; exact ⟨hp, hb, hf⟩
    unfold bbolt.nameHolds
    ileft
    iexists i
    iframe Hf
    ipureintro; exact hi

/-- A file at `path` holding `D` is the file `path` holds (`fileHolds`). -/
theorem fileAt_fileHolds (path : GoString) (D : Data) :
    fileAt (GF := GF) path D ⊢ fileHolds path D := by
  rcases hfs : theFs GF with _ | ⟨S, ok, has, ne⟩
  · simp only [fileAt, onFs_none hfs]
    iintro H; iexfalso; iexact H
  · simp only [fileAt, fileHolds, onFs_some hfs]
    unfold fileAtF nameAtF fileHoldsF
    iintro ⟨%i, ⟨%R, %d, %b, %dq, %j, %qc, %h, %hp, #Hinv, #Hsh, Hp, Hcp, Hnm⟩, Hf⟩
    obtain ⟨hp, hb, hi, hf⟩ := hp
    iexists R, d, b, dq, j, qc, h
    iframe Hinv Hsh Hp Hcp Hnm
    isplitr
    · ipureintro; exact ⟨hp, hb, hf⟩
    unfold bbolt.nameHolds
    ileft
    iexists i
    iframe Hf
    ipureintro; exact hi

/-! ## Laws (bbolt's API's) -/

/-- The cases of `theFs` in a law: none (every predicate `False`), or the instances. -/
local macro "fs_law" : tactic =>
  `(tactic| (rcases hfs : theFs GF with _ | ⟨S, ok, has, ne⟩ <;>
    first
    | simp only [ownDB, isDB, txLive, txBytes, ownWTxG, wBkt, ownCur, txDone, txDB,
        onFs_none hfs]
    | simp only [ownDB, isDB, txLive, txBytes, ownWTxG, wBkt, ownCur, txDone, txDB,
        onFs_some hfs]))

@[instance] theorem isDB_persistent (db : Loc) (γ : DBNames) :
    Persistent (isDB (GF := GF) db γ) := by
  fs_law <;> infer_instance
@[instance] theorem txBytes_persistent (tx : Loc) (γ : DBNames) (s : GoSlice) (b : GoString) :
    Persistent (txBytes (GF := GF) tx γ s b) := by
  fs_law <;> infer_instance
@[instance] theorem wBkt_persistent (tx : Loc) (γ : DBNames) (b : Loc) (n : GoString) (g : Nat) :
    Persistent (wBkt (GF := GF) tx γ b n g) := by
  fs_law <;> infer_instance
@[instance] theorem txDone_persistent (tx : Loc) : Persistent (txDone (GF := GF) tx) := by
  fs_law <;> infer_instance
@[instance] theorem txDB_persistent (tx : Loc) (γ : DBNames) (db : Loc) :
    Persistent (txDB (GF := GF) tx γ db) := by
  fs_law <;> infer_instance
@[instance] theorem wBkt_timeless (tx : Loc) (γ : DBNames) (b : Loc) (n : GoString) (g : Nat) :
    Timeless (wBkt (GF := GF) tx γ b n g) := by
  fs_law <;> infer_instance
@[instance] theorem ownCur_timeless (tx : Loc) (γ : DBNames) (c : Loc) (T : bbolt.TxView)
    (es : List Ent) (pos : Option Nat) : Timeless (ownCur (GF := GF) tx γ c T es pos) := by
  fs_law <;> infer_instance
@[instance] theorem txLive_fractional (tx : Loc) (γ : DBNames) (T : bbolt.TxView) :
    Fractional (fun q => txLive (GF := GF) tx γ q T) := by
  rcases hfs : theFs GF with _ | ⟨S, ok, has, ne⟩
  · simp only [txLive, onFs_none hfs]
    constructor
    intro _ _
    constructor
    · iintro %H; exact H.elim
    · iintro ⟨%H, -⟩; exact H.elim
  · simp only [txLive, onFs_some hfs]
    exact bbolt.boltTx_fractional tx γ T

/-- **A later transaction is a transaction, given its database** (bbolt's `boltTx_later`: a
transaction holds bbolt's invariants, which are not timeless; the database's give them back). -/
theorem txLive_later (db tx : Loc) (γ : DBNames) (q : Qp) (T : bbolt.TxView) :
    isDB (GF := GF) db γ ⊢ ▷ txLive tx γ q T -∗ ◇ txLive tx γ q T := by
  fs_law
  · iintro %H; exact H.elim
  · exact bbolt.boltTx_later db tx γ q T

/-- Two fractions of one transaction agree on its view. -/
theorem txLive_agree (tx : Loc) (γ : DBNames) (q1 q2 : Qp) (T1 T2 : bbolt.TxView) :
    txLive (GF := GF) tx γ q1 T1 ∗ txLive tx γ q2 T2 ⊢ ⌜T1 = T2⌝ := by
  fs_law
  · iintro ⟨%H, -⟩; exact H.elim
  · exact bbolt.boltTx_agree tx γ q1 q2 T1 T2

/-- **Each bucket of a read transaction's snapshot holds fewer than `2 ^ 61` entries** (bbolt's
`boltTx_size`: a snapshot is read from the memory map of the database file, whose size `fileHolds`
bounds; until S1 the axiom `rtxSnap_size`). -/
theorem txLive_size (tx : Loc) (γ : DBNames) (q : Qp) (D : Data) :
    txLive (GF := GF) tx γ q (bbolt.TxView.ro D) ⊢
      ⌜∀ (n : GoString) (m : BktData), D.lookup n = some m → m.size < 2 ^ 61⌝ := by
  fs_law
  · iintro %H; exact H.elim
  · exact bbolt.boltTx_size tx γ q D

/-- A transaction's slice is read while the transaction is live. -/
theorem txBytes_acc (tx : Loc) (γ : DBNames) (s : GoSlice) (b : GoString) (q : Qp)
    (T : bbolt.TxView) :
    txBytes (GF := GF) tx γ s b ∗ txLive tx γ q T ⊢
      ∃ dq : DFrac, s ↦*{dq} b ∗ (s ↦*{dq} b -∗ txLive tx γ q T) := by
  fs_law
  · iintro ⟨%H, -⟩; exact H.elim
  · exact bbolt.txBytes_acc tx γ q T s b

/-- A live transaction is a non-nil `*Tx` (`DB.Begin` returns one with a nil error; the
backend's `t.tx != nil` and `readTx.tx != nil` checks rely on it). -/
theorem txLive_nonnull (tx : Loc) (γ : DBNames) (q : Qp) (T : bbolt.TxView) :
    txLive (GF := GF) tx γ q T ⊢ ⌜tx ≠ Loc.null⌝ := by
  fs_law
  · iintro %H; exact H.elim
  · exact bbolt.boltTx_nonnull tx γ q T

/-- The write transaction owns its bucket handles' `FillPercent` field (of every handle it gave
out, current or not), written back with any value but a NaN (bbolt's `boltTx_fill`; until S1 an
axiom taking any value, which `examples/axiomcx/bboltnan` refuted). -/
theorem ownWTxG_fill (tx b : Loc) (γ : DBNames) (D S : Data) (G : GoString → Nat) (n : GoString)
    (g : Nat) :
    ownWTxG (GF := GF) tx γ D S G ∗ wBkt tx γ b n g ⊢
      ∃ f : w64, structFieldRef go_etcd_io.bbolt.Bucket go!"FillPercent" b ↦ f ∗
        (∀ f' : w64, ⌜¬ bbolt.float64IsNaN f'⌝ -∗
          structFieldRef go_etcd_io.bbolt.Bucket go!"FillPercent" b ↦ f' -∗
          ownWTxG tx γ D S G) := by
  fs_law
  · iintro ⟨%H, -⟩; exact H.elim
  · exact bbolt.boltTx_fill tx b γ _ n g rfl

/-- The write transaction, its buckets at some generations: what `Begin` gives and `Commit`
takes, and what the backend holds between operations. -/
abbrev ownWTx (tx : Loc) (γ : DBNames) (D S : Data) : IProp GF :=
  ∃ G : GoString → Nat, ownWTxG tx γ D S G

/-- The write transaction is live (at its view). -/
theorem ownWTx_live (tx : Loc) (γ : DBNames) (D S : Data) :
    ownWTx (GF := GF) tx γ D S ⊢
      ∃ T, txLive tx γ 1 T ∗ (txLive tx γ 1 T -∗ ownWTx tx γ D S) := by
  unfold ownWTx ownWTxG
  iintro ⟨%G, H⟩
  iexists (wView D S G)
  isplitl [H]
  · iexact H
  iintro H
  iexists G
  iexact H

/-- What a cursor move to the `i`-th entry returns: its key (never nil: bbolt's keys are not
empty) and value, valid while `tx` is live; nil and nil past the end. -/
def curAt (tx : Loc) (γ : DBNames) (es : List Ent) (i : Nat) (k v : GoSlice) : IProp GF :=
  match es[i]? with
  | some e => iprop(⌜k ≠ slice.nil⌝ ∗ txBytes tx γ k e.1 ∗ txBytes tx γ v e.2)
  | none => iprop(⌜k = slice.nil ∧ v = slice.nil⌝)

instance curAt_persistent (tx : Loc) (γ : DBNames) (es : List Ent) (i : Nat) (k v : GoSlice) :
    Persistent (curAt (GF := GF) tx γ es i k v) := by
  unfold curAt; split <;> infer_instance

/-- The backend's `curAt` is bbolt's, at the instances. -/
theorem curAt_eq [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
 [FsNoErrAll] (tx : Loc) (γ : DBNames)
    (es : List Ent) (i : Nat) (k v : GoSlice) :
    curAt (GF := GF) tx γ es i k v = bbolt.curAt tx γ es i k v := by
  unfold curAt bbolt.curAt txBytes
  simp only [onFs_eq]
  rfl

/-- An unfired read update over the whole committed data, fired by the caller itself: the data
back (what `Begin(false)`'s error case gives back of `boltState_read_au`). -/
theorem boltState_au_back [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] (γ : DBNames)
    (D : Data) :
    (AU <{ ∃∃ (q : Qp) (D' : bbolt.Data), bbolt.boltState (GF := GF) γ q D' }> @ ⊤ \ ↑γ.ns, ∅
        <{ bbolt.boltState γ q D', COMM bbolt.boltState γ 1 D ∗ ⌜D' = D⌝ }>) ⊢
    |={⊤}=> bbolt.boltState γ 1 D := by
  iintro Hau
  ihave Hau := atomic_update_mask_weaken (Eo2 := ⊤) (fun _ _ => CoPset.mem_full) $$ Hau
  ihave Hacc := aupd_aacc $$ Hau
  unfold atomic_acc
  imod Hacc with Hacc
  isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hacc
  icases Hacc with ⟨%q, %D', Hx, Hucl⟩
  icases Hucl with ⟨-, Hcommit⟩
  isimp only [tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at Hcommit
  imod Hcommit $$ Hx with ⟨Hs, -⟩
  imodintro
  iexact Hs

/-- The whole committed data's `boltState` as two halves, both ways (backend-snapshot B1: `ownDB`'s and
the commit invariant's). -/
theorem boltState_halves [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] (γ : DBNames) (D : Data) :
    bbolt.boltState (GF := GF) γ 1 D ⊣⊢
      bbolt.boltState γ (1 : Qp).half D ∗ bbolt.boltState γ (1 : Qp).half D := by
  conv => lhs; rw [← Qp.half_add_half 1]
  exact (bbolt.boltState_fractional γ D).fractional _ _

/-- **A read update from a share `q` of the committed data** (backend-snapshot B1: the batch lock
holds half of `boltState`): bbolt's `boltState_read_au` at any share, the share back at the commit. -/
theorem boltState_read_au_q [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] (γ : DBNames) (q : Qp)
    (D : Data) :
    bbolt.boltState (GF := GF) γ q D ⊢
      AU <{ ∃∃ (q' : Qp) (D' : bbolt.Data), bbolt.boltState γ q' D' }> @ ⊤ \ ↑γ.ns, ∅
        <{ bbolt.boltState γ q' D', COMM bbolt.boltState γ q D ∗ ⌜D' = D⌝ }> := by
  iintro H
  iauintro
  unfold atomic_acc
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hcl
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists q, D
  iframe H
  isplit
  · iintro H; imod Hcl with -; imodintro; iexact H
  · iintro H; imod Hcl with -; imodintro; iframe H; ipureintro; rfl

/-- `boltState_au_back` at a share `q` (`boltState_read_au_q`'s update, unfired). -/
theorem boltState_au_back_q [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] (γ : DBNames) (q : Qp)
    (D : Data) :
    (AU <{ ∃∃ (q' : Qp) (D' : bbolt.Data), bbolt.boltState (GF := GF) γ q' D' }> @ ⊤ \ ↑γ.ns, ∅
        <{ bbolt.boltState γ q' D', COMM bbolt.boltState γ q D ∗ ⌜D' = D⌝ }>) ⊢
    |={⊤}=> bbolt.boltState γ q D := by
  iintro Hau
  ihave Hau := atomic_update_mask_weaken (Eo2 := ⊤) (fun _ _ => CoPset.mem_full) $$ Hau
  ihave Hacc := aupd_aacc $$ Hau
  unfold atomic_acc
  imod Hacc with Hacc
  isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hacc
  icases Hacc with ⟨%q', %D', Hx, Hucl⟩
  icases Hucl with ⟨-, Hcommit⟩
  isimp only [tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at Hcommit
  imod Hcommit $$ Hx with ⟨Hs, -⟩
  imodintro
  iexact Hs

end preds

end backend
end EtcdGrove
end Perennial
