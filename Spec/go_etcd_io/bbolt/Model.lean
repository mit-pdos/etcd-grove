/-
# bbolt's pure model (batch 4c)

What bbolt's specs are written over (`Api.lean` holds the resources and laws). Transparent: the
model is the meaning of the specs.

* **The data** (`Ent`, `Data`): a database is its root bucket; a bucket holds a sequence counter
  (`NextSequence`) and entries sorted by key (`bytes.Compare`, `go.GoStringLt`), each a plain value
  or a nested bucket. The root's entries are the top-level buckets (no `Tx` method puts a plain value
  there). A bucket is named by its **path** from the root (`BPath`). Every operation of the model
  keeps the entries sorted with distinct keys (`insEnt`, `delEnt`), so a database reached from
  `Data.empty` or from a file (`Api.lean`'s `fileHolds`) is sorted.
* **A transaction's view** (`TxView`): read or write, managed (`View`/`Update`) or not, the
  committed data it began at (`base`), its data now (`cur`), the per-path **generation** that
  `DeleteBucket` bumps (a deleted bucket's handles are never current again,
  `nonissues/bbolt-deleted-bucket-handle.md`), and the database's `NoSync` mode.
* **The client-owned state** (`BoltSt`): the committed data and **what a crash may recover**
  (`dur`), with the two flags the durability argument needs (`busy`, `lost`); the transitions of a
  commit, a failed commit attempt and a sync (`BoltSt.commit`, `attempt`, `settle`, `sync`).
* The size bounds (`maxKeySize`, `bboltEntryMax`) and the options (`OptsM`).
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Golang.Defn.String

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Bbolt

/-! ## Data -/

/-- **A bucket entry**: a plain value, or a nested bucket with its sequence counter and its entries
(sorted by key, keys distinct). A database is its root bucket (`Data`). -/
inductive Ent where
  | val (v : GoString)
  | bkt (seq : w64) (ents : List (GoString × Ent))
  deriving Inhabited

/-- A database's data: its root bucket (whose entries are the top-level buckets). -/
abbrev Data := Ent

/-- A bucket's path from the root: the names of the buckets that lead to it (`[]`: the root). -/
abbrev BPath := List GoString

/-- The empty database (a fresh file: `Open`'s `init`). -/
def Data.empty : Data := .bkt (W64 0) []

namespace Ent

/-- A bucket's entries (none for a value). -/
def ents : Ent → List (GoString × Ent)
  | .val _ => []
  | .bkt _ es => es

/-- A bucket's sequence counter (`Bucket.Sequence`; `0` for a value). -/
def seq : Ent → w64
  | .val _ => W64 0
  | .bkt s _ => s

/-- Whether the entry is a bucket. -/
def isBkt : Ent → Bool
  | .val _ => false
  | .bkt _ _ => true

/-- The entry at key `k` of a bucket. -/
def lookup (e : Ent) (k : GoString) : Option Ent :=
  (e.ents.find? (fun x => decide (x.1 = k))).map Prod.snd

/-- The entry at path `p` (`[]`: `e` itself). -/
def atPath : Ent → BPath → Option Ent
  | e, [] => some e
  | e, k :: p => (e.lookup k).bind (fun c => c.atPath p)

/-- The bucket at path `p` exists. -/
def bktAt (e : Ent) (p : BPath) : Prop :=
  ∃ s es, e.atPath p = some (.bkt s es)

/-- Insert or replace `k ↦ x` in a sorted entry list (sorted by `go.GoStringLt`). -/
def insEnt (k : GoString) (x : Ent) : List (GoString × Ent) → List (GoString × Ent)
  | [] => [(k, x)]
  | (k', y) :: es =>
    if k' = k then (k, x) :: es
    else if go.GoStringLt k k' then (k, x) :: (k', y) :: es
    else (k', y) :: insEnt k x es

/-- Remove key `k` from an entry list. -/
def delEnt (k : GoString) (es : List (GoString × Ent)) : List (GoString × Ent) :=
  es.filter (fun x => decide (x.1 ≠ k))

/-- A bucket with key `k` set to `x` (`some`) or removed (`none`); a value is unchanged. -/
def setKey : Ent → GoString → Option Ent → Ent
  | .val v, _, _ => .val v
  | .bkt s es, k, some x => .bkt s (insEnt k x es)
  | .bkt s es, k, none => .bkt s (delEnt k es)

/-- A bucket with its sequence counter set to `n`; a value is unchanged. -/
def setSeq : Ent → w64 → Ent
  | .val v, _ => .val v
  | .bkt _ es, n => .bkt n es

/-- `e` with the entry at path `p` replaced by `f` of it (unchanged if there is none). -/
def modAt : Ent → BPath → (Ent → Ent) → Ent
  | e, [], f => f e
  | e, k :: p, f =>
    match e.lookup k with
    | some c => e.setKey k (some (c.modAt p f))
    | none => e

/-- A bucket's entries as a cursor (and `ForEach`) returns them, in key order: a value's bytes,
or `none` for a nested bucket (Go returns a nil value for a bucket's key). -/
def curEnts (e : Ent) : List (GoString × Option GoString) :=
  e.ents.map (fun x => (x.1, match x.2 with
    | .val v => some v
    | .bkt _ _ => none))

end Ent

/-- A cursor entry: a key and its value (`none`: a nested bucket). -/
abbrev CurEnt := GoString × Option GoString

/-- The first index of a sorted entry list whose key is not below `k` (`Cursor.Seek`). -/
def seekIdx (es : List CurEnt) (k : GoString) : Nat :=
  (es.takeWhile (fun e => decide (go.GoStringLt e.1 k))).length

/-- The path of the bucket `k` inside the bucket at `p`. -/
abbrev BPath.child (p : BPath) (k : GoString) : BPath := p ++ [k]

/-! ## Size bounds -/

/-- bbolt's `MaxKeySize` (`bucket.go`): `Put` returns `ErrKeyTooLarge` above it. -/
@[word_unfold] def maxKeySize : Nat := 32768

/-- bbolt's `MaxValueSize` (`bucket.go`), for reference: `Put` returns `ErrValueTooLarge` above it,
but accepts sizes it cannot store (`issues/bbolt-max-value-size-unusable.md`). -/
@[word_unfold] def maxValueSize : Nat := 2 ^ 31 - 2

/-- **The largest entry (key plus value, in bytes) bbolt stores and reads back** (the old spec's
bound, unchanged): one leaf page may hold up to four entries whatever their size, and a page's
buffer must stay below `MaxAllocSize = 2^31 - 1`, or `Commit` (`WriteInodeToPage`) or a later read
panics (`issues/bbolt-max-value-size-unusable.md`, `issues/bbolt-large-values-leaf-unreadable.md`).
Rests on the split threshold being at most the page size (`splitThreshold`'s trusted model, D17). -/
@[word_unfold] def bboltEntryMax : Nat := 2 ^ 28

/-- `f`, a `float64`'s bits, is a NaN: exponent all ones, mantissa non-zero. -/
def float64IsNaN (f : w64) : Prop :=
  (f.toNat / 2 ^ 52) % 2 ^ 11 = 2 ^ 11 - 1 ∧ f.toNat % 2 ^ 52 ≠ 0

/-! ## A transaction's view -/

/-- **A transaction's view** (see the header).
- `rw`: a write transaction (`Begin(true)`); `managed`: run by `View`/`Update` (its `Commit` and
  `Rollback` panic);
- `base`: the committed data when it began (its snapshot, for a read transaction);
- `cur`: its data now (`base` throughout a read transaction);
- `gen p`: the generation of the bucket path `p`, bumped by `DeleteBucket` of `p`; `0` throughout
  a read transaction;
- `noSync`: the database's `NoSync` option (`isBolt`'s mode), which `Commit` follows.
Written with named fields. -/
structure TxView where
  rw : Bool
  managed : Bool
  base : Data
  cur : Data
  gen : BPath → Nat
  noSync : Bool

/-- A read transaction's view: the snapshot `D` (on a database of mode `ns`). -/
def TxView.ro (D : Data) (managed : Bool) (ns : Bool) : TxView :=
  { rw := false, managed := managed, base := D, cur := D, gen := fun _ => 0, noSync := ns }

/-- A write transaction's view when it begins at the committed `D`, on a database of mode `ns`. -/
def TxView.wr (D : Data) (managed : Bool) (ns : Bool) : TxView :=
  { rw := true, managed := managed, base := D, cur := D, gen := fun _ => 0, noSync := ns }

/-- The generations of `p` and of each of its ancestors, root first: a bucket handle is current
while these are what they were when the handle was made. -/
def TxView.gens (T : TxView) (p : BPath) : List Nat :=
  (List.range (p.length + 1)).map (fun i => T.gen (p.take i))

/-- The entries of the bucket at `p` in cursor order (`[]` if there is none). -/
def TxView.ents (T : TxView) (p : BPath) : List CurEnt :=
  match T.cur.atPath p with
  | some e => e.curEnts
  | none => []

/-- The view with its data changed to `D`. -/
def TxView.setCur (T : TxView) (D : Data) : TxView := { T with cur := D }

/-- The view with the bucket `p.child k` deleted (with everything in it) and its generation
bumped. -/
def TxView.dropBkt (T : TxView) (p : BPath) (k : GoString) : TxView :=
  { T with cur := T.cur.modAt p (fun b => b.setKey k none),
           gen := fun x => if x = p.child k then T.gen x + 1 else T.gen x }

/-! ## The client-owned state: committed data and durability -/

/-- **The database's state as its client owns it** (`Api.lean`'s `boltState`).
- `data`: the committed data: what a transaction beginning now reads;
- `dur`: **what a crash may recover besides `data`**: `some ds`, `data` or one of `ds` (each a state
  committed earlier, or attempted); `none`, no promise (a `NoSync` commit not yet synced: the file a
  crash leaves may not be a database);
- `busy`: a commit's meta page write may be in flight (from the commit's update to the end of its
  `Commit`): a sync then cannot promise the meta page reached the disk;
- `lost`: an `fdatasync` of the file failed since it was opened in this generation (Linux may then
  have dropped dirty pages without writing them, so a later successful sync no longer makes every
  page durable: `notes/osfs-ext-plan.md`, D2). -/
structure BoltSt where
  data : Data
  dur : Option (List Data)
  busy : Bool
  lost : Bool

/-- The state of a file just opened by a generation (or a fresh file): `D`, all of it durable. -/
def BoltSt.init (D : Data) : BoltSt := { data := D, dur := some [], busy := false, lost := false }

/-- **A crash may leave the database holding `D`.** -/
def BoltSt.recovers (σ : BoltSt) (D : Data) : Prop :=
  ∃ ds, σ.dur = some ds ∧ (D = σ.data ∨ D ∈ ds)

/-- **A commit of `D` takes effect** (its meta page write, which will succeed, begins): `D` is
committed, the old data stays recoverable until a sync, and under `NoSync` nothing is promised
(the commit's pages are not synced before its meta page). -/
def BoltSt.commit (σ : BoltSt) (D : Data) (noSync : Bool) : BoltSt :=
  { σ with data := D, busy := true,
           dur := if noSync then none else σ.dur.map (fun ds => ds ++ [σ.data]) }

/-- **A commit of `D` is attempted and fails** (its meta page write, which will fail, begins): the
committed data stays, but a crash during the write may still find `D` (a page write in flight may
reach the disk), so `D` becomes recoverable (under `NoSync`, nothing is promised). -/
def BoltSt.attempt (σ : BoltSt) (D : Data) (noSync : Bool) : BoltSt :=
  { σ with busy := true, dur := if noSync then none else σ.dur.map (fun ds => ds ++ [D]) }

/-- **A sync of the file ends** (`ok`: the `fdatasync` succeeded): if it succeeded with no meta
page write in flight and no earlier failure, only the committed data is recoverable. -/
def BoltSt.sync (σ : BoltSt) (ok : Bool) : BoltSt :=
  if ok then (if σ.busy || σ.lost then σ else { σ with dur := some [] })
  else { σ with lost := true }

/-- **A commit ends** (after its updates): no meta page write in flight any more; `synced`: it
ended with a successful `fdatasync` of its meta page (`NoSync` off), which makes the committed data
the only recoverable state unless a sync failed earlier; `failed`: an `fdatasync` failed. -/
def BoltSt.settle (σ : BoltSt) (synced failed : Bool) : BoltSt :=
  { σ with busy := false,
           lost := σ.lost || failed,
           dur := if synced && !σ.lost then some [] else σ.dur }

/-! ## Options -/

section opts
variable [GooseExts] [GoGlobalContext]

/-- The part of a bbolt `Options` value `Open`'s behaviour depends on (`Options` is an axiomatized
type: a translator gap, `Code/go_etcd_io/bbolt.toml`). -/
structure OptsM where
  readOnly : Bool
  pageSize : w64
  /-- `OpenFile` (`nil`: `os.OpenFile`) -/
  openFile : GoFunc
  logger : GoInterface
  mlock : Bool
  mmapFlags : w64
  noSync : Bool

/-- `Open(path, mode, nil)`'s options (`DefaultOptions`: no timeout, grow sync, the array
freelist; every field the model reads at its zero). -/
def OptsM.dflt : OptsM :=
  { readOnly := false, pageSize := W64 0, openFile := func.nil, logger := GoInterface.nil,
    mlock := false, mmapFlags := W64 0, noSync := false }

/-- `syscall.MAP_POPULATE` (Linux). -/
@[word_unfold] def mapPopulate : Nat := 0x8000

/-- The logger is nil or of a pointer type: `(*Options).String` formats it with `%p` (a scope
restriction of the model, as before: the backend's `*zapBoltLogger` and nil meet it). -/
def loggerPtrOk : GoInterface → Prop
  | .nil => True
  | .ok li => ∃ (t : go.GoType) (l : Loc), li.ty = go.GoType.PointerType t ∧ li.v = #l

/-- **Options `Open` accepts here**: read-write; the default page size
(`nonissues/bbolt-large-page-size.md`); `Mlock` off and `MmapFlags` `0` or `MAP_POPULATE` (the
system calls OsFs models: scope restrictions of the model, not of Go); a pointer-typed logger.
`OpenFile` may be custom (etcd's defrag), with the contract `Api.lean`'s `openFileOk`. `NoSync`
is a mode of the specs (`TxView.noSync`, `BoltSt.commit`); the other fields change no outcome the
specs state (`NoGrowSync` only what an un-synced `grow` leaves, which the next commit's sync
covers; `InitialMmapSize` at worst an `mmap` error; `Timeout` a `flock` that loops or fails;
`NoFreelistSync` and `FreelistType` only the freelist's representation, batch 4d's). -/
def OptsM.ok (o : OptsM) : Prop :=
  o.readOnly = false ∧ o.pageSize = W64 0 ∧ o.mlock = false ∧
    (o.mmapFlags.toNat = 0 ∨ o.mmapFlags.toNat = mapPopulate) ∧ loggerPtrOk o.logger

end opts

end Bbolt
end EtcdGrove
end Perennial
