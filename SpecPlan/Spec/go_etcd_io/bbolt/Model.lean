/-
# bbolt's pure model (batch 4c)

What bbolt's specs are written over (`Api.lean` holds the resources and laws). Transparent: the
model is the meaning of the specs.

* **The data** (`Ent`, `Data`): a database is its root bucket; a bucket holds a sequence counter
  (`NextSequence`) and entries sorted by key (`bytes.Compare`, `go.GoStringLt`), each a plain value
  or a nested bucket. The root's entries are the top-level buckets: no `Tx` method puts a plain
  value there, but the root's handle (`Tx.Cursor`, then `Cursor.Bucket`) can (`Bucket.Put` at
  `[]`); etcd puts none. A bucket is named by its **path** from the root (`BPath`). Every operation of the model
  keeps the entries sorted with distinct keys (`insEnt`, `delEnt`), so a database reached from
  `Data.empty` or from a file (`Api.lean`'s `fileHolds`) is sorted.
* **A transaction's view** (`TxView`): read or write, managed (`View`/`Update`) or not, the
  committed data it began at (`base`), its data now (`cur`), and the database's `NoSync` mode.
  Which bucket handles are current is not in the view: a write transaction's handles are owned
  (`Api.lean`'s `bktOwn`), a read transaction's never go stale.
* **The client-owned state** (`BoltSt`): the committed data and **what a crash may recover**
  (`dur`), with the two flags the durability argument needs (`busy`, `lost`); the transitions of a
  commit, a failed commit attempt and a sync (`BoltSt.commit`, `attempt`, `settle`, `sync`).
* The size bounds (`maxKeySize`, `bboltEntryMax`) and the options (`OptsM`).
* **Laws** over the data model (`Ent.atPath_modAt.spec`, ..., at the end): pure obligations the
  clients use (lookup after a put or a delete, the cursor order after a put, well-formedness kept).

**Changes (2026-11-12, `notes/specs-only/ledger.md`).** `TxView.gen`/`gens` removed (a generation
counter in the view was unobservable state, redundant with the ownership of a write transaction's
bucket handles, `Api.lean`'s `bktOwn`): `dropBkt` only changes the data. Added: the bucket paths
(`Ent.bktPaths`, `Ent.bktsUnder`, `TxView.bktNames`), `Ent.curVal`, and the model's laws.
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

/-- An entry's value as a cursor returns it: a value's bytes, `none` for a nested bucket. -/
def curVal : Ent → Option GoString
  | .val v => some v
  | .bkt _ _ => none

/-- A bucket's entries as a cursor (and `ForEach`) returns them, in key order: a value's bytes,
or `none` for a nested bucket (Go returns a nil value for a bucket's key). -/
def curEnts (e : Ent) : List (GoString × Option GoString) :=
  e.ents.map (fun x => (x.1, x.2.curVal))

mutual
/-- **The paths of the nested buckets** of `e`, at any depth, relative to `e` (not `[]`: `e`
itself), in key order, parents first. -/
def bktPaths : Ent → List BPath
  | .val _ => []
  | .bkt _ es => entsBktPaths es

/-- The nested bucket paths of an entry list (`bktPaths`' helper). -/
def entsBktPaths : List (GoString × Ent) → List BPath
  | [] => []
  | (k, c) :: es =>
    (if c.isBkt then [k] :: (bktPaths c).map (k :: ·) else []) ++ entsBktPaths es
end

/-- **The bucket at `q` and every bucket below it** (`[]` if there is no bucket at `q`): the
handles `DeleteBucket` of `q` invalidates. -/
def bktsUnder (e : Ent) (q : BPath) : List BPath :=
  match e.atPath q with
  | some c => if c.isBkt then q :: (bktPaths c).map (q ++ ·) else []
  | none => []

end Ent

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

namespace Ent

/-- **A well-formed entry**: every bucket's keys non-empty, **at most `maxKeySize`** and strictly
sorted (`go.GoStringLt`, `bytes.Compare`), and **each plain value's key and value together at most
`bboltEntryMax`**, recursively. Every state bbolt holds is well-formed (`Api.lean`'s `boltTx_wf`,
for a transaction's views and the committed data, and `boltImage_wf`): `Put` refuses a longer key
and takes the entry bound as a premise, `CreateBucket*` take the name bound, and a file bbolt opens
holds only such entries (`fileHolds`). The bounds are what a copy needs to meet `Put`'s and
`CreateBucketIfNotExists`' premises with data it read (etcd's defrag; verify-round A11 F6). -/
inductive wf : Ent → Prop
  | val (v : GoString) : wf (.val v)
  | bkt (s : w64) (es : List (GoString × Ent)) :
      es.Pairwise (fun a b => go.GoStringLt a.1 b.1) → (∀ x ∈ es, x.1 ≠ []) →
      (∀ x ∈ es, x.1.length ≤ maxKeySize) →
      (∀ k v, (k, Ent.val v) ∈ es → k.length + v.length ≤ bboltEntryMax) →
      (∀ x ∈ es, wf x.2) → wf (.bkt s es)

end Ent

/-- A cursor entry: a key and its value (`none`: a nested bucket). -/
abbrev CurEnt := GoString × Option GoString

/-- The first index of a sorted entry list whose key is not below `k` (`Cursor.Seek`). -/
def seekIdx (es : List CurEnt) (k : GoString) : Nat :=
  (es.takeWhile (fun e => decide (go.GoStringLt e.1 k))).length

/-- The path of the bucket `k` inside the bucket at `p`. -/
abbrev BPath.child (p : BPath) (k : GoString) : BPath := p ++ [k]

/-- `f`, a `float64`'s bits, is a NaN: exponent all ones, mantissa non-zero. -/
def float64IsNaN (f : w64) : Prop :=
  (f.toNat / 2 ^ 52) % 2 ^ 11 = 2 ^ 11 - 1 ∧ f.toNat % 2 ^ 52 ≠ 0

/-! ## A transaction's view -/

/-- **A transaction's view** (see the header).
- `rw`: a write transaction (`Begin(true)`); `managed`: run by `View`/`Update` (its `Commit` and
  `Rollback` panic);
- `base`: the committed data when it began (its snapshot, for a read transaction);
- `cur`: its data now (`base` throughout a read transaction);
- `noSync`: the database's `NoSync` option (`isBolt`'s mode), which `Commit` follows.
Written with named fields. -/
structure TxView where
  rw : Bool
  managed : Bool
  base : Data
  cur : Data
  noSync : Bool

/-- A read transaction's view: the snapshot `D` (on a database of mode `ns`). -/
def TxView.ro (D : Data) (managed : Bool) (ns : Bool) : TxView :=
  { rw := false, managed := managed, base := D, cur := D, noSync := ns }

/-- A write transaction's view when it begins at the committed `D`, on a database of mode `ns`. -/
def TxView.wr (D : Data) (managed : Bool) (ns : Bool) : TxView :=
  { rw := true, managed := managed, base := D, cur := D, noSync := ns }

/-- The entries of the bucket at `p` in cursor order (`[]` if there is none). -/
def TxView.ents (T : TxView) (p : BPath) : List CurEnt :=
  match T.cur.atPath p with
  | some e => e.curEnts
  | none => []

/-- The names of the nested buckets of the bucket at `p`, in key order (`ForEachBucket`'s). -/
def TxView.bktNames (T : TxView) (p : BPath) : List GoString :=
  ((T.ents p).filter (fun e => e.2.isNone)).map Prod.fst

/-- The view with its data changed to `D`. -/
def TxView.setCur (T : TxView) (D : Data) : TxView := { T with cur := D }

/-- The view with the bucket `p.child k` deleted, with everything in it (`DeleteBucket`; its
handles' tokens are consumed, `Api.lean`'s `bktOwn`). -/
def TxView.dropBkt (T : TxView) (p : BPath) (k : GoString) : TxView :=
  { T with cur := T.cur.modAt p (fun b => b.setKey k none) }

/-! ## The client-owned state: committed data and durability -/

/-- **The database's state as its client owns it** (`Api.lean`'s `boltState`).
- `data`: the committed data: what a transaction beginning now reads;
- `dur`: **what a crash may recover besides `data`**: `some ds`, `data` or one of `ds` (each a state
  committed earlier, or attempted); `none`, no promise (a `NoSync` commit not yet synced, or a
  commit after a failed sync: the file a crash leaves may not be a database);
- `busy`: a commit's meta page write may be in flight (from the commit's update to the end of its
  `Commit`): a sync then cannot promise the meta page reached the disk;
- `lost`: an `fdatasync` of the file failed since it was opened in this generation (Linux marks the
  dirty pages clean without writing them, so no later sync writes them unless they are rewritten:
  `notes/osfs-ext-plan.md`, D2). Once `lost`, no commit makes a promise
  (`nonissues/bbolt-commit-after-failed-sync.md`);
- `broken`: a commit failed after the database lost its mapping (a failed remap in `allocate`):
  every later `Begin` fails (`ErrInvalidMapping`). A client whose commits all succeeded knows it is
  `false`;
- `named`: the file's name is durable in its directory. bbolt creates a missing file
  (`O_CREATE`) and never syncs its directory (`nonissues/bbolt-create-dir-not-synced.md`; OsFs's
  D4: a created file's name is not durable), so a generation that starts from no file (or from an
  empty file whose name may not be durable: `boltFresh_alloc`, `BoltSt.fresh`) has `named = false`
  for its whole life, and a crash may then also find no file at all, which the next generation
  starts from again (verify-round A11 F1, a user decision: `notes/specs-only/verify/repair-bbolt.md`,
  "New decisions"). A generation that opens an existing file whose name is durable (`fileHolds`:
  one that survived a crash, a snapshot synced with its name, an empty file its creator made
  durable) has `named = true`. -/
structure BoltSt where
  data : Data
  dur : Option (List Data)
  busy : Bool
  lost : Bool
  broken : Bool
  named : Bool

/-- The state of an existing file a generation opens (`fileHolds`): `D`, all of it durable, its
name too. -/
def BoltSt.init (D : Data) : BoltSt :=
  { data := D, dur := some [], busy := false, lost := false, broken := false, named := true }

/-- The state of a database bbolt will create (no file, or an empty one whose name may not be
durable: `boltFresh_alloc`): empty, and the file may vanish at a crash. -/
def BoltSt.fresh : BoltSt := { BoltSt.init Data.empty with named := false }

/-- **A crash may leave the database holding `D`**: (with a promise, `dur ≠ none`) the committed
data, one of `dur`'s, or, while the file's name is not durable, the empty database (no file). -/
def BoltSt.recovers (σ : BoltSt) (D : Data) : Prop :=
  ∃ ds, σ.dur = some ds ∧ (D = σ.data ∨ D ∈ ds ∨ (σ.named = false ∧ D = Data.empty))

/-- **A commit of `D` takes effect** (its meta page is written): `D` is committed, the old data
stays recoverable until a sync; under `NoSync`, or after a failed sync (`lost`: pages this commit's
tree reaches may have been dropped), nothing is promised. -/
def BoltSt.commit (σ : BoltSt) (D : Data) (noSync : Bool) : BoltSt :=
  { σ with data := D, busy := true,
           dur := if noSync || σ.lost then none else σ.dur.map (fun ds => ds ++ [σ.data]) }

/-- **A commit of `D` is attempted and fails** (before or at its meta page write): the committed
data stays, but a crash during the write may still find `D` (a page write in flight may reach the
disk), so `D` becomes recoverable (under `NoSync` or once `lost`, nothing is promised). -/
def BoltSt.attempt (σ : BoltSt) (D : Data) (noSync : Bool) : BoltSt :=
  { σ with busy := true,
           dur := if noSync || σ.lost then none else σ.dur.map (fun ds => ds ++ [D]) }

/-- **A sync of the file ends** (`ok`: the `fdatasync` succeeded): if it succeeded with no meta
page write in flight and no earlier failure, only the committed data is recoverable. -/
def BoltSt.sync (σ : BoltSt) (ok : Bool) : BoltSt :=
  if ok then (if σ.busy || σ.lost then σ else { σ with dur := some [] })
  else { σ with lost := true }

/-- **A commit ends** (after its commit update): no meta page write in flight any more; `synced`:
it ended with a successful `fdatasync` of its meta page (`NoSync` off), which makes the committed
data the only recoverable state unless a sync failed earlier; `failed`: an `fsync`/`fdatasync`
failed (the meta's, `grow`'s, the data pages'), or the meta write reported an error after writing
the page; `brk`: the commit failed with the mapping lost. -/
def BoltSt.settle (σ : BoltSt) (synced failed brk : Bool) : BoltSt :=
  { σ with busy := false,
           lost := σ.lost || failed,
           broken := σ.broken || brk,
           dur := if synced && !σ.lost && !failed then some [] else σ.dur }

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
  /-- `NoFreelistSync` (re-review N1: with it off, `Open` commits once to write a freelist page
  into a file that has none, `db.go:338-350` at `ea4cab5`, a commit the client's state must record) -/
  noFreelistSync : Bool

/-- `Open(path, mode, nil)`'s options (`DefaultOptions`: no timeout, grow sync, the array
freelist; every field the model reads at its zero). -/
def OptsM.dflt : OptsM :=
  { readOnly := false, pageSize := W64 0, openFile := func.nil, logger := GoInterface.nil,
    mlock := false, mmapFlags := W64 0, noSync := false, noFreelistSync := false }

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
`FreelistType` only the freelist's representation, batch 4d's). `NoFreelistSync` is tracked: off,
`Open` may commit (`Open.spec`'s freelist update). -/
def OptsM.ok (o : OptsM) : Prop :=
  o.readOnly = false ∧ o.pageSize = W64 0 ∧ o.mlock = false ∧
    (o.mmapFlags.toNat = 0 ∨ o.mmapFlags.toNat = mapPopulate) ∧ loggerPtrOk o.logger

end opts

/-! ## Laws of the data model (2026-11-12, `notes/specs-only/ledger.md`)

Pure obligations over the transparent model, which the clients use instead of re-deriving them
(the backend's range after a put, its compaction's deletes). Each is true of the definitions;
the comments say why, for the edge cases. -/

namespace Ent

/-- **`atPath` after `modAt` at the same path and below it**: the entry at `p` is `f` of the old
one, and the entries below are `f`'s (`r = []`: the same path). If there is no entry at `p`
(a missing key, or a value on the way), `modAt` changes nothing and both sides are `none`. -/
def atPath_modAt.spec : Prop :=
  ∀ (e : Ent) (p r : BPath) (f : Ent → Ent),
    (e.modAt p f).atPath (p ++ r) = ((e.atPath p).map f).bind (fun c => c.atPath r)

/-- **`atPath` after `modAt` at another path**: unchanged when neither path is a prefix of the
other (`modAt` replaces only the first entry of each key on its way, so another key's first
entry, which `lookup` finds, stays). An ancestor of `p` is changed (its subtree is). -/
def atPath_modAt_other.spec : Prop :=
  ∀ (e : Ent) (p p' : BPath) (f : Ent → Ent),
    ¬ p.IsPrefix p' → ¬ p'.IsPrefix p → (e.modAt p f).atPath p' = e.atPath p'

/-- **Lookup after `setKey`** in a bucket: the key gives what was set (`some x`: put, inserted or
replaced; `none`: deleted), every other key what it gave before. (A value's `setKey` is the value,
whose `lookup` is `none`: hence the bucket premise.) -/
def lookup_setKey.spec : Prop :=
  ∀ (e : Ent) (k k' : GoString) (x : Option Ent), e.isBkt = true →
    (e.setKey k x).lookup k' = if k' = k then x else e.lookup k'

/-- **A put or delete at a bucket, seen at its key's path** (`Get` after `Put`/`Delete`): with a
bucket at `p`, the key's path holds what was set. Other keys' paths are unchanged
(`atPath_modAt_other.spec`: `p.child k` and `p.child k'` are not prefixes of each other). -/
def atPath_child_setKey.spec : Prop :=
  ∀ (e : Ent) (p : BPath) (k : GoString) (x : Option Ent), e.bktAt p →
    (e.modAt p (fun b => b.setKey k x)).atPath (p.child k) = x

/-- **The cursor order after a put** (`curEnts`, what `Seek`/`Next` return): in a well-formed
bucket (keys strictly sorted, so the entries before `k` are the `seekIdx` first, and at most the
next one has the key `k`), the entry `(k, x.curVal)` is at `seekIdx`, after the entries below `k`
and before those above it, replacing the old entry of `k` if there was one. (A bucket: a value's
`setKey` is the value, whose `curEnts` stays `[]`.) -/
def curEnts_put.spec : Prop :=
  ∀ (e : Ent) (k : GoString) (x : Ent), e.isBkt = true → e.wf →
    (e.setKey k (some x)).curEnts =
      e.curEnts.take (seekIdx e.curEnts k) ++ (k, x.curVal) ::
        (e.curEnts.drop (seekIdx e.curEnts k)).filter (fun c => decide (c.1 ≠ k))

/-- **The cursor order after a delete**: the entries without the key (in order; a value's
`setKey` is the value, whose `curEnts` is `[]` either way). -/
def curEnts_del.spec : Prop :=
  ∀ (e : Ent) (k : GoString),
    (e.setKey k none).curEnts = e.curEnts.filter (fun c => decide (c.1 ≠ k))

/-- **A put keeps an entry well-formed** under the entry bounds (a key non-empty and at most
`maxKeySize`; a value's key and value together at most `bboltEntryMax`; a nested bucket itself
well-formed): what `Put`'s and `CreateBucket*`'s premises give. Sorted insertion: `GoStringLt`,
the bytes' lexicographic order, is a strict total order. -/
def wf_setKey.spec : Prop :=
  ∀ (e : Ent) (k : GoString) (x : Ent), e.wf → k ≠ [] → k.length ≤ maxKeySize → x.wf →
    (∀ v, x = Ent.val v → k.length + v.length ≤ bboltEntryMax) → (e.setKey k (some x)).wf

/-- **A delete keeps an entry well-formed** (a filter keeps the order and the bounds). -/
def wf_delKey.spec : Prop :=
  ∀ (e : Ent) (k : GoString), e.wf → (e.setKey k none).wf

/-- **`modAt` keeps an entry well-formed** when it changes a bucket into a well-formed bucket
(the key on the way to it unchanged, a bucket's entry not under the value bound). With no entry
at `p` it changes nothing. (A value at `p` is excluded: a longer value could break its parent's
entry bound.) -/
def wf_modAt.spec : Prop :=
  ∀ (e : Ent) (p : BPath) (f : Ent → Ent), e.wf →
    (∀ c, e.atPath p = some c → c.isBkt = true ∧ (f c).isBkt = true ∧ (f c).wf) →
    (e.modAt p f).wf

/-- **The bucket paths are the paths of buckets** (not the root), without duplicates, in a
well-formed entry (distinct keys: `lookup` finds the one entry of each key). -/
def bktPaths_mem.spec : Prop :=
  ∀ (e : Ent), e.wf →
    (∀ q, q ∈ e.bktPaths ↔ q ≠ [] ∧ e.bktAt q) ∧ e.bktPaths.Nodup

/-- **The buckets under `q`** are the buckets at paths extending `q`, without duplicates, in a
well-formed entry. -/
def bktsUnder_mem.spec : Prop :=
  ∀ (e : Ent) (q : BPath), e.wf →
    (∀ d, d ∈ e.bktsUnder q ↔ q.IsPrefix d ∧ e.bktAt d) ∧ (e.bktsUnder q).Nodup

/-- **The bucket paths after a bucket's creation** (`CreateBucket*` of a key absent from the
bucket at `p`): the new bucket's path and its own buckets' (none for `CreateBucket`'s empty
bucket) join the old ones, up to order. Well-formed data: keys sorted and distinct, so `setKey`
on each ancestor replaces its one entry (on unsorted entries `insEnt` could insert a second copy
of an ancestor's key, whose paths `bktPaths` would count twice). What a client keeping
`[∗list] d ∈ T.cur.bktPaths, …` (the backend's lock invariant) rebuilds its list by. -/
def bktPaths_create.spec : Prop :=
  ∀ (e : Ent) (p : BPath) (k : GoString) (x : Ent), e.wf → e.bktAt p →
    e.atPath (p.child k) = none → x.isBkt = true →
    (e.modAt p (fun b => b.setKey k (some x))).bktPaths.Perm
      ((p.child k :: x.bktPaths.map (p.child k ++ ·)) ++ e.bktPaths)

/-- **The bucket paths after a bucket's deletion** (`DeleteBucket`, `TxView.dropBkt`): those at or
below `p.child k` go (the tokens `DeleteBucket` consumes, `bktsUnder`), the others stay, up to
order. With no bucket at `p.child k` (absent, a value), nothing goes; with no bucket at `p`,
`modAt` changes nothing. -/
def bktPaths_dropBkt.spec : Prop :=
  ∀ (e : Ent) (p : BPath) (k : GoString), e.wf →
    (e.modAt p (fun b => b.setKey k none)).bktPaths.Perm
      (e.bktPaths.filter (fun d => !((p.child k).isPrefixOf d)))

/-- **A value's put or delete leaves the bucket paths as they were** (`Put`, `Delete`,
`Cursor.Delete`: the key holds no bucket, and what is set is a value or nothing; values add no
path, so even the order is kept). -/
def bktPaths_setVal.spec : Prop :=
  ∀ (e : Ent) (p : BPath) (k : GoString) (x : Option Ent), e.wf →
    (e.atPath (p.child k)).any Ent.isBkt = false → (∀ y, x = some y → y.isBkt = false) →
    (e.modAt p (fun b => b.setKey k x)).bktPaths = e.bktPaths

/-- **A sequence update leaves the bucket paths as they were** (`SetSequence`, `NextSequence`:
`setSeq` keeps a bucket's entries). -/
def bktPaths_setSeq.spec : Prop :=
  ∀ (e : Ent) (p : BPath) (n : w64), e.wf →
    (e.modAt p (fun b => b.setSeq n)).bktPaths = e.bktPaths

end Ent

end Bbolt
end EtcdGrove
end Perennial
