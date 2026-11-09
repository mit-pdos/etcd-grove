/-
# bbolt's public API: the vocabulary (batch 4c)

What a proof outside bbolt uses of bbolt (`DB`, `Tx`, `Bucket`, `Cursor`): this module, the pure
model (`Model.lean`) and one spec file per function (`Spec/go_etcd_io/bbolt/<T>__<M>.lean`). It
replaces the frozen spec of 2026-11-03 (`specs-ref/Spec/go_etcd_io/bbolt/`,
`.claude/skills/spec/examples/bbolt-api.md`), whose user decisions it keeps (D1, D3-D5, D7, D13,
D17, D18, D20, D21, D22: below where each lands), and extends it to nested buckets, sequences,
`View`/`Update`, `ForEach`, `WriteTo`, `Sync`, a custom `OpenFile`, mutations on read transactions
(their errors) and **durability across crashes**.

Every predicate is stated over the Linux file extension OsFs (`GooseLang/Ext/OsFs/`): each takes
`[HasExt osFsExt]` and the generation's heap `[hG : HeapGS HasLC.hasLC GF]` **in its own
signature** (a section variable an opaque body does not use is dropped, PRINCIPLES "An instance
binder a statement must carry goes inside the statement"; the generation matters to the crash law,
whose two sides are in two generations).

## Names

`BoltName` (opaque) names **one database file for one generation** (from its allocation by
`fileHolds_alloc` to the next crash), across any number of `Open`/`Close`: `γ.path` its file,
`γ.ns` the namespace the client chose for bbolt's invariants (D-round 2: the masks of bbolt's
updates are `⊤ \ ↑γ.ns`).

## Resources

* **`boltState γ q σ`** (fractional, timeless): **the database's state is `σ`** (`BoltSt`: the
  committed data and what a crash may recover), the client's: it keeps it where it wants (a lock, an
  invariant: a crash-safe client keeps it in an invariant, which the crash law reads), and bbolt
  changes it only by the client's atomic updates (a read's at `Begin(false)`, a commit's and a
  sync's). Intended realization: the client's half of a ghost variable of `σ`, whose other half is
  in the file's crash invariant (`boltFile`).
* **`boltFile γ`** (persistent): **the crash invariant of `γ`'s file**: it holds, at every step,
  the file's OsFs resources (a half of each byte and of its `OsMeta`, as the old
  `Proof/os/CrashSt.lean`'s `csInv`; the other half is the open database's, or the invariant's
  while closed) and the other half of `σ`, with the fact that **every image a crash may leave**
  (OsFs's crash relation, with D9's aligned page rule and the sector rule of the report's decision
  4c-D1) **is a bbolt file whose data `σ.recovers`**. This is the meta-page rule: a commit writes
  its pages, syncs them, then writes its meta page (one aligned OS page) at page `txid % 2` (the
  page the current meta is not on), then syncs; at every point the newest valid meta of any crash
  image is the old or the new one.
* **`boltClosed γ`** (exclusive): the file is closed: the right to `Open` it.
* **`isBolt db γ ns`** (persistent): `db` is an open (or closed by a `Close`, after which `Begin`
  fails) `*DB` of `γ`'s file, opened with `NoSync = ns`. It carries bbolt's package initialization
  and its invariants (the locks, the mapping, the freelist, the readers' pool of `mmaplock` reader
  slots lent for a `threadTok`, one spare kept for the writer's `freepages`, the commit counter
  backed by time receipts). It owns `DB`'s exported fields (`StrictMode`, `NoSync`, `MaxSize`,
  `AllocSize`, ...): a client must not write them after `Open` (no client holds their
  points-to; etcd writes none).
* **`boltOpened db γ`** (exclusive): the right to close `db` and get `boltClosed γ` back; while it
  is held, `db` stays open. **`dbClosed db`** (persistent): `db` was closed (a later `Close` does
  nothing).
* **`boltTx tx γ q T`** (fractional): `tx` is a live transaction of `γ` with the view `T`
  (`TxView`). A read transaction's whole holds the reader slot its `Begin` took for the caller's
  `threadTok`; a write transaction holds `rwlock`. Read operations take any fraction; a write
  transaction's operations that change it, or its node cache, take all of it. It owns `Tx`'s
  exported field `WriteFlag` (at `0`).
* **`txDone tx`** (persistent): `tx` was committed or rolled back (its statistics can be read).
* **`txDB tx db`** (persistent): `tx` is a transaction of the `*DB` `db`.
* **`bktH tx γ b p gs`** (persistent): `b` is `tx`'s handle of the bucket at path `p`, made when
  the generations of `p`'s prefixes were `gs` (`TxView.gens`). Its operations need `T.gens p = gs`
  (`bktH_live`: the bucket then exists). Owns nothing but `FillPercent`'s use (`boltTx_fill`).
* **`boltCur tx γ c p gs T pos`** (exclusive): `c` is a cursor of `tx` over the bucket at `p`
  (handle generations `gs`), last positioned at the view `T`, at `pos` (`none`: not positioned;
  `some i`, `i ≤ (T.ents p).length`: at the `i`-th entry, or past the last). `Next`/`Prev` need
  the transaction still at `T`; `First`/`Last`/`Seek` reposition it at the current view (Go:
  "reposition your cursor after mutating data").
* **`txBytes tx γ s b`** (persistent): the slice `s` holds `b` while `tx` is live (a key or value
  bbolt returned: in the mapping or the transaction's nodes); read through `txBytes_acc`.
* **`fileHolds path D`** (exclusive, timeless): **the file at `path` holds a database with the
  data `D`, all of it durable**, in the generation's OsFs terms (`osMeta`, `osBytes`, every byte
  clean; or no file, or an empty one, or one `init` redoes: then `D = Data.empty`), well-formed
  as the old `fileHolds`' docstring lists (valid metas recording page size 4096, the current at page
  `txid % 2`, the tree's pages within the high-water mark, disjoint, sorted, exact branch keys, no
  empty non-root page, leaves at one depth, an inline bucket's page a leaf within its value, entries
  within `bboltEntryMax`, bucket names within `maxKeySize`, a synced freelist page well-formed, the
  txid at least 1 and below the receipts' bound). What a generation starts from: `fileHolds_new`
  (a fresh path), `fileHolds_image` (a snapshot file), and the crash law's conclusion.
* **`optsAt l dq o`**: the `Options` at `l` (an axiomatized type) has the fields `o`.

## Contracts (opaque, the client's to establish)

* `boltLogger l`: the logger `l` (or nil) may be called as bbolt does (`Debugf`, `Errorf`, `Infof`,
  `Warningf` with a format and its arguments, `%v`/`%s`/`%d` of errors, strings, numbers and
  byte slices; the old `Logger.lean`'s `boltLogger`, D20′): each call returns and reads its
  arguments only. `boltLogger_nil`.
* `openFileOk f path`: the `OpenFile` option `f` called with `(path, O_RDWR|O_CREATE, mode)`
  returns an `*os.File` open read-write on `path`'s OsFs file (an fd of it, as `os.OpenFile`
  would), or an error; the caller (etcd's defrag) proves it from the file it already opened.
* `writerOk w W` (transparent): an `io.Writer` `w` whose `Write` appends a prefix of its argument
  to the stream `W` (the client's predicate of what was written), all unless it fails; with
  `writerPlain`: its dynamic type has no `ReadFrom` (else `io.CopyN` calls that instead).
* `boltImage bs D` (an opaque pure fact): `bs` is a bbolt file image holding `D`, which `Open`
  reads as `D` (realized with batch 4d's decoders: `BboltCommon.metaOf`, `pageItems`, ...).

## Laws

Persistence, timelessness, fractions, agreement, validity, exclusivity of each predicate;
`boltTx_later`, `boltTx_nonnull`, `boltTx_base`, `bktH_live`, `txBytes_acc`, `boltTx_fill`; the
updates a holder of `boltState γ 1 σ` can supply (`boltState_read_au`, `boltState_commit_au`,
`boltState_settle_au`); the file laws (`fileHolds_new`, `fileHolds_image`, `fileHolds_alloc`) and
**the crash law** (`boltCrash`); the error values (`errIs`, `errIs_distinct`).

## Requirement snippets (`examples/specreq/bbolt/`)

`ReqBackendBatch` (the backend's batch: `Begin(true)`, `CreateBucketIfNotExists`, `Bucket`,
`FillPercent`, `Put`, `Delete`, a range by `Seek`/`Next`, `Commit`, `Stats`), `ReqBackendRead` (the
read transaction: `Begin(false)`, `Bucket`, `Cursor`, `Rollback`, `Size`, `DB().Info()`),
`ReqDeleteBucketNotFound`, `ReqHash` (`View`, root cursor, `ForEach`), `ReqSnapshot` (`WriteTo`),
`ReqDefrag` (two databases, custom `OpenFile`, `NoSync`, `Sync`, `Close`), `ReqBank` (crash
safety: atomicity and durability of `Update`, `View` snapshots), `ReqNested` (nested buckets,
`NextSequence`), `ReqReadOnlyPut` (a mutation on a read transaction fails),
`ReqCursorDelete`.
-/
module

public import GeneratedProof.go_etcd_io.bbolt
public import GeneratedProof.go_etcd_io.bbolt.errors
public import Spec.PkgInit.go_etcd_io.bbolt
public import Spec.PkgInit.go_etcd_io.bbolt.errors
public import Perennial.ProgramLogic.Bounds
public import Iris.BI.Lib.Atomic
public import GooseLang.Ext.OsFs.Crash
public import Spec.go_etcd_io.bbolt.Model

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Bbolt

open Iris Iris.BI go_etcd_io.bbolt

/-! ## Names -/

/-- **A database file's ghost names, for one generation** (see the header). Opaque. -/
opaque BoltName : Type := Unit

/-- The namespace of `γ`'s invariants (the client's choice at `fileHolds_alloc`). -/
opaque BoltName.ns : BoltName → Namespace

/-- The path of `γ`'s file. -/
opaque BoltName.path : BoltName → GoString

/-! ## Resources -/

section vocab
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors}

/-- **The database's state is `σ`**, at fraction `q` (the client's; see the header). -/
opaque boltState [HasExt osFsExt] [hG : HeapGS HasLC.hasLC GF] (γ : BoltName) (q : Qp)
    (σ : BoltSt) : IProp GF := iprop(True)

/-- **The crash invariant of `γ`'s file** (persistent; see the header). -/
opaque boltFile [HasExt osFsExt] [hG : HeapGS HasLC.hasLC GF] (γ : BoltName) : IProp GF :=
  iprop(True)

/-- `γ`'s file is closed: the right to open it (exclusive). -/
opaque boltClosed [HasExt osFsExt] [hG : HeapGS HasLC.hasLC GF] (γ : BoltName) : IProp GF :=
  iprop(True)

/-- **`db` is an open `*DB` of `γ`'s file with `NoSync = ns`** (persistent; see the header). -/
opaque isBolt [HasExt osFsExt] [hG : HeapGS HasLC.hasLC GF] (db : Loc) (γ : BoltName)
    (ns : Bool) : IProp GF := iprop(True)

/-- The right to close `db` (exclusive). -/
opaque boltOpened [HasExt osFsExt] [hG : HeapGS HasLC.hasLC GF] (db : Loc) (γ : BoltName) :
    IProp GF := iprop(True)

/-- `db` was closed (persistent): a later `Close` does nothing. -/
opaque dbClosed [HasExt osFsExt] [hG : HeapGS HasLC.hasLC GF] (db : Loc) : IProp GF := iprop(True)

/-- **`tx` is a live transaction of `γ` with the view `T`**, at fraction `q`. -/
opaque boltTx [HasExt osFsExt] [hG : HeapGS HasLC.hasLC GF] (tx : Loc) (γ : BoltName) (q : Qp)
    (T : TxView) : IProp GF := iprop(True)

/-- `tx` is a transaction of the `*DB` `db` (persistent; what `Tx.DB` returns). -/
opaque txDB [HasExt osFsExt] [hG : HeapGS HasLC.hasLC GF] (tx db : Loc) : IProp GF := iprop(True)

/-- `tx` was committed or rolled back (persistent). -/
opaque txDone [HasExt osFsExt] [hG : HeapGS HasLC.hasLC GF] (tx : Loc) : IProp GF := iprop(True)

/-- **`b` is `tx`'s handle of the bucket at `p`**, made at the generations `gs` (persistent). -/
opaque bktH [HasExt osFsExt] [hG : HeapGS HasLC.hasLC GF] (tx : Loc) (γ : BoltName) (b : Loc)
    (p : BPath) (gs : List Nat) : IProp GF := iprop(True)

/-- **`c` is a cursor of `tx` over the bucket at `p`**, last positioned at the view `T`, at
`pos` (exclusive). -/
opaque boltCur [HasExt osFsExt] [hG : HeapGS HasLC.hasLC GF] (tx : Loc) (γ : BoltName) (c : Loc)
    (p : BPath) (gs : List Nat) (T : TxView) (pos : Option Nat) : IProp GF := iprop(True)

/-- The slice `s` holds `b` while `tx` is live (persistent). -/
opaque txBytes [HasExt osFsExt] [hG : HeapGS HasLC.hasLC GF] (tx : Loc) (γ : BoltName)
    (s : GoSlice) (b : GoString) : IProp GF := iprop(True)

/-- **The file at `path` holds a database with the data `D`, all durable** (exclusive). -/
opaque fileHolds [HasExt osFsExt] [hG : HeapGS HasLC.hasLC GF] (path : GoString) (D : Data) :
    IProp GF := iprop(True)

/-- The `Options` at `l`, at fraction `dq`, has the fields `o`. -/
opaque optsAt [HasExt osFsExt] [hG : HeapGS HasLC.hasLC GF] (l : Loc) (dq : DFrac) (o : OptsM) :
    IProp GF := iprop(True)

/-- `Open`'s options argument: `nil` (`DefaultOptions`), or an `Options` with the fields `o`. -/
def optsArg [HasExt osFsExt] [hG : HeapGS HasLC.hasLC GF] (l : Loc) (dq : DFrac) (o : OptsM) :
    IProp GF :=
  iprop((⌜l = Loc.null ∧ o = OptsM.dflt⌝) ∨ (⌜l ≠ Loc.null⌝ ∗ optsAt l dq o))

/-- **The logger contract** (persistent; see the header). -/
opaque boltLogger [HasExt osFsExt] [hG : HeapGS HasLC.hasLC GF] (l : GoInterface) : IProp GF :=
  iprop(True)

/-- **The `OpenFile` contract** for `path` (persistent; see the header). -/
opaque openFileOk [HasExt osFsExt] [hG : HeapGS HasLC.hasLC GF] (f : GoFunc) (path : GoString) :
    IProp GF := iprop(True)

/-- `bs` is a bbolt file image holding `D` (see the header). -/
opaque boltImage (bs : List w8) (D : Data) : Prop

/-- The dynamic type of `wi` has no `ReadFrom` method. -/
opaque writerPlain (wi : GoInterfaceOk) : Prop

end vocab

section contracts
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **An `io.Writer` `w` appending to the stream `W`** (`W bs`: `bs` was written so far; the
client's): its `Write(b)` writes a prefix of `b`, all of it unless it fails. -/
def writerOk (w : GoInterface) (W : List w8 → IProp GF) :
    IProp GF :=
  iprop(∃ wi : GoInterfaceOk, ⌜w = interface.ok wi ∧ writerPlain wi⌝ ∗
    □ ∀ (bs : List w8) (b : GoSlice) (ys : List w8) (dq : DFrac) (Φ : val → IProp GF),
      W bs -∗ b ↦*{dq} ys -∗
      ▷ (∀ (n : w64) (err : GoInterface), b ↦*{dq} ys -∗
          ⌜uint.nat n ≤ ys.length ∧ (err = interface.nil → uint.nat n = ys.length)⌝ -∗
          W (bs ++ ys.take (uint.nat n)) -∗ Φ (PairV #n #err)) -∗
      WP (App (Val #(methods wi.ty go!"Write" wi.v)) (Val #b)) {{ Φ }})

/-- `err` is the value of `go.etcd.io/bbolt/errors`' variable `g` (`ErrBucketNotFound`, ...). -/
def errIs (g : GoString) (err : GoInterface) : IProp GF :=
  iprop(globalAddr g ↦□ err)

/-- `err` is the (non-nil) error `g` of `go.etcd.io/bbolt/errors`. -/
def isErr (g : GoString) (err : GoInterface) : IProp GF :=
  iprop(⌜err ≠ interface.nil⌝ ∗ errIs g err)

end contracts

section vocab2
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors}

/-- What a cursor move to the `i`-th entry of `es` returns: its key (never nil: keys are not
empty) and its value (nil for a nested bucket), valid while `tx` is live; nil and nil past the
end. -/
def curAt [HasExt osFsExt] [hG : HeapGS HasLC.hasLC GF] (tx : Loc) (γ : BoltName)
    (es : List CurEnt) (i : Nat) (k v : GoSlice) : IProp GF :=
  match es[i]? with
  | some (kb, some vb) => iprop(⌜k ≠ slice.nil⌝ ∗ txBytes tx γ k kb ∗ txBytes tx γ v vb)
  | some (kb, none) => iprop(⌜k ≠ slice.nil ∧ v = slice.nil⌝ ∗ txBytes tx γ k kb)
  | none => iprop(⌜k = slice.nil ∧ v = slice.nil⌝)

/-- What pays for `statlock`'s reader slot in `DB.Stats` (the old `statSlot`, D2): the caller's
`threadTok` (`none`), or the whole of a read transaction (`some (tx, T)`), whose reader slot covers
`statlock` too (the reader pool lends a pair per token). -/
def statSlot [HasExt osFsExt] [hG : HeapGS HasLC.hasLC GF] (γ : BoltName) :
    Option (Loc × TxView) → IProp GF
  | none => threadTok
  | some (tx, T) => iprop(boltTx tx γ 1 T ∗ ⌜T.rw = false⌝)

end vocab2

/-! ## Laws -/

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The error variables of `go.etcd.io/bbolt/errors` bbolt's public API returns. -/
def bboltErrNames : List GoString :=
  [go_etcd_io.bbolt.errors.ErrBucketNotFound, go_etcd_io.bbolt.errors.ErrBucketExists,
   go_etcd_io.bbolt.errors.ErrIncompatibleValue, go_etcd_io.bbolt.errors.ErrTxNotWritable,
   go_etcd_io.bbolt.errors.ErrTxClosed, go_etcd_io.bbolt.errors.ErrDatabaseNotOpen,
   go_etcd_io.bbolt.errors.ErrKeyRequired, go_etcd_io.bbolt.errors.ErrKeyTooLarge,
   go_etcd_io.bbolt.errors.ErrBucketNameRequired]

/-- The persistent predicates. -/
def persistent.spec [HasExt osFsExt] : Prop :=
  (∀ γ, Persistent (boltFile (GF := GF) γ)) ∧
  (∀ db γ ns, Persistent (isBolt (GF := GF) db γ ns)) ∧
  (∀ tx, Persistent (txDone (GF := GF) tx)) ∧
  (∀ tx db, Persistent (txDB (GF := GF) tx db)) ∧
  (∀ db, Persistent (dbClosed (GF := GF) db)) ∧
  (∀ tx γ b p gs, Persistent (bktH (GF := GF) tx γ b p gs)) ∧
  (∀ tx γ s b, Persistent (txBytes (GF := GF) tx γ s b)) ∧
  (∀ l, Persistent (boltLogger (GF := GF) l)) ∧
  (∀ f path, Persistent (openFileOk (GF := GF) f path))

/-- The timeless predicates (`boltTx` is not: it holds the locks' invariants; `boltTx_later`). -/
def timeless.spec [HasExt osFsExt] : Prop :=
  (∀ γ q σ, Timeless (boltState (GF := GF) γ q σ)) ∧
  (∀ γ, Timeless (boltClosed (GF := GF) γ)) ∧
  (∀ db γ, Timeless (boltOpened (GF := GF) db γ)) ∧
  (∀ tx γ c p gs T pos, Timeless (boltCur (GF := GF) tx γ c p gs T pos)) ∧
  (∀ path D, Timeless (fileHolds (GF := GF) path D))

/-- `boltState` is fractional, its fractions agree, and the whole is at most `1`. -/
def boltState_frac.spec [HasExt osFsExt] : Prop :=
  (∀ γ σ, Fractional (fun q => boltState (GF := GF) γ q σ)) ∧
  (∀ γ q1 q2 σ1 σ2, boltState (GF := GF) γ q1 σ1 ∗ boltState γ q2 σ2 ⊢ ⌜σ1 = σ2⌝) ∧
  (∀ γ q σ, boltState (GF := GF) γ q σ ⊢ ⌜q ≤ 1⌝)

/-- The exclusive tokens. -/
def excl.spec [HasExt osFsExt] : Prop :=
  (∀ γ, boltClosed (GF := GF) γ ∗ boltClosed γ ⊢ False) ∧
  (∀ db γ, boltOpened (GF := GF) db γ ∗ boltOpened db γ ⊢ False) ∧
  (∀ path D D', fileHolds (GF := GF) path D ∗ fileHolds path D' ⊢ False)

/-- **A later transaction is a transaction, given its database** (the old D-A: `boltTx` holds
the locks' and bbolt's invariants, which are not timeless; they come from `isBolt`). -/
def boltTx_later.spec [HasExt osFsExt] : Prop :=
  ∀ db tx γ ns q T, isBolt (GF := GF) db γ ns ⊢ ▷ boltTx tx γ q T -∗ ◇ boltTx tx γ q T

/-- `boltTx` is fractional; two fractions agree on the view; the whole is at most `1`; a live
transaction is a non-nil `*Tx`. -/
def boltTx_frac.spec [HasExt osFsExt] : Prop :=
  (∀ tx γ T, Fractional (fun q => boltTx (GF := GF) tx γ q T)) ∧
  (∀ tx γ q1 q2 T1 T2, boltTx (GF := GF) tx γ q1 T1 ∗ boltTx tx γ q2 T2 ⊢ ⌜T1 = T2⌝) ∧
  (∀ tx γ q T, boltTx (GF := GF) tx γ q T ⊢ ⌜q ≤ 1⌝) ∧
  (∀ tx γ q T, boltTx (GF := GF) tx γ q T ⊢ ⌜tx ≠ Loc.null⌝)

/-- **While a write transaction is live, the committed data is the one it began at** (it holds
`rwlock`; only it can commit). How a client learns the data `Begin(true)` began at. -/
def boltTx_base.spec [HasExt osFsExt] : Prop :=
  ∀ tx γ q q' T σ, boltTx (GF := GF) tx γ q T ∗ boltState γ q' σ ⊢
    ⌜T.rw = true → T.base = σ.data⌝

/-- **A current handle's bucket exists** (in the transaction's data now). -/
def bktH_live.spec [HasExt osFsExt] : Prop :=
  ∀ tx γ q T b p gs, boltTx (GF := GF) tx γ q T ∗ bktH tx γ b p gs ∗ ⌜T.gens p = gs⌝ ⊢
    ⌜T.cur.bktAt p⌝

/-- A slice the transaction returned is read while the transaction is live (any fraction). -/
def txBytes_acc.spec [HasExt osFsExt] : Prop :=
  ∀ tx γ q T s b, txBytes (GF := GF) tx γ s b ∗ boltTx tx γ q T ⊢
    ∃ dq : DFrac, s ↦*{dq} b ∗ (s ↦*{dq} b -∗ boltTx tx γ q T)

/-- **A bucket handle's `FillPercent` field** (exported; the backend writes `0.9`), of any handle
of a write transaction, with all of it: read, and written back with any value but a NaN (a NaN
makes `Commit` panic on a large leaf: `nonissues/bbolt-fillpercent-nan.md`; the old D5). -/
def boltTx_fill.spec [HasExt osFsExt] : Prop :=
  ∀ tx b γ T p gs, T.rw = true →
    boltTx (GF := GF) tx γ 1 T ∗ bktH tx γ b p gs ⊢
      ∃ f : w64, structFieldRef go_etcd_io.bbolt.Bucket go!"FillPercent" b ↦ f ∗
        (∀ f' : w64, ⌜¬ float64IsNaN f'⌝ -∗
          structFieldRef go_etcd_io.bbolt.Bucket go!"FillPercent" b ↦ f' -∗ boltTx tx γ 1 T)

/-- **A holder of the whole state supplies a read's update** (the layer a client holding
`boltState γ 1 σ` in a lock uses: the backend's batch lock). -/
def boltState_read_au.spec [HasExt osFsExt] : Prop :=
  ∀ γ σ, boltState (GF := GF) γ 1 σ ⊢
    AU <{ ∃∃ (q : Qp) (σ' : BoltSt), boltState γ q σ' }> @ ⊤ \ ↑γ.ns, ∅
      <{ boltState γ q σ', COMM boltState γ 1 σ ∗ ⌜σ' = σ⌝ }>

/-- **A holder of the whole state supplies a commit's update** of the data `D` from `σ`. -/
def boltState_commit_au.spec [HasExt osFsExt] : Prop :=
  ∀ γ σ D ns, boltState (GF := GF) γ 1 σ ⊢
    AU <{ ∃∃ (σ' : BoltSt), boltState γ 1 σ' }> @ ⊤ \ ↑γ.ns, ∅
      <{ ∀∀ (ok : Bool), boltState γ 1 (if ok then σ'.commit D ns else σ'.attempt D ns),
         COMM ⌜σ' = σ⌝ ∗ boltState γ 1 (if ok then σ.commit D ns else σ.attempt D ns) }>

/-- **A holder of the whole state supplies a commit's settling update** (and a sync's). -/
def boltState_settle_au.spec [HasExt osFsExt] : Prop :=
  ∀ γ σ, boltState (GF := GF) γ 1 σ ⊢
    AU <{ ∃∃ (σ' : BoltSt), boltState γ 1 σ' }> @ ⊤ \ ↑γ.ns, ∅
      <{ ∀∀ (σ'' : BoltSt), boltState γ 1 σ'', COMM ⌜σ' = σ⌝ ∗ boltState γ 1 σ'' }>

/-- **A fresh path holds the empty database**: no file, or an empty one with no mapping. -/
def fileHolds_new.spec [HasExt osFsExt] : Prop :=
  ∀ (path : GoString) (mo : Option OsMeta),
    osMeta (GF := GF) path (DFrac.own 1) mo ∗
      (match mo with
       | none => iprop(emp)
       | some m => iprop(⌜m.size = 0 ∧ m.maps = ∅⌝ ∗ osBytes (GF := GF) path 0 (DFrac.own 1) []))
    ⊢ fileHolds path Data.empty

/-- **A durable file image of `D` holds `D`** (a snapshot written by `WriteTo`, then synced): its
bytes all clean, its size and name durable, no mapping. -/
def fileHolds_image.spec [HasExt osFsExt] : Prop :=
  ∀ (path : GoString) (m : OsMeta) (xs : List (w8 × Bool)) (D : Data),
    ⌜boltImage (xs.map Prod.fst) D ∧ (∀ x ∈ xs, x.2 = true) ∧ m.size = xs.length ∧
      m.lo = xs.length ∧ m.hi = xs.length ∧ m.named = true ∧ m.maps = ∅⌝ ∗
    osMeta (GF := GF) path (DFrac.own 1) (some m) ∗ osBytes (GF := GF) path 0 (DFrac.own 1) xs
    ⊢ fileHolds path D

/-- **Allocating a database's names over a file** (a ghost step, at the start of a generation or
for a new file): its crash invariant, the closed token, and all of its state `BoltSt.init D`, in
the namespace `N` the client chooses (disjoint from OsFs's: bbolt's invariants stay open across
OsFs steps). -/
def fileHolds_alloc.spec [HasExt osFsExt] : Prop :=
  ∀ (E : CoPset) (N : Namespace) (path : GoString) (D : Data), ↑N ## ↑osN →
    fileHolds (GF := GF) path D ⊢ |={E}=> ∃ γ : BoltName, ⌜γ.ns = N ∧ γ.path = path⌝ ∗
      boltFile γ ∗ boltClosed γ ∗ boltState γ 1 (BoltSt.init D)

/-- **The crash law.** After the generation crashes (its `crashed`), from the file's crash
invariant and any fraction of the state `σ` (a crash-safe client keeps one in an invariant, which
survives the crash), the next generation `L'` gets the file holding a state `σ` says a crash may
recover, out of the extension's restart resources (`crashRest`, the files not yet taken `Ps`).
Nothing is promised when `σ.dur = none` (a `NoSync` commit not synced). -/
def boltCrash.spec [HasExt osFsExt] : Prop :=
  ∀ (L' : GooseLocalGS GF) (γ : BoltName) (q : Qp) (σ : BoltSt) (ds : List Data)
    (Ps : List GoString),
    σ.dur = some ds → γ.path ∉ Ps →
    boltFile (GF := GF) γ ∗ boltState γ q σ ∗ crashed ∗
      crashRest (gooseOsGS (L := hG.goose_localGS)) (gooseOsGS (L := L')) Ps ⊢
    |={⊤}=> ∃ D : Data, ⌜σ.recovers D⌝ ∗
      @fileHolds _ _ _ GF _ ⟨hG.goose_globalGS, L'⟩ γ.path D ∗
      crashRest (gooseOsGS (L := hG.goose_localGS)) (gooseOsGS (L := L')) (γ.path :: Ps)

/-- The nil logger meets the contract (`Open` replaces it by the discard logger). -/
def boltLogger_nil.spec [HasExt osFsExt] : Prop :=
  ⊢ boltLogger (GF := GF) GoInterface.nil

/-- **bbolt's error values are distinct and non-nil** (`errors.New`'s in `bbolt/errors`'
initializer; batch 4c needs: `ErrBucketNotFound`, `ErrBucketExists`, `ErrIncompatibleValue`,
`ErrTxNotWritable`, `ErrTxClosed`, `ErrDatabaseNotOpen`, `ErrKeyRequired`, `ErrKeyTooLarge`,
`ErrBucketNameRequired`). A fact of the package's globals after initialization. -/
def errIs_distinct.spec : Prop :=
  ∀ (g g' : GoString) (e e' : GoInterface), g ∈ bboltErrNames → g' ∈ bboltErrNames →
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.errors ∗ errIs g e ∗ errIs g' e' ⊢
      ⌜e ≠ interface.nil ∧ (g ≠ g' → e ≠ e')⌝

end laws

end Bbolt
end EtcdGrove
end Perennial
