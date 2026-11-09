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
  (OsFs's crash relation, with D9's aligned page rule, **plus the sector rule of decision 4c-D1**)
  **is a bbolt file whose data `σ.recovers`** (or no file, while its name is not durable:
  `BoltSt.named`, verify-round A11 F1; then `σ.recovers Data.empty`). This is the meta-page rule: a commit writes its pages,
  syncs them, then writes its meta page (one aligned OS page) at page `txid % 2` (the page the
  current meta is not on), then syncs; at every point the newest valid meta of any crash image is
  the old or the new one.

  **The sector rule (decision 4c-D1, open; sharpened at the verify round, A11 F2 and F10).** A
  sector written by one `pwrite` since the last successful sync of the file holds, in a crash
  image, its durable bytes or that write's bytes; **a sector past the durable size** (no durable
  bytes: `init`'s first write of four pages over an empty file, `db.go:722-731`, before its
  sync) **holds zeros or that write's bytes** (true of ext4 `data=ordered` and xfs, which never
  expose unwritten blocks; false of ext4 `data=writeback`, which the environment hypothesis
  excludes). So a crash before `init`'s first sync leaves zero metas, which the next `Open`'s
  `metasZero` sends to `init` again (`Data.empty`). OsFs's crash relation knows neither half today
  (`CrashImage`: bytes past the durable image are arbitrary). The two options: **(a)** the rule
  goes into OsFs's crash relation, which then carries the ghost record of the writes since the
  last sync (so `crashRest`'s `CrashRel` states it), and `boltCrash.spec` is stated over
  `crashRest` as below; **(b)** the rule is a crash premise of every bbolt closed theorem, and
  `boltCrash.spec` is stated over OsFs's premise-carrying restart resources (`crashRestQ`,
  `CrashP1.lean`) in place of `crashRest`. The law's **conclusion** (a file holding a state `σ`
  recovers) is the same under both; its **statement** is the one written below under (a), and
  changes to `crashRestQ` under (b). Under OsFs as it is, it is false.
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
  bbolt returned: in the mapping or the transaction's nodes); read through `txBytes_acc`, **against a
  share of the transaction's liveness `txLive tx p`**, not of `boltTx`.
* **`txLive tx p`** (fractional; integration Y, I6's request for the backend's compaction): **a
  share of "`tx` is not closed"**: the bytes it returned stay valid (the mapping is not remapped
  before the commit; a node's bytes are never written in place). `Begin` gives the whole with
  `boltTx`; `Commit`, `Rollback` (and `DB.Update`/`View`'s callbacks' return) take it back whole.
  Separate from `boltTx` so that a write transaction's `Put`/`Delete` (all of `boltTx`) may run while
  bytes it returned are read (the backend's compaction deletes the very keys its range returned,
  holding them: `kvstore_compaction.go:58-71`).
* **`fileHolds path D`** (exclusive, timeless): **the file at `path` holds a database with the
  data `D`, all of it durable, its name too** (verify-round A11 F1: a path with no file, or an
  empty file whose name may not be durable, is not a `fileHolds`: a generation starts from it by
  `boltFresh_alloc`, with `BoltSt.fresh`), in the generation's OsFs terms (`osMeta`, `osBytes`,
  every byte clean, `lo = hi`, `named`; or an empty file with nothing past it (`hi = 0`), or one
  `init` redoes: then `D = Data.empty`), well-formed
  as the old `fileHolds`' docstring lists (valid metas recording page size 4096, the current at page
  `txid % 2`, the tree's pages within the high-water mark, disjoint, sorted, exact branch keys, no
  empty non-root page, leaves at one depth, an inline bucket's page a leaf within its value, entries
  within `bboltEntryMax`, keys within `maxKeySize` (`Ent.wf`), a synced freelist page well-formed, the
  txid at least 1 and below the receipts' bound). What a generation starts from: `fileHolds_new`
  (an empty file whose name is durable), `fileHolds_image` (a snapshot file), and the crash law's
  conclusion; or, for no file, `boltFresh_alloc`. A closed
  database's file comes back out of `boltFile γ` by `boltRelease` (to rename, remove or reopen it:
  etcd's defrag).
* **`optsAt l dq o`**: the `Options` at `l` (an axiomatized type) has the fields `o`.

## Contracts (opaque, the client's to establish)

* `boltLogger l` (transparent, the old D20′): nil, or a pointer-typed logger whose `Debugf`,
  `Errorf`, `Infof`, `Warningf` return for any format and arguments of the kinds bbolt passes
  (`logArgOk`: basic values, errors whose `Error()` returns, byte slices readable now), reading
  only them. A `*zapBoltLogger` meets it from zap's `Sugar` specs (4a). `boltLogger_nil`.
* `openFileOk f path R` (transparent, **one-shot**: `Open` calls `f` once): the `OpenFile` option
  `f` called with `(path, flag, mode)` returns an `*os.File` (`osFileOf`, provisional: the `os`
  package's representation, `req/os.md`) over an fd of `path`'s OsFs file, read-write, with a way
  back to the caller's `R` from the file's handle, or an error and `R`; `Open`'s error gives `R`
  back (bbolt has closed the file: etcd then closes it again and removes it). etcd's defrag closure
  returning the file it created meets it from that file, once (`ReqDefrag`; verify-round A11 F4,
  was persistent, which a closure returning one exclusive file cannot meet).
* `writerOk w W` (transparent): an `io.Writer` `w` whose `Write` appends a prefix of its argument
  to the stream `W` (the client's predicate of what was written), all unless it fails; with
  `writerPlain` (transparent): its dynamic type has no `ReadFrom` (else `io.CopyN` calls that).
* `boltImage bs D` (an opaque pure fact): `bs` is a bbolt file image holding `D`, which `Open`
  reads as `D` (realized with batch 4d's decoders: `BboltCommon.metaOf`, `pageItems`, ...);
  `boltImage_wf`.
* `putLoan tx γ v dv vb` (exclusive): the value slice `v` lent to a write transaction's `Put` (Go:
  "the value must remain valid for the life of the transaction"), given back once the transaction
  is done (`putLoan_done`).
* `txSize tx n` (persistent): `tx.Size()` is `n` (below `2 ^ 48`) and `tx.WriteTo` writes `n` bytes
  (`boltTx_size`: its existence and its agreement).
* `dbBroken γ` (persistent): a `Begin` failed because a commit lost the mapping; then the client's
  state says so (`dbBroken_state`: `σ.broken`).

## Laws

Persistence, timelessness, fractions, agreement, validity, exclusivity of each predicate
(`boltOpened_closed`); `boltTx_later`, `boltTx_nonnull`, `boltTx_base`, `bktH_live`,
`txBytes_acc`, `txLive_frac`, `boltTx_fill`; well-formedness (`boltTx_wf`, for views and the committed data; `boltImage_wf`); the
size (`boltTx_size`, with `txSize`'s agreement); `putLoan_done`; `dbBroken_state`; `statSlot_wtx`
(a write transaction pays for `Stats`); the updates a holder of `boltState γ 1 σ` can supply
(`boltState_read_au`, `boltState_commit_au`: a commit's two updates, the settling one given at the
commit's, `commitAU`; `boltState_settle_au`, any update, a sync's); the file laws
(`fileHolds_new`, `fileHolds_image`, `fileHolds_alloc`, `boltFresh_alloc`, `boltRelease`) and **the crash law**
(`boltCrash`). The error values (`errIs`, `isErr`; laws `errIs_init`,
`errIs_distinct`) are `bbolt/errors`' (`Spec/go_etcd_io/bbolt/errors/Api.lean`, re-exported).

## Requirement snippets (`examples/specreq/bbolt/`)

`ReqBackendBatch` (the backend's batch: `Begin(true)`, `CreateBucketIfNotExists`, `Bucket`,
`FillPercent`, `Put`, `Delete`, a range by `Seek`/`Next`, `Commit`, `Stats`), `ReqBackendRead` (the
read transaction: `Begin(false)`, `Bucket`, `Cursor`, `Rollback`, `Size`, `DB().Info()`),
`ReqDeleteBucketNotFound`, `ReqHash` (`View`, root cursor, `ForEach`), `ReqSnapshot` (`WriteTo`),
`ReqDefrag` (two databases, custom `OpenFile` and its error path, `NoSync`, `Sync`, `Close`, the
file released by `boltRelease`, renamed and reopened), `ReqDeleteReturned` (a write transaction
deletes the keys its own range returned: `txLive`), `ReqBank` (crash
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
public import Spec.go_etcd_io.bbolt.errors.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Bbolt

open Iris Iris.BI go_etcd_io.bbolt

/- The error values (`errIs`, `isErr`, `bboltErrNames`; laws `BboltErrors.errIs_init`,
`BboltErrors.errIs_distinct`) live in `bbolt/errors`' own API (`Spec/go_etcd_io/bbolt/errors/Api.lean`),
which `internal/common`'s `Meta.Validate` uses too; re-exported here. -/
export BboltErrors (errIs isErr bboltErrNames)

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

/-- **A share `p` of `tx`'s liveness** (fractional; see the header). -/
opaque txLive [HasExt osFsExt] [hG : HeapGS HasLC.hasLC GF] (tx : Loc) (p : Qp) : IProp GF :=
  iprop(True)

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

/-- `bs` is a bbolt file image holding `D` (see the header). -/
opaque boltImage (bs : List w8) (D : Data) : Prop

/-- (provisional, the `os` package's) `f` is an `*os.File` over the fd `fd` (`TrustedCode/os.lean`'s
`File`/`file`: its `fd` and name), exclusive, as `os.OpenFile` returns it. -/
opaque osFileOf [HasExt osFsExt] [hG : HeapGS HasLC.hasLC GF] (f : Loc) (fd : w64) : IProp GF :=
  iprop(True)

/-- The value slice `v` lent to `tx`'s `Put`, back once `tx` is done (exclusive). -/
opaque putLoan [HasExt osFsExt] [hG : HeapGS HasLC.hasLC GF] (tx : Loc) (γ : BoltName) (v : GoSlice)
    (dv : DFrac) (vb : GoString) : IProp GF := iprop(True)

/-- `tx.Size()` is `n`, the length of its `WriteTo` image (persistent). -/
opaque txSize [HasExt osFsExt] [hG : HeapGS HasLC.hasLC GF] (tx : Loc) (n : w64) : IProp GF :=
  iprop(True)

/-- A `Begin` on a database of `γ` failed because a commit lost the mapping (persistent). -/
opaque dbBroken [HasExt osFsExt] [hG : HeapGS HasLC.hasLC GF] (γ : BoltName) : IProp GF :=
  iprop(True)

end vocab

section plain
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

/-- The dynamic type of `wi` has no `ReadFrom` method (`io.CopyN` would call it). -/
def writerPlain (wi : GoInterfaceOk) : Prop := methodSet wi.ty !! go!"ReadFrom" = none

end plain

section contracts
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The logger methods bbolt calls (`lg.Debugf`, `Errorf`, `Infof`, `Warningf`). -/
def boltLogMethods : List GoString := [go!"Debugf", go!"Errorf", go!"Infof", go!"Warningf"]

/-- **An argument bbolt passes to its logger**, under the caller's resource `R`: nil, a basic value
(`fmt.ArgWf`: numbers, strings), an error whose `Error()` returns (reading under `R`), or a byte
slice readable under `R`. -/
def logArgOk (R : IProp GF) : GoInterface → IProp GF
  | .nil => iprop(True)
  | .ok ii => iprop(⌜_root_.Perennial.fmt.ArgWf ii⌝ ∨
      (□ ∀ Φ : val → IProp GF, R -∗ ▷ (∀ e : GoString, R -∗ Φ #e) -∗
        WP (App (Val #(methods ii.ty go!"Error" ii.v)) (Val #())) {{ Φ }}) ∨
      (∃ (sl : GoSlice) (b : GoString),
        ⌜ii.ty = go.GoType.SliceType go.byte ∧ ii.v = #sl⌝ ∗
        □ (R -∗ ∃ dq : DFrac, sl ↦*{dq} b ∗ (sl ↦*{dq} b -∗ R))))

/-- **The logger contract** (the old D20′, restated): nil, or a pointer-typed logger whose four
printf methods return for any format and arguments of `logArgOk`, reading only them. -/
def boltLogger (l : GoInterface) : IProp GF :=
  iprop(⌜l = GoInterface.nil⌝ ∨
    ∃ li : GoInterfaceOk, ⌜l = interface.ok li ∧ loggerPtrOk l⌝ ∗
      □ ∀ (m fmtS : GoString) (args : GoSlice) (xs : List GoInterface) (dq : DFrac) (R : IProp GF)
          (Φ : val → IProp GF),
        ⌜m ∈ boltLogMethods⌝ -∗ args ↦*{dq} xs -∗ ([∗list] x ∈ xs, logArgOk R x) -∗ R -∗
        ▷ (args ↦*{dq} xs -∗ R -∗ Φ #()) -∗
        WP (App (App (Val #(methods li.ty m li.v)) (Val #fmtS)) (Val #args)) {{ Φ }})

/-- **The `OpenFile` contract for `path`** (one-shot: `Open` calls `f` once, `db.go:243`):
`f(path, flag, mode)` returns an `*os.File` over a read-write fd of `path`'s OsFs file, with a
wand from its handle back to the caller's `R` (what `Open`'s error returns once bbolt has closed
the file), or an error and `R`. -/
def openFileOk [HasExt osFsExt] (f : GoFunc) (path : GoString) (R : IProp GF) : IProp GF :=
  iprop(∀ (flag : w64) (mode : w32) (Φ : val → IProp GF),
    ▷ (∀ (fl : Loc) (err : GoInterface),
        ((⌜err = GoInterface.nil⌝ ∗ ∃ fd : w64, osFileOf fl fd ∗
           osFd fd (DFrac.own 1) ⟨path, true, true⟩ ∗ (osFileOf fl fd -∗ R)) ∨
         (⌜err ≠ GoInterface.nil⌝ ∗ R)) -∗
        Φ (PairV #fl #err)) -∗
    WP (App (App (App (Val #f) (Val #path)) (Val #flag)) (Val #mode)) {{ Φ }})

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
`threadTok` (`none`), or the whole of a transaction (`some (tx, T)`): a read transaction's reader
slot covers `statlock` too (the reader pool lends a pair per token); a write transaction's holder
holds `rwlock`, so it is the only writer, and `isBolt` keeps one spare `statlock` reader slot for
it (as one spare `mmaplock` slot for its `freepages`; verify-round A11-completeness F4: the
backend's `begin(true)` calls `db.Stats()` holding only its write transaction,
`backend.go:1086-1098`). -/
def statSlot [HasExt osFsExt] [hG : HeapGS HasLC.hasLC GF] (γ : BoltName) :
    Option (Loc × TxView) → IProp GF
  | none => threadTok
  | some (tx, T) => boltTx tx γ 1 T

/-- **A commit's updates** (what `Tx.Commit` and `DB.Update`'s callback take), nested: the
**commit update** (at the meta page write: `ok`, committed; else attempted, the data unchanged;
bbolt shows the data was `B` when it began) whose commit **gives the settling update** (when the
commit ends: `synced`, the meta page synced; `failed`, a sync failed; `brk`, the mapping was lost),
which commits to the client's `S ok synced failed brk`. bbolt fires the commit update first on
every path, so a holder of the whole state builds both from its one copy
(`boltState_commit_au`), an invariant holder from its invariant (verify-round A11 F5: two
independent updates each needed the state up front, which a holder of one copy cannot give). -/
def commitAU [HasExt osFsExt] [hG : HeapGS HasLC.hasLC GF] (γ : BoltName) (B D : Data) (ns : Bool)
    (S : Bool → Bool → Bool → Bool → IProp GF) : IProp GF :=
  iprop(AU <{ ∃∃ (σ : BoltSt), boltState γ 1 σ }> @ ⊤ \ ↑γ.ns, ∅
    <{ ∀∀ (ok : Bool), ⌜σ.data = B⌝ ∗
       boltState γ 1 (if ok then σ.commit D ns else σ.attempt D ns),
       COMM (AU <{ ∃∃ (σ' : BoltSt), boltState γ 1 σ' }> @ ⊤ \ ↑γ.ns, ∅
         <{ ∀∀ (synced failed brk : Bool), boltState γ 1 (σ'.settle synced failed brk),
            COMM S ok synced failed brk }>) }>)

end vocab2

/-! ## Laws -/

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The persistent predicates. -/
def persistent.spec [HasExt osFsExt] : Prop :=
  (∀ γ, Persistent (boltFile (GF := GF) γ)) ∧
  (∀ db γ ns, Persistent (isBolt (GF := GF) db γ ns)) ∧
  (∀ tx, Persistent (txDone (GF := GF) tx)) ∧
  (∀ tx db, Persistent (txDB (GF := GF) tx db)) ∧
  (∀ db, Persistent (dbClosed (GF := GF) db)) ∧
  (∀ tx γ b p gs, Persistent (bktH (GF := GF) tx γ b p gs)) ∧
  (∀ tx γ s b, Persistent (txBytes (GF := GF) tx γ s b)) ∧
  (∀ tx n, Persistent (txSize (GF := GF) tx n)) ∧
  (∀ γ, Persistent (dbBroken (GF := GF) γ))

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
  (∀ path D D', fileHolds (GF := GF) path D ∗ fileHolds path D' ⊢ False) ∧
  (∀ tx γ v dv vb, putLoan (GF := GF) tx γ v dv vb ∗ putLoan tx γ v dv vb ⊢ False)

/-- **The close right excludes a close** (`boltOpened` is held until the right's `Close`). -/
def boltOpened_closed.spec [HasExt osFsExt] : Prop :=
  ∀ db γ, boltOpened (GF := GF) db γ ∗ dbClosed db ⊢ False

/-- **Every state is well-formed** (sorted keys, recursively): a transaction's views and the
committed data. -/
def boltTx_wf.spec [HasExt osFsExt] : Prop :=
  (∀ tx γ q T, boltTx (GF := GF) tx γ q T ⊢ ⌜T.cur.wf ∧ T.base.wf⌝) ∧
  (∀ γ q σ, boltState (GF := GF) γ q σ ⊢ ⌜σ.data.wf⌝)

/-- An image holds a well-formed database. -/
def boltImage_wf.spec : Prop := ∀ bs D, boltImage bs D → D.wf

/-- **A transaction's size** (`Size()`, `WriteTo`'s length), below `2 ^ 48`, fixed for its life. -/
def boltTx_size.spec [HasExt osFsExt] : Prop :=
  (∀ tx γ q T, boltTx (GF := GF) tx γ q T ⊢ ∃ n : w64, txSize tx n ∗ ⌜uint.nat n < 2 ^ 48⌝) ∧
  (∀ tx n m, txSize (GF := GF) tx n ∗ txSize tx m ⊢ ⌜n = m⌝)

/-- **A `Put`'s value comes back once the transaction is done** (committed or rolled back). -/
def putLoan_done.spec [HasExt osFsExt] : Prop :=
  ∀ (E : CoPset) tx γ v dv vb, ↑γ.ns ⊆ E →
    txDone (GF := GF) tx ∗ putLoan tx γ v dv vb ⊢ |={E}=> v ↦*{dv} vb

/-- **A broken database is one whose client state says so.** -/
def dbBroken_state.spec [HasExt osFsExt] : Prop :=
  ∀ γ q σ, dbBroken (GF := GF) γ ∗ boltState γ q σ ⊢ ⌜σ.broken = true⌝

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

/-- A slice the transaction returned is read while the transaction is live (any share of its
liveness: the transaction's view, `boltTx`, is not needed, so it may be written meanwhile). -/
def txBytes_acc.spec [HasExt osFsExt] : Prop :=
  ∀ tx γ p s b, txBytes (GF := GF) tx γ s b ∗ txLive tx p ⊢
    ∃ dq : DFrac, s ↦*{dq} b ∗ (s ↦*{dq} b -∗ txLive tx p)

/-- The liveness is fractional (several reads' bytes out at once). -/
def txLive_frac.spec [HasExt osFsExt] : Prop :=
  ∀ tx, Fractional (fun p => txLive (GF := GF) tx p)

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

/-- **A holder of the whole state supplies a commit's updates** (`commitAU`, both from its one
copy: the settling update is built, at the commit update's commit, from the state that update
gives back), ending with the whole state settled: `σ` committed (`ok`) or attempted, then settled;
and the data was `B` (verify-round A11 F5: was the commit update alone, whose state a second law
for the settling update could not also consume). -/
def boltState_commit_au.spec [HasExt osFsExt] : Prop :=
  ∀ γ σ B D ns, boltState (GF := GF) γ 1 σ ⊢
    commitAU γ B D ns (fun ok synced failed brk => iprop(⌜σ.data = B⌝ ∗
      boltState γ 1 ((if ok then σ.commit D ns else σ.attempt D ns).settle synced failed brk)))

/-- **A write transaction pays for `DB.Stats`** (`statSlot`'s `some` case is any transaction's
whole; listed for the backend's `begin(true)`, `backend.go:1086-1098`, verify-round A11-completeness
F4: the realization's spare `statlock` reader slot in `isBolt`, used only by the writer, which
holds `rwlock`). -/
def statSlot_wtx.spec [HasExt osFsExt] : Prop :=
  ∀ tx γ T, T.rw = true → (boltTx (GF := GF) tx γ 1 T ⊣⊢ statSlot γ (some (tx, T)))

/-- **A holder of the whole state supplies any update of it** (a sync's, `DB.Sync`; a settling
update built apart). -/
def boltState_settle_au.spec [HasExt osFsExt] : Prop :=
  ∀ γ σ, boltState (GF := GF) γ 1 σ ⊢
    AU <{ ∃∃ (σ' : BoltSt), boltState γ 1 σ' }> @ ⊤ \ ↑γ.ns, ∅
      <{ ∀∀ (σ'' : BoltSt), boltState γ 1 σ'', COMM ⌜σ' = σ⌝ ∗ boltState γ 1 σ'' }>

/-- **An empty file whose name is durable holds the empty database**: no mapping, nothing past
its end a crash could bring back (`hi = 0`: no un-synced truncation; verify-round A11 F3, true of
every empty file OsFs's specs make: `newMeta`, a boot file's `initMeta`), its name durable
(`named`: a boot file, or one whose creator synced its directory; A11 F1). A path with no file,
or an empty file whose name may not be durable: `boltFresh_alloc`. -/
def fileHolds_new.spec [HasExt osFsExt] : Prop :=
  ∀ (path : GoString) (m : OsMeta),
    osMeta (GF := GF) path (DFrac.own 1) (some m) ∗
      ⌜m.size = 0 ∧ m.hi = 0 ∧ m.maps = ∅ ∧ m.named = true⌝ ∗
      osBytes (GF := GF) path 0 (DFrac.own 1) []
    ⊢ fileHolds path Data.empty

/-- **Allocating a database's names over a path bbolt will create the file at** (no file; or an
empty one, named or not, with nothing past its end; etcd's first boot, `member/snap/db`, and
defrag's `os.CreateTemp` file): as `fileHolds_alloc`, with the state `BoltSt.fresh` (empty, its
name not durable: bbolt never syncs the directory, so a crash may leave no file;
`nonissues/bbolt-create-dir-not-synced.md`; verify-round A11 F1, a user decision). -/
def boltFresh_alloc.spec [HasExt osFsExt] : Prop :=
  ∀ (E : CoPset) (N : Namespace) (path : GoString) (mo : Option OsMeta), ↑N ## ↑osN →
    osMeta (GF := GF) path (DFrac.own 1) mo ∗
      (match mo with
       | none => iprop(emp)
       | some m => iprop(⌜m.size = 0 ∧ m.hi = 0 ∧ m.maps = ∅⌝ ∗
           osBytes (GF := GF) path 0 (DFrac.own 1) []))
    ⊢ |={E}=> ∃ γ : BoltName, ⌜γ.ns = N ∧ γ.path = path⌝ ∗
      boltFile γ ∗ boltClosed γ ∗ boltState γ 1 BoltSt.fresh

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

/-- **A closed database's file comes back out of its crash invariant** (verify-round
A11-completeness F3: etcd's defrag renames the synced copy over the database, removes it on a
failure, `backend.go:553-606`): with the closed token and the whole state, the file's OsFs
resources at their whole fractions (no mapping: it is closed); when the state promises only its
data (`dur = some []`, no commit in flight) and the data is not empty, the file's bytes are all
clean and durable to its size and form an image of that data (`fileHolds_image`'s premise but for
the name; its name durable as `σ.named` says). No file only if the data is empty (never opened in
this generation, from `boltFresh_alloc`). Realization: `boltFile γ` is a cancelable invariant whose
token is split between `boltClosed γ` and the invariant's half of `σ`. -/
def boltRelease.spec [HasExt osFsExt] : Prop :=
  ∀ (E : CoPset) (γ : BoltName) (σ : BoltSt), ↑γ.ns ⊆ E →
    boltFile (GF := GF) γ ∗ boltClosed γ ∗ boltState γ 1 σ ⊢ |={E}=>
      ∃ mo : Option OsMeta, osMeta (GF := GF) γ.path (DFrac.own 1) mo ∗
        (match mo with
         | none => iprop(⌜σ.data = Data.empty⌝)
         | some m => iprop(∃ xs : List (w8 × Bool),
             osBytes (GF := GF) γ.path 0 (DFrac.own 1) xs ∗
             ⌜m.size = xs.length ∧ m.maps = ∅ ∧ (σ.named = true → m.named = true) ∧
               (σ.dur = some [] → σ.busy = false → σ.data ≠ Data.empty →
                 boltImage (xs.map Prod.fst) σ.data ∧ (∀ x ∈ xs, x.2 = true) ∧
                 m.lo = xs.length ∧ m.hi = xs.length)⌝))

/-- **The crash law.** After the generation crashes (its `crashed`), from the file's crash
invariant and any fraction of the state `σ` (a crash-safe client keeps one in an invariant, which
survives the crash), the next generation `L'` gets the file holding a state `σ` says a crash may
recover, out of the extension's restart resources (`crashRest`, the files not yet taken `Ps`).
Nothing is promised when `σ.dur = none` (a `NoSync` commit not synced). While the file's name is
not durable (`σ.named = false`, a generation that created it), the file may be gone (OsFs's D4;
verify-round A11 F1): then `D` is empty (`σ.recovers` admits it) and the next generation gets the
path with no file, from which `boltFresh_alloc` starts it again. True only with the sector
rule of decision 4c-D1 (open), including its clause for sectors past the durable size; this is
its statement under option (a); under (b) it is stated over `crashRestQ` instead (see the header,
A11 F10). -/
def boltCrash.spec [HasExt osFsExt] : Prop :=
  ∀ (L' : GooseLocalGS GF) (γ : BoltName) (q : Qp) (σ : BoltSt) (ds : List Data)
    (Ps : List GoString),
    σ.dur = some ds → γ.path ∉ Ps →
    boltFile (GF := GF) γ ∗ boltState γ q σ ∗ crashed ∗
      crashRest (gooseOsGS (L := hG.goose_localGS)) (gooseOsGS (L := L')) Ps ⊢
    |={⊤}=> ∃ D : Data, ⌜σ.recovers D⌝ ∗
      (@fileHolds _ _ _ GF _ ⟨hG.goose_globalGS, L'⟩ γ.path D ∨
       (⌜σ.named = false ∧ D = Data.empty⌝ ∗
         osMeta (GF := GF) (L := L') γ.path (DFrac.own 1) none)) ∗
      crashRest (gooseOsGS (L := hG.goose_localGS)) (gooseOsGS (L := L')) (γ.path :: Ps)

/-- The nil logger meets the contract (`Open` replaces it by the discard logger). -/
def boltLogger_nil.spec : Prop :=
  ⊢ boltLogger (GF := GF) GoInterface.nil

end laws

end Bbolt
end EtcdGrove
end Perennial
