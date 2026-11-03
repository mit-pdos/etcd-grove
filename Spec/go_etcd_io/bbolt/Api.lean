/-
# bbolt's API module (the frozen spec of 2026-11-03)

What a proof outside bbolt may use of bbolt: this module, the pure data (`Data.lean`), the
logger contract (`Logger.lean`), the options (`Options.lean`) and the one-function spec files
`Spec/go_etcd_io/bbolt/<T>__<M>.lean` (`etc/api/bbolt.txt`). The design, the decisions (D1-D22)
and who took them: `notes/bbolt-spec-decisions.md`; `notes/decisions.md`, "bbolt's API spec".

**The predicates** (`isBolt`, `boltState`, `boltTx`, `txDB`, `txDone`, `boltBkt`, `boltCur`,
`txBytes`, `fileHolds`) are sealed: each is a `@[no_expose]` definition over a non-public import
of `Proof/go_etcd_io/bbolt/Inv/` (U0a, `notes/bbolt-proof-plan.md`: `isBolt db γ` is
`isBoltDef (bnsOf γ.gs) γ.ns db`, and so on), with the statements they had as `opaque`s (their
ambient instance arguments now include the heap's, which their bodies use). Each takes OsFs's
`[HasExt osFsExt]` in its signature. **The laws** are proved from their `…Def` versions in
`Inv/`, whose `sorry`s are the proof's planned work.
-/
module

public import GeneratedProof.go_etcd_io.bbolt
public import GeneratedProof.go_etcd_io.bbolt.errors
public import Perennial.Proof.ProofPrelude
public import Perennial.ProgramLogic.Bounds
public import Iris.BI.Lib.Atomic
public import GooseLang.Ext.OsFs.Specs
public import Proof.go_etcd_io.bbolt.PkgInit
public import Spec.go_etcd_io.bbolt.Data
import Proof.go_etcd_io.bbolt.Inv.FileHolds

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

/-- bbolt's page size in every file the specs admit (round 10, named once): `OptsM.ok`'s default
page size, `DefaultPageSize`'s package fact (`Proof/go_etcd_io/bbolt/PkgInit.lean`), and the page
size every valid meta records (`fileHolds`). Round 11 (D22): it is also OsFs's `osPageSize`, the
OS page whose aligned writes OsFs's `pwrite` makes all-or-nothing (`boltPageSize_eq_osPageSize`). -/
@[word_unfold] def boltPageSize : Nat := 4096

/-- bbolt's page is the OS page (D22): a meta write, one `boltPageSize` buffer at offset
`id · boltPageSize`, is a write within one aligned OS page. -/
theorem boltPageSize_eq_osPageSize : boltPageSize = osPageSize := rfl

/-! # The vocabulary (`Spec/go_etcd_io/bbolt/Api.lean`; sealed) -/

/-- **A database's ghost names** (round 4: a structure, no longer `opaque`, so that clients that
store it in their own ghost names derive `Pos.Countable`/`Inhabited`, as mvcc's `InvStore.lean`
(`bNames_countable`) and etcdserver's `InvApplier.lean` do for the backend's `BNames`). What the
names mean is the implementation's, sealed: a client only stores and passes them.
- `gs`: the implementation's ghost names (`Open` allocates them; the list's length and order are
  the implementation's business);
- `ns`: the namespace the client chose at `Open` (round 2: in place of a fixed `boltN`). bbolt's
  invariants live in it, and the masks of its atomic updates are `⊤ \ ↑γ.ns`. `Open`'s post says
  `γ.ns = N`. -/
structure BoltName where
  gs : List GName
  ns : Namespace
  deriving Inhabited, DecidableEq

/-- Countable through its fields (`List GName` and `Namespace = List Pos` both are), as mvcc's
`dbNames_countable` does for the old `DBNames`. -/
instance boltName_countable : Pos.Countable BoltName :=
  countableOfLeftInverse (fun x : BoltName => (x.gs, x.ns)) (fun p => ⟨p.1, p.2⟩) (fun _ => rfl)

section vocab
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
/- The vocabulary is over OsFs's semantics (round 11: the default `osFs_semantics`, D22): each
predicate takes the instance in its signature (round 10), and the laws, which use the
predicates, take this section variable. -/
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **`db` is the database `γ`** (persistent): open, or closed by a `Close` (after which `Begin`
fails). It carries bbolt's package initialization and its invariants: the locks, the memory map,
the file, the freelist, the readers' pool of `mmaplock` reader slots (the owner's protocol of
`notes/bounds-plan.md`: each slot is lent for a `threadTok`; one spare slot kept in `rwlock`'s
resource for the writer's `freepages`, see `Open.spec`), the commit counter backed by time
receipts, and the authority of the committed data.
It also owns **`DB`'s exported fields** (`StrictMode`, `NoSync`, `NoGrowSync`, `NoFreelistSync`,
`MmapFlags`, `MaxBatchSize`, `MaxBatchDelay`, `AllocSize`, `MaxSize`, `Mlock`, ...): a client
must not write them after `Open` (Go lets it; the specs do not, since no client holds their
points-to). `StrictMode = true` alone would change `Commit` (it runs `tx.Check()`: goroutines,
read transactions, a panic on any report). etcd writes none of them. -/
@[no_expose] def isBolt [HasExt osFsExt] (db : Loc) (γ : BoltName) : IProp GF :=
  isBoltDef (bnsOf γ.gs) γ.ns db

/-- **The committed data of `γ` is `D`**, at fraction `q`: the client's view, which the
atomic updates of `Begin(false)` and `Commit` act on (fractional: a read needs some fraction, a
commit all of it). Survives `Close` (the data then stays `D`). -/
@[no_expose] def boltState [HasExt osFsExt] (γ : BoltName) (q : Qp) (D : Data) : IProp GF :=
  boltStateDef (bnsOf γ.gs) q D

/-- **`tx` is a transaction of `γ`, live, with the view `T`**, at fraction `q`. A read
transaction's whole (`q = 1`) holds the reader slot `Begin(false)` took for the caller's
`threadTok` (given back by `Rollback`); its fractions may be shared between goroutines for
reads. A write transaction's operations that change it need all of it. -/
@[no_expose] def boltTx [HasExt osFsExt] (tx : Loc) (γ : BoltName) (q : Qp) (T : TxView) : IProp GF :=
  boltTxDef (bnsOf γ.gs) γ.ns tx q T

-- Round 6: `txSnap` (and `boltTx_snap`, `txSnap_agree`) dropped (review 5, finding 5): with no
-- name it needs a registry keyed by `tx`, which D19 rejected, and no caller needs it (the backend
-- keeps `boltTx tx γ q (ro D)` where it kept `rtxSnap tx D`).

/-- `tx` is a transaction of the database `db` (persistent; what `Tx.DB` returns). -/
@[no_expose] def txDB [HasExt osFsExt] (tx db : Loc) : IProp GF :=
  txDBDef tx db

/-- `tx` was committed or rolled back (persistent): its statistics can be read. -/
@[no_expose] def txDone [HasExt osFsExt] (tx : Loc) : IProp GF :=
  txDoneDef tx

/-- `b` is `tx`'s handle of the bucket named `n` at generation `g` (persistent). Its operations
need `n` at generation `g` in the transaction's view: a deleted bucket's handle is never current
again (a re-created bucket of the name gets a new generation). -/
@[no_expose] def boltBkt [HasExt osFsExt] (tx : Loc) (γ : BoltName) (b : Loc) (n : GoString) (g : Nat) : IProp GF :=
  boltBktDef (bnsOf γ.gs) tx b n g

/-- `c` is a cursor of `tx`, made at the view `T`, over the entries `es`, at position `pos`
(`none`: not positioned; `some i`, `i ≤ es.length`: at the `i`-th entry, or past the last at
`es.length`, see `Cursor.Next.spec`). Exclusive. Its moves need `tx` at the view `T`: after a
change of the transaction, a cursor made before it is not usable (Go: "You must reposition your
cursor after mutating data"; the spec does not let it be repositioned). -/
@[no_expose] def boltCur [HasExt osFsExt] (tx : Loc) (γ : BoltName) (c : Loc) (T : TxView) (es : List BoltEnt) (pos : Option Nat) : IProp GF :=
  boltCurDef (bnsOf γ.gs) tx c T es pos

/-- The slice `s` holds `b` while `tx` is live (persistent; read with `txBytes_acc`): a key or
value bbolt returned, pointing into the memory map (unmapped by a remap or `Close`, which wait
for the transaction) or into the transaction's nodes. -/
@[no_expose] def txBytes [HasExt osFsExt] (tx : Loc) (γ : BoltName) (s : GoSlice) (b : GoString) : IProp GF :=
  txBytesDef (bnsOf γ.gs) tx s b

/-- **The file at `path` holds a database with the data `D`** (exclusive): what `Open` reads.
Defined over the Linux file extension (`GooseLang/Ext/OsFs`: the file's whole `osMeta`, with no
mapping, and its `osBytes`; round 2: *not* "every byte synced": the in-process specs read the
page cache, and durability is out of scope), and either
- **fresh**: no file, or an empty one (`Open` runs `init`), and then `D = ∅` (`fileHolds_new`);
- or **well-formed**: a bbolt file whose **every valid meta records page size `4096`**
  (`DefaultPageSize`; round 8: D18's `getPageSize` takes page 0's size whenever page 0 is valid,
  current or not); its metas
  (round 4, in place of "two valid metas", which a failed commit's torn meta write breaks):
  **at least one valid meta**, the current one the valid meta whose txid is **strictly higher than
  any other valid meta's** (round 7: an equal pair makes `meta()` pick page 0 whatever the parity),
  **lying at page `txid % 2`** (round 6: a commit writes its meta at page `txid % 2`, so the next commit
  writes the *other* page and a torn write there leaves the current meta valid; without it, the
  next commit may overwrite the only valid meta and a torn write makes `db.meta()` panic, in
  `rollback` and in a concurrent `Begin`), and no other valid meta in page 0 at the offsets
  `getPageSize` reads there (1024, 2048: zero in every file bbolt writes). With D18's fork change (decided: `getPageSize` returns a meta read error, and
  probes past page 1 only after successful reads with a bad checksum, i.e. both metas invalid),
  nothing about user values is assumed. Its tree holding `D`:
  - the root holds top-level buckets only (no nested bucket, no plain value); every key
    non-empty; every entry within `bboltEntryMax`;
  - (round 4: over *extents*) every tree page's extent (`id` through `id + overflow`) and the
    synced freelist page's extent lie in `[2, hwm)` (so within the file, by the high-water-mark
    clause below: a mapped load past the end of the file is a hole in OsFs, stuck); the extents
    are pairwise disjoint
    (no page shared: `freepages`' check reports "multiple references" on any overlap) and
    disjoint from the synced freelist's ids (`Free` panics on an id already free); every tree
    page is of leaf or branch type;
  - (round 8) **every tree page's header id is its page number** (the first page of its extent:
    `tx.page`'s `FastCheck` panics otherwise, in every read), and **an inline bucket's page has
    header id 0** (`node.read` takes `n.pgid` from it, and `spill` frees `tx.page(n.pgid)` when it
    is non-zero);
  - (round 7) **the high-water mark times the page size is at most the file's length** (free ids,
    synced or computed by `freepages` under `NoFreelistSync`, are bounded by `hwm` only, and
    `allocate` reuses a free page without remapping: one past the mapping would be read out of
    bounds by the next reader. Maintained (round 8 wording): `tx.write` writes every allocated
    extent whole, `(overflow + 1) · pageSize` bytes, and the last one ends at the new mark, so
    the file reaches it even under `NoGrowSync` (where `grow` does not truncate); a failed commit
    keeps the old mark; `WriteTo`'s images are `hwm · pageSize` long);
  - (round 6) **the synced freelist page** (if the meta has one) is of freelist type, its count
    and ids lie within its own extent, and its ids are distinct and in `[2, hwm)` (`Read` panics
    on another page type; `Allocate` panics on ids 0 and 1; an id at or past the high-water mark
    or a duplicate is handed out wrongly, twice, or as a root above the mark);
  - keys strictly sorted within and across the pages of each tree, and (round 3) **each branch
    element's key exactly its child page's first key** (`spill`'s `parent.put` and
    `rebalance`'s `parent.del` match keys exactly: an inexact one inserts a stale element or
    misses it);
  - **no empty non-root page** (round 2: else `Prev` and `Last` misread or hang,
    `issues/bbolt-cursor-prev-empty-leaf.md`), and (round 3) **every branch page with at least two
    elements** (`rebalance` asserts `parent.numChildren() > 1`);
  - (D-E, the coordinator after the invariant design) **every leaf at the same depth**
    (`rebalance` merges a node with a sibling without checking that both are leaves or both
    branches; bbolt's own writes keep it: `spill` splits a node into siblings of its kind, and
    `rebalance` collapses only the root);
  - (round 6, replacing round 3's clause) **every page's element headers and key/value bytes lie
    within the page's own extent** (`(overflow + 1) * pageSize` bytes from its start), and end
    below `MaxAllocSize` from the page start (bbolt never bounds-checks them: bytes read through
    another page's extent would change when that page is freed and reused, with no commit of
    these entries; with 4096-byte pages and elements of at least 17 bytes this also bounds the
    count far below `node.write`'s `0xFFFF`);
  - an inline bucket's value longer than its header, its page (inside the value) a **leaf** page
    whose elements and bytes lie **within the value** (round 6; `pageNode` panics on a non-leaf
    inline page);
  - its txid below `2 ^ 62` (round 3: the invariant `Commit` keeps is `txid < t₀ + receipts <
    2 ^ 63`, with `t₀ < 2 ^ 62` the opened file's: what "no wrap" needs).
  (Round 1's clause "no user value holds a valid meta at a probed offset" is gone: D18's fork
  change makes it unnecessary, and no `Commit` could keep it, since `Put` takes arbitrary bytes.
  The one valid meta this list requires stops the probe at page 0 or page 1.)
**Maintenance** (round 3; `notes/bbolt-spec-decisions.md`, "fileHolds is kept by Commit"): `spill` rewrites the
parent key of every child it writes, and every ancestor of a changed node is materialized
(exact keys); split pieces have at least `minKeysPerPage = 2` elements, `rebalance` merges a node
below `minKeys` and removes an empty one, and collapses a root branch with one child (two
elements, no empty page): whatever the split threshold. The page bound needs the threshold at
most the page size (`splitThresholdOk`, D17). Extents (round 4): `spill` frees whole extents as
pending and `allocate`s fresh contiguous runs (below the high-water mark, growing it), and every
page it writes reaches the file by `pwrite`; the meta clause: a successful commit writes a valid
meta at page `txid % 2` (the page the current meta is not on), a failed one leaves the *current*
meta valid and current (round 6), since OsFs's `pwrite` of one aligned OS page, which a meta
write is, is all-or-nothing in-process (round 11, D22; until round 10 the named premise P2);
`Tx.WriteTo`'s images place the current meta at page `txid % 2` on the fork (D21, round 7); a written page's elements lie in its own buffer (`node.write`
into a buffer sized by `node.size()`); without `NoFreelistSync` the commit writes free plus
pending ids, each in `[2, hwm)` and unique, into a freelist-type page sized for them, and with it
(etcd) the meta's freelist is `PgidNoFreelist` and the clause is vacuous. With these, the check `freepages` runs in a failed
commit (`recursivelyCheckBucket`, which panics on any report) finds nothing. -/
-- Round 9 folded OsFs's `osInv` into `fileHolds`; the coordinator unfolded it after the
-- invariant design (D-B: `osInv` is an invariant, so `fileHolds` was not timeless, and the fold's
-- reason went with D22 = (b)): `Open` takes `osInv` separately, and `fileHolds` is `osMeta`,
-- `osBytes` and pure facts.
@[no_expose] def fileHolds [HasExt osFsExt] (path : GoString) (D : Data) : IProp GF :=
  fileHoldsDef path D

/-! ## Laws -/

@[instance] theorem isBolt_persistent (db : Loc) (γ : BoltName) :
    Persistent (isBolt (GF := GF) db γ) := by
  unfold isBolt; infer_instance
-- Round 3: round 2's `isBolt_agree`/`boltTx_isBolt` are dropped (review 2, finding 6: a pure
-- entailment between two handles needs a registry `db ↦ γ`, and none can be had: a package fact
-- is a fixed proposition, so a ghost name inside it does not agree between two copies; D-E).
-- The clients carry `γ` instead: the backend already has it (`BNames`' `γ.db`, beside every
-- `isDB db`), so its layer is `isDB db := isBolt db γ.db` (`notes/bbolt-spec-decisions.md`, D19).
@[instance] theorem boltState_timeless (γ : BoltName) (q : Qp) (D : Data) :
    Timeless (boltState (GF := GF) γ q D) := by
  unfold boltState; infer_instance
@[instance] theorem boltState_fractional (γ : BoltName) (D : Data) :
    Fractional (fun q => boltState (GF := GF) γ q D) := by
  unfold boltState; exact boltStateDef_fractional _ _
theorem boltState_agree (γ : BoltName) (q1 q2 : Qp) (D1 D2 : Data) :
    boltState (GF := GF) γ q1 D1 ∗ boltState γ q2 D2 ⊢ ⌜D1 = D2⌝ := by
  unfold boltState; exact boltStateDef_agree _ _ _ _ _
theorem boltState_valid (γ : BoltName) (q : Qp) (D : Data) :
    boltState (GF := GF) γ q D ⊢ ⌜q ≤ 1⌝ := by
  unfold boltState; exact boltStateDef_valid _ _ _

/-- **A later transaction is a transaction, given its database** (decided by the coordinator after
the invariant design, D-A, in place of `boltTx_timeless`: `boltTx` holds the transaction's locks'
and bbolt's invariants, which are not timeless; the timeless rest is stripped, and the invariants
come from `isBolt`). -/
theorem boltTx_later (db tx : Loc) (γ : BoltName) (q : Qp) (T : TxView) :
    isBolt (GF := GF) db γ ⊢ ▷ boltTx tx γ q T -∗ ◇ boltTx tx γ q T := by
  unfold isBolt boltTx; exact boltTxDef_later _ _ _ _ _ _
@[instance] theorem boltTx_fractional (tx : Loc) (γ : BoltName) (T : TxView) :
    Fractional (fun q => boltTx (GF := GF) tx γ q T) := by
  unfold boltTx; exact boltTxDef_fractional _ _ _ _
/-- Two fractions of one transaction of one database agree on its view (round 6: over one name;
across names it needed a registry keyed by `tx`, D19). Provable from `isBolt γ`'s ghost map of
transactions `tx ↪ γtx` and `γtx`'s fractional view. -/
theorem boltTx_agree (tx : Loc) (γ : BoltName) (q1 q2 : Qp) (T1 T2 : TxView) :
    boltTx (GF := GF) tx γ q1 T1 ∗ boltTx tx γ q2 T2 ⊢ ⌜T1 = T2⌝ := by
  unfold boltTx; exact boltTxDef_agree _ _ _ _ _ _ _
theorem boltTx_valid (tx : Loc) (γ : BoltName) (q : Qp) (T : TxView) :
    boltTx (GF := GF) tx γ q T ⊢ ⌜q ≤ 1⌝ := by
  unfold boltTx; exact boltTxDef_valid _ _ _ _ _
/-- A live transaction is a non-nil `*Tx` (the backend's `tx != nil` checks). -/
theorem boltTx_nonnull (tx : Loc) (γ : BoltName) (q : Qp) (T : TxView) :
    boltTx (GF := GF) tx γ q T ⊢ ⌜tx ≠ Loc.null⌝ := by
  unfold boltTx; exact boltTxDef_nonnull _ _ _ _ _
/-- **While a write transaction is live, the committed data is the one it began at** (it holds
`rwlock`; only it can commit). How a client learns the data `Begin(true)` began at. -/
theorem boltTx_base (tx : Loc) (γ : BoltName) (q q' : Qp) (T : TxView) (D : Data) :
    boltTx (GF := GF) tx γ q T ∗ boltState γ q' D ⊢ ⌜T.rw = true → T.base = D⌝ := by
  unfold boltTx boltState; exact boltTxDef_base _ _ _ _ _ _ _

@[instance] theorem txDB_persistent (tx db : Loc) : Persistent (txDB (GF := GF) tx db) := by
  unfold txDB; infer_instance
@[instance] theorem txDone_persistent (tx : Loc) : Persistent (txDone (GF := GF) tx) := by
  unfold txDone; infer_instance
@[instance] theorem boltBkt_persistent (tx : Loc) (γ : BoltName) (b : Loc) (n : GoString)
    (g : Nat) : Persistent (boltBkt (GF := GF) tx γ b n g) := by
  unfold boltBkt; infer_instance
@[instance] theorem txBytes_persistent (tx : Loc) (γ : BoltName) (s : GoSlice) (b : GoString) :
    Persistent (txBytes (GF := GF) tx γ s b) := by
  unfold txBytes; infer_instance
@[instance] theorem boltCur_timeless (tx : Loc) (γ : BoltName) (c : Loc) (T : TxView)
    (es : List BoltEnt) (pos : Option Nat) : Timeless (boltCur (GF := GF) tx γ c T es pos) := by
  unfold boltCur; infer_instance
@[instance] theorem fileHolds_timeless (path : GoString) (D : Data) :
    Timeless (fileHolds (GF := GF) path D) := by
  unfold fileHolds; infer_instance

/-- A slice the transaction returned is read while the transaction is live (any fraction). -/
theorem txBytes_acc (tx : Loc) (γ : BoltName) (q : Qp) (T : TxView) (s : GoSlice) (b : GoString) :
    txBytes (GF := GF) tx γ s b ∗ boltTx tx γ q T ⊢
      ∃ dq : DFrac, s ↦*{dq} b ∗ (s ↦*{dq} b -∗ boltTx tx γ q T) := by
  unfold txBytes boltTx; exact txBytesDef_acc _ _ _ _ _ _ _

/-- **A bucket handle's `FillPercent` field** (exported, written by clients: the backend's
`0.9`), of any handle the transaction gave out, current or not, with the whole transaction: read,
and written back with any value but a NaN (a NaN passes `node.splitTwo`'s clamp and makes
`Commit` panic on a large leaf: `nonissues/bbolt-fillpercent-nan.md`; every other value is
clamped into `[0.1, 1.0]`). The repair of the refuted `backend.ownWTxG_fill`. Round 3: in the
model the premise matters only through `splitThresholdOk` (D17); without the trusted helper no
premise on the field could bound the threshold. For a write transaction only (decided by the
coordinator after the invariant design, D-D: a reader's `Tx.Bucket` runs at any fraction and
allocates a fresh handle each call, which no entailment from `boltTx … 1` can find; the backend
writes `FillPercent` in write transactions only). -/
theorem boltTx_fill (tx b : Loc) (γ : BoltName) (T : TxView) (n : GoString) (g : Nat)
    (hrw : T.rw = true) :
    boltTx (GF := GF) tx γ 1 T ∗ boltBkt tx γ b n g ⊢
      ∃ f : w64, structFieldRef go_etcd_io.bbolt.Bucket go!"FillPercent" b ↦ f ∗
        (∀ f' : w64, ⌜¬ float64IsNaN f'⌝ -∗
          structFieldRef go_etcd_io.bbolt.Bucket go!"FillPercent" b ↦ f' -∗ boltTx tx γ 1 T) := by
  unfold boltTx boltBkt; exact boltTxDef_fill _ _ _ _ _ _ _ hrw

/-- What a cursor move to the `i`-th entry returns: its key (never nil: bbolt's keys are not
empty) and value, valid while `tx` is live; nil and nil past the end. -/
def curAt (tx : Loc) (γ : BoltName) (es : List BoltEnt) (i : Nat) (k v : GoSlice) : IProp GF :=
  match es[i]? with
  | some e => iprop(⌜k ≠ slice.nil⌝ ∗ txBytes tx γ k e.1 ∗ txBytes tx γ v e.2)
  | none => iprop(⌜k = slice.nil ∧ v = slice.nil⌝)

instance curAt_persistent (tx : Loc) (γ : BoltName) (es : List BoltEnt) (i : Nat)
    (k v : GoSlice) : Persistent (curAt (GF := GF) tx γ es i k v) := by
  unfold curAt; split <;> infer_instance

/-- **A client holding the committed data** (all of it, not in an invariant) can supply any read
update over it: the layer the backend's batch lock uses (it holds `boltState γ 1 D`). -/
theorem boltState_read_au (γ : BoltName) (D : Data) :
    boltState (GF := GF) γ 1 D ⊢
      AU <{ ∃∃ (q : Qp) (D' : Data), boltState γ q D' }> @ ⊤ \ ↑γ.ns, ∅
        <{ boltState γ q D', COMM boltState γ 1 D ∗ ⌜D' = D⌝ }> := by
  unfold boltState; exact boltState_read_au' _ _ _

/-- The same for a commit from `D` to `S`. -/
theorem boltState_commit_au (γ : BoltName) (D S : Data) :
    boltState (GF := GF) γ 1 D ⊢
      AU <{ ∃∃ (D' : Data), boltState γ 1 D' }> @ ⊤ \ ↑γ.ns, ∅
        <{ ⌜D' = D⌝ ∗ boltState γ 1 S, COMM boltState γ 1 S }> := by
  unfold boltState; exact boltState_commit_au' _ _ _ _

/-- **bbolt's `Close` succeeds** (opaque, a named premise about the program's environment, moved
from the backend's `InvBbolt.lean`): `db.Close()` does not fail for the environment's reasons
(unmapping the file, unlocking it, closing it). Not used by `DB.Close.spec`, which is proved over
a file model where these system calls may fail; only the trust-boundary layer
`DB.Close_kv` (backend) rests on it. -/
opaque dbCloseOk : Prop

/-- **A fresh file holds the empty database** (round 2; the concurrent test's start, a path in a
fresh directory): no file at `path`, or an empty one with no mapping, in OsFs's terms
(`GooseLang/Ext/OsFs/Specs.lean`). Round 11: stated again, at the default semantics (D22). (D-B,
the coordinator: no `osInv` here, which `fileHolds` no longer holds.) -/
theorem fileHolds_new (path : GoString) (mo : Option OsMeta) :
    osMeta (GF := GF) path (DFrac.own 1) mo ∗
      (match mo with
       | none => iprop(emp)
       | some m => iprop(⌜m.size = 0 ∧ m.maps = ∅⌝ ∗ osBytes (GF := GF) path 0 (DFrac.own 1) []))
    ⊢ fileHolds path ∅ := by
  unfold fileHolds; exact fileHoldsDef_new _ _

end vocab

section stat
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
/- Every bbolt spec is stated over OsFs's semantics (round 11, D22: the default `osFs_semantics`,
whose `pwrite` within one aligned OS page is all-or-nothing): the binder `∀ [HasExt osFsExt]` at
the head of each triple (a section variable is dropped from a definition that does not use it),
and in the signature of each vocabulary predicate, so that every statement carries it (checked
with `#check`). -/
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- What pays for `statlock`'s reader slot in `DB.Stats`: the caller's `threadTok` (`none`), or
the whole of a read transaction (`some (tx, D)`), whose reader slot covers `statlock` too: for a
caller whose token a read transaction holds, as the backend's `begin` right after
`Begin(false)` (`notes/bbolt-spec-decisions.md`, D2). Sound because the implementation's reader pool lends a
*pair* per token, an `mmaplock` reader token and a `statlock` one, so a read transaction's slot
covers its `Stats`; it needs all of the transaction, since two holders of fractions calling
`Stats` at once would need two `statlock` tokens. -/
def statSlot [HasExt osFsExt] (γ : BoltName) : Option (Loc × Data) → IProp GF
  | none => threadTok
  | some (tx, D) => boltTx tx γ 1 (TxView.ro D)

end stat

end bbolt
end EtcdGrove
end Perennial
