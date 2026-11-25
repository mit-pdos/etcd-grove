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
`[ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]` in its signature. **The laws** are proved from their `…Def` versions in
`Inv/`, whose `sorry`s are the proof's planned work.
-/
module

public import GeneratedProof.go_etcd_io.bbolt
public import GeneratedProof.go_etcd_io.bbolt.errors
public import Perennial.Proof.ProofPrelude
public import Perennial.ProgramLogic.Bounds
public import Iris.BI.Lib.Atomic
public import GooseLang.Ext.Fs.Specs
public import GooseLang.Ext.Fs.TreeShared
public import Proof.go_etcd_io.bbolt.PkgInit
public import Spec.go_etcd_io.bbolt.Data
public import Perennial.Ghost.DGhostVar
import Proof.go_etcd_io.bbolt.Inv.FileHolds
import Proof.go_etcd_io.bbolt.Inv.TxSize

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

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
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
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
@[no_expose] def isBolt [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] (db : Loc) (γ : BoltName) : IProp GF :=
  isBoltDef (bnsOf γ.gs) γ.ns db

/-- **The database `γ`'s file is the inode `i`** (persistent; session bbolt-inv): the file `Open`
opened (`Open.spec` gives it), which a closer owning the data gets back
(`DB.Close.spec`). -/
@[no_expose] def boltIno [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] (γ : BoltName) (i : Ino) : IProp GF :=
  iprop(∃ t0 : Nat, t0At (GF := GF) (bnsOf γ.gs) t0 i)

/-- **The database `γ` is closed only by the holder of this token** (exclusive, timeless; session
S3f): `Open` gives it, `DB.Close` (and its variants) consumes it. So a holder knows the database open
(no other thread can close it), which `DB.Close.spec` needs to give the file back. -/
@[no_expose] def boltCloser [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] (γ : BoltName) : IProp GF :=
  ghostVar (bnsOf γ.gs).clo 1 ()

/-- **The committed data of `γ` is `D`**, at fraction `q`: the client's view, which the
atomic updates of `Begin(false)` and `Commit` act on (fractional: a read needs some fraction, a
commit all of it). Survives `Close` (the data then stays `D`). -/
@[no_expose] def boltState [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] (γ : BoltName) (q : Qp) (D : Data) : IProp GF :=
  boltStateDef (bnsOf γ.gs) q D

/-- **The database `γ` syncs** (persistent): `γ`'s `DB` (`dblAt`) has `NoSync = false` and
`NoGrowSync = false` (fields `Open` sets from its options and never writes again, `dbFixed`), so every
`Tx.Commit` `fdatasync`s after its pages and after its meta, `DB.grow` `fsync`s after its `Truncate`, and a
writable `Open` `fdatasync`s before it returns. What C-I1's `dbOpts` is (the crash laws need it). -/
@[no_expose] def boltSyncs [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] (γ : BoltName) : IProp GF :=
  iprop(∃ db : Loc, dblAt (bnsOf γ.gs) db ∗ db.[DB, go!"NoSync"] ↦□ false ∗
    db.[DB, go!"NoGrowSync"] ↦□ false)

/-- **The namespace of the crash invariant of `γ`'s file** (under `γ.ns`): what a crash law over the
database's file opens (C-I1's `dbCrash`). -/
def crashN (N : Namespace) : Namespace := N .@ "crash"

/-- **The committed data of `γ` is `D` at version `ν`**, at fraction `q`: `boltState` with the
version, the committed txid, which moves by exactly one at each commit (`Tx.Commit.spec`'s update
gives the data back at `ν + 1`). -/
@[no_expose] def boltStateV [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] (γ : BoltName) (q : Qp) (D : Data)
    (ν : Nat) : IProp GF :=
  boltStateVDef (bnsOf γ.gs) q D ν

/-- **`tx` is a transaction of `γ`, live, with the view `T`**, at fraction `q`. A read
transaction's whole (`q = 1`) holds the reader slot `Begin(false)` took for the caller's
`threadTok` (given back by `Rollback`); its fractions may be shared between goroutines for
reads. A write transaction's operations that change it need all of it. -/
@[no_expose] def boltTx [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] (tx : Loc) (γ : BoltName) (q : Qp) (T : TxView) : IProp GF :=
  boltTxDef (bnsOf γ.gs) γ.ns tx q T

-- Round 6: `txSnap` (and `boltTx_snap`, `txSnap_agree`) dropped (review 5, finding 5): with no
-- name it needs a registry keyed by `tx`, which D19 rejected, and no caller needs it (the backend
-- keeps `boltTx tx γ q (ro D)` where it kept `rtxSnap tx D`).

/-- `tx` is a transaction of the database `db` named `γ` (persistent; what `Tx.DB` returns).
Takes `γ` (batch 21, approved by the user, 2026-11-04; the D-C precedent of `boltBkt`/`boltCur`). -/
@[no_expose] def txDB [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] (tx : Loc) (γ : BoltName) (db : Loc) : IProp GF :=
  txDBDef (bnsOf γ.gs) γ.ns tx db

/-- `tx` was committed or rolled back (persistent): its statistics can be read. -/
@[no_expose] def txDone [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] (tx : Loc) : IProp GF :=
  txDoneDef tx

/-- `b` is `tx`'s handle of the bucket named `n` at generation `g` (persistent). Its operations
need `n` at generation `g` in the transaction's view: a deleted bucket's handle is never current
again (a re-created bucket of the name gets a new generation). -/
@[no_expose] def boltBkt [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] (tx : Loc) (γ : BoltName) (b : Loc) (n : GoString) (g : Nat) : IProp GF :=
  boltBktDef (bnsOf γ.gs) tx b n g

/-- `c` is a cursor of `tx`, made at the view `T`, over the entries `es`, at position `pos`
(`none`: not positioned; `some i`, `i ≤ es.length`: at the `i`-th entry, or past the last at
`es.length`, see `Cursor.Next.spec`). Exclusive. Its moves need `tx` at the view `T`: after a
change of the transaction, a cursor made before it is not usable (Go: "You must reposition your
cursor after mutating data"; the spec does not let it be repositioned). -/
@[no_expose] def boltCur [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] (tx : Loc) (γ : BoltName) (c : Loc) (T : TxView) (es : List BoltEnt) (pos : Option Nat) : IProp GF :=
  boltCurDef (bnsOf γ.gs) tx c T es pos

/-- The slice `s` holds `b` while `tx` is live (persistent; read with `txBytes_acc`): a key or
value bbolt returned, pointing into the memory map (unmapped by a remap or `Close`, which wait
for the transaction) or into the transaction's nodes. -/
@[no_expose] def txBytes [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] (tx : Loc) (γ : BoltName) (s : GoSlice) (b : GoString) : IProp GF :=
  txBytesDef (bnsOf γ.gs) tx s b

/-- **The file at `path` holds a database with the data `D`** (exclusive): what `Open` reads.
Defined over the Linux file extension (`GooseLang/Ext/OsFs`: the file's whole `osMeta`, with no
mapping, and its `osBytes`; round 2: *not* "every byte synced": the in-process specs read the
page cache, and durability is out of scope), **its size below `2 ^ 62`** (2026-11-04, decided by
the coordinator: true of every file bbolt writes, whose mapping is at most `maxMapSize = 2 ^ 48`
on 64-bit; `Open` reads the size as an `int64` and computes the mapping's size from it), and
either
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
  - the root holds top-level buckets only (no nested bucket, no plain value), their names of
    `1..MaxKeySize` bytes (`CreateBucket` refuses others); every key non-empty; leaf entries fit the single-element address window
    (`bboltEntryMax` for key and value together), and a key fits the share available for a
    branch separator (`branchKeyMax`). These bounds hold for a successful `Put` and cover
    every file admitted by the former 256 MiB entry bound (`entryBytesFit_legacy`);
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
    and ids lie within its own extent, (2026-11-05, decided by the coordinator) **its header id is
    its page number** (true of every file bbolt writes: `init` writes it with id 2, `commitFreelist`
    the page `allocate` returns, whose header id `allocate` sets; `Commit` frees the page by
    `p.Id()` and its overflow), and its ids are distinct and in `[2, hwm)` (`Read` panics
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
    2 ^ 63`, with `t₀ < 2 ^ 62` the opened file's: what "no wrap" needs), and at least `1`
    (2026-11-04: `init` writes its current meta with txid 1, the fork's `init` is crash-safe,
    a commit only raises it, and `WriteTo` copies a database of txid at least 1; a reader of
    txid 0 would make `ReleasePendingPages` release pages a reader sees,
    `nonissues/bbolt-txid0-reader-release.md`).
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
@[no_expose] def fileHolds [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] (i : Ino) (D : Data) : IProp GF :=
  fileHoldsDef i D

/-- bbolt's largest mapping, `maxMapSize` (`0xFFFFFFFFFFFF` on amd64, `internal/common/types.go`):
`mmapSize` refuses a larger one ("mmap too large"). -/
@[word_unfold] def boltMaxMapSize : Nat := 0xFFFFFFFFFFFF

/-- **The file of inode `i` holds a database with the data `D`, and is mappable** (session S3f): what
`fileHolds` says, with the file's size at most `boltMaxMapSize`, so that `Open`'s `mmap` of it does
not fail with "mmap too large" (`Open.spec` takes it, through `nameHolds`). `DB.Close.spec` gives it
back (session S3g): in the model every mapping fits the address space (`maxAddr = 2 ^ 47`), so
`DB.grow` never truncates past `2 ^ 47 + 2 ^ 12 + AllocSize`, below `maxMapSize` (on real hardware it
can, `nonissues/bbolt-grow-past-max-map-size.md`, which needs about 256 TiB of pages). A fresh file
is (`fileHoldsM_new`), and so is an image no longer than `boltMaxMapSize`
(`fileHoldsM_of_image`; `Tx.WriteTo` writes the pages below the high-water mark, inside the
mapping). -/
@[no_expose] def fileHoldsM [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] (i : Ino) (D : Data) : IProp GF :=
  fileHoldsMDef i D

/-- **The bytes `bs` are a bbolt database file holding `D`** (S4a of
`notes/bbolt-integration-plan.md`, D-I6; pure): what `fileHolds` asks of a file's page-cache bytes,
with the file's size the length of `bs`: whole pages below `2 ^ 62` bytes (session bbolt-inv: whole
pages, as every file bbolt writes), and either empty (`D = ∅`) or a
well-formed bbolt file whose committed tree holds `D` (every clause of `fileHolds`' docstring:
metas, page extents, the synced freelist page, the high-water mark inside the bytes, the txid's
bounds). What `Tx.WriteTo` writes (its two meta pages and its data pages; many byte strings encode
one `D`, by their page layout and free pages), and what a file must hold for `Open` to read `D`
(`fileHolds_of_image`). Sealed: a client relates it only through that law. -/
@[no_expose] def boltImage (bs : List w8) (D : Data) : Prop :=
  (bs.length < 2 ^ 62 ∧ bs.length % 4096 = 0) ∧ fileOK bs bs.length D

/-- **The bytes `bs`' txid has been reached** (persistent; session bbolt-inv): the time receipt
of the txid of the committed state `bs` is an image of (if any). A file's txid counts its commits,
each a counted step of the program, so it is below the bound on the program's steps: what an
`Open` of the file needs, besides `boltImage`, to bound its later txids (`fileHolds_of_image`).
`Tx.WriteTo` gives it for the bytes it writes; a client carries it with them. -/
@[no_expose] def boltImageRcpt [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] (bs : List w8) : IProp GF :=
  fileRcpt bs

/-! ## Laws -/

@[instance] theorem isBolt_persistent (db : Loc) (γ : BoltName) :
    Persistent (isBolt (GF := GF) db γ) := by
  unfold isBolt; infer_instance
-- Round 3: round 2's `isBolt_agree`/`boltTx_isBolt` are dropped (review 2, finding 6: a pure
-- entailment between two handles needs a registry `db ↦ γ`, and none can be had: a package fact
-- is a fixed proposition, so a ghost name inside it does not agree between two copies; D-E).
-- The clients carry `γ` instead: the backend already has it (`BNames`' `γ.db`, beside every
-- `isDB db`), so its layer is `isDB db := isBolt db γ.db` (`notes/bbolt-spec-decisions.md`, D19).
@[instance] theorem boltIno_persistent (γ : BoltName) (i : Ino) :
    Persistent (boltIno (GF := GF) γ i) := by
  unfold boltIno t0At; infer_instance
@[instance] theorem boltCloser_timeless (γ : BoltName) :
    Timeless (boltCloser (GF := GF) γ) := by
  unfold boltCloser; infer_instance

/-- The closer token is exclusive. -/
theorem boltCloser_excl (γ : BoltName) :
    boltCloser (GF := GF) γ ∗ boltCloser γ ⊢ False := by
  unfold boltCloser
  iintro ⟨H1, H2⟩
  icombine H1 H2 gives %h
  exfalso
  have h1 := h.1
  rw [Qp.le_iff, Qp.val_add, Qp.val_one] at h1
  grind

@[instance] theorem boltImageRcpt_persistent (bs : List w8) :
    Persistent (boltImageRcpt (GF := GF) bs) := by
  unfold boltImageRcpt; infer_instance
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
/-- `boltState` is `boltStateV` at some version. -/
theorem boltState_eq_V (γ : BoltName) (q : Qp) (D : Data) :
    boltState (GF := GF) γ q D ⊣⊢ ∃ ν, boltStateV γ q D ν := by
  unfold boltState boltStateV boltStateDef; exact .rfl
@[instance] theorem boltSyncs_persistent (γ : BoltName) :
    Persistent (boltSyncs (GF := GF) γ) := by
  unfold boltSyncs dblAt; infer_instance
@[instance] theorem boltStateV_timeless (γ : BoltName) (q : Qp) (D : Data) (ν : Nat) :
    Timeless (boltStateV (GF := GF) γ q D ν) := by
  unfold boltStateV; infer_instance
@[instance] theorem boltStateV_fractional (γ : BoltName) (D : Data) (ν : Nat) :
    Fractional (fun q => boltStateV (GF := GF) γ q D ν) := by
  unfold boltStateV; exact boltStateVDef_fractional _ _ _
theorem boltStateV_agree (γ : BoltName) (q1 q2 : Qp) (D1 D2 : Data) (ν1 ν2 : Nat) :
    boltStateV (GF := GF) γ q1 D1 ν1 ∗ boltStateV γ q2 D2 ν2 ⊢ ⌜D1 = D2 ∧ ν1 = ν2⌝ := by
  unfold boltStateV; exact boltStateVDef_agree _ _ _ _ _ _ _

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

/-- **A read transaction's buckets hold fewer than `2 ^ 61` entries** (S1a of
`notes/bbolt-integration-plan.md`, D-I3; the backend's `rtxSnap_size`, an axiom until then). Every
entry of a bucket of the snapshot is an element of a leaf page of the database's memory map (or of
the inline page in such an element): a page holds at most `2 ^ 16` (its header's `count` is a
`uint16`), the leaves of a bucket are distinct pages (no page is shared), and every page lies
within the map, of at most `maxMapSize < 2 ^ 48` bytes, so there are fewer than `2 ^ 36` of them:
at most `2 ^ 52` entries. For a read transaction only: a writer's view holds its nodes' entries,
which no bound of the invariant counts (the backend needs it only for its read transactions). -/
theorem boltTx_size (tx : Loc) (γ : BoltName) (q : Qp) (D : Data) :
    boltTx (GF := GF) tx γ q (TxView.ro D) ⊢
      ⌜∀ (n : GoString) (m : BktData), D.lookup n = some m → m.size < 2 ^ 61⌝ := by
  unfold boltTx; exact boltTxDef_size_ro _ _ _ _ _

@[instance] theorem txDB_persistent (tx : Loc) (γ : BoltName) (db : Loc) :
    Persistent (txDB (GF := GF) tx γ db) := by
  unfold txDB; infer_instance
@[instance] theorem txDone_persistent (tx : Loc) : Persistent (txDone (GF := GF) tx) := by
  unfold txDone; infer_instance
@[instance] theorem boltBkt_persistent (tx : Loc) (γ : BoltName) (b : Loc) (n : GoString)
    (g : Nat) : Persistent (boltBkt (GF := GF) tx γ b n g) := by
  unfold boltBkt; infer_instance
private instance ite_timeless_api (c : Prop) [Decidable c] (P Q : IProp GF) [Timeless P]
    [Timeless Q] : Timeless (if c then P else Q) := by
  split <;> infer_instance
/-- A bucket handle is timeless (ghost state and persistent points-tos; stage S1, 2026-11-17: the
backend keeps its read transaction's handles in an invariant, `backend.cmFacts`). -/
@[instance] theorem boltBkt_timeless (tx : Loc) (γ : BoltName) (b : Loc) (n : GoString)
    (g : Nat) : Timeless (boltBkt (GF := GF) tx γ b n g) := by
  unfold boltBkt boltBktDef reg handleFrag viewOf rBkt locOwn
  refine @exists_timeless _ _ _ _ (fun r => ?_)
  rcases r with ⟨db, n', rw, src⟩
  cases rw <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> infer_instance
@[instance] theorem txBytes_persistent (tx : Loc) (γ : BoltName) (s : GoSlice) (b : GoString) :
    Persistent (txBytes (GF := GF) tx γ s b) := by
  unfold txBytes; infer_instance
@[instance] theorem boltCur_timeless (tx : Loc) (γ : BoltName) (c : Loc) (T : TxView)
    (es : List BoltEnt) (pos : Option Nat) : Timeless (boltCur (GF := GF) tx γ c T es pos) := by
  unfold boltCur; infer_instance
@[instance] theorem fileHolds_timeless (i : Ino) (D : Data) :
    Timeless (fileHolds (GF := GF) i D) := by
  unfold fileHolds; infer_instance

@[instance] theorem fileHoldsM_timeless (i : Ino) (D : Data) :
    Timeless (fileHoldsM (GF := GF) i D) := by
  unfold fileHoldsM; infer_instance

/-- A mappable file holds its data (session S3f). -/
theorem fileHoldsM_fileHolds (i : Ino) (D : Data) :
    fileHoldsM (GF := GF) i D ⊢ fileHolds i D := by
  unfold fileHoldsM fileHolds; exact fileHoldsMDef_holds _ _

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

/-- The same for a commit from `D` to `S` (the versioned update `Tx.Commit` takes). -/
theorem boltState_commit_au (γ : BoltName) (D S : Data) :
    boltState (GF := GF) γ 1 D ⊢
      AU <{ ∃∃ (D' : Data) (ν : Nat), boltStateV γ 1 D' ν }> @ ⊤ \ ↑γ.ns, ∅
        <{ ⌜D' = D⌝ ∗ boltStateV γ 1 S (ν + 1), COMM boltState γ 1 S }> := by
  unfold boltState boltStateV; exact boltState_commit_au' _ _ _ _

/-- **A commit update over `boltState` is one over `boltStateV`** (what a caller holding the
unversioned update gives `Tx.Commit`). -/
theorem commitAU_of_unversioned (γ : BoltName) (Db Dn : Data) (Q : IProp GF) :
    AU <{ ∃∃ (D' : Data), boltState (GF := GF) γ 1 D' }> @ ⊤ \ ↑γ.ns, ∅
        <{ ⌜D' = Db⌝ ∗ boltState γ 1 Dn, COMM Q }> ⊢
      AU <{ ∃∃ (D' : Data) (ν : Nat), boltStateV γ 1 D' ν }> @ ⊤ \ ↑γ.ns, ∅
        <{ ⌜D' = Db⌝ ∗ boltStateV γ 1 Dn (ν + 1), COMM Q }> := by
  unfold boltState boltStateV; exact commitAU_versioned _ _ _ _ _

/-- **bbolt's `Close` succeeds** (opaque, a named premise about the program's environment, moved
from the backend's `InvBbolt.lean`): `db.Close()` does not fail for the environment's reasons
(unmapping the file, unlocking it, closing it). Not used by `DB.Close.spec`, which is proved over
a file model where these system calls may fail; only the trust-boundary layer
`DB.Close_kv` (backend) rests on it. -/
opaque dbCloseOk : Prop

/-- **A file just created holds the empty database** (`os.OpenFile.specCreate`'s `newMeta`). -/
theorem fileHolds_new (i : Ino) :
    osMeta (GF := GF) i (DFrac.own 1) newMeta ⊢ fileHolds i ∅ := by
  unfold fileHolds; exact fileHoldsDef_new _

/-- **A file just created holds the empty database, and is mappable** (session S3f). -/
theorem fileHoldsM_new (i : Ino) :
    osMeta (GF := GF) i (DFrac.own 1) newMeta ⊢ fileHoldsM i ∅ := by
  unfold fileHoldsM fileHoldsMDef
  iintro H
  iexists newMeta, []
  iframe H
  isplitl
  · unfold osBytes; iapply (bytesG_nil _ _ _ _).2; iempintro
  isplitr
  · ipureintro
    exact ⟨rfl, rfl, by decide, Or.inl ⟨rfl, rfl⟩⟩
  isplitr
  · ipureintro; rw [show newMeta.size = 0 from rfl]; omega
  unfold fileRcpt
  ileft; ipureintro
  exact fun C h => fileImage_nil_not C (by simpa using h)

/-- **A file holding a database image holds its data** (S4a, D-I6: the receiver's half of the
snapshot's round trip): the whole `OsMeta` of a file with no mapping, of size `xs.length`, and all
of its page-cache bytes `xs` (any crash candidates), whose values are an image of `D`, with the
time receipt of their txid (`boltImageRcpt`, session bbolt-inv). -/
theorem fileHolds_of_image (i : Ino) (m : OsMeta) (xs : List ByteG) (D : Data)
    (hmaps : m.maps = ∅) (hsize : m.size = xs.length) (himg : boltImage (xs.map Prod.fst) D) :
    osMeta (GF := GF) i (DFrac.own 1) m ∗ osBytes i 0 (DFrac.own 1) xs ∗
      boltImageRcpt (xs.map Prod.fst) ⊢ fileHolds i D := by
  unfold fileHolds fileHoldsDef boltImageRcpt
  unfold boltImage at himg
  rw [List.length_map] at himg
  iintro ⟨Hm, Hb, #Hr⟩
  iexists m, xs
  iframe Hm Hb Hr
  ipureintro
  exact ⟨hmaps, hsize.symm, hsize ▸ himg.1, hsize ▸ himg.2⟩

/-- **A mappable image holds its data, mappable** (session S3f; `fileHolds_of_image` with the image no
longer than `boltMaxMapSize`). -/
theorem fileHoldsM_of_image (i : Ino) (m : OsMeta) (xs : List ByteG) (D : Data)
    (hmaps : m.maps = ∅) (hsize : m.size = xs.length) (himg : boltImage (xs.map Prod.fst) D)
    (hlen : xs.length ≤ boltMaxMapSize) :
    osMeta (GF := GF) i (DFrac.own 1) m ∗ osBytes i 0 (DFrac.own 1) xs ∗
      boltImageRcpt (xs.map Prod.fst) ⊢ fileHoldsM i D := by
  unfold fileHoldsM fileHoldsMDef boltImageRcpt
  unfold boltImage at himg
  rw [List.length_map] at himg
  iintro ⟨Hm, Hb, #Hr⟩
  iexists m, xs
  iframe Hm Hb Hr
  isplitr
  · ipureintro
    exact ⟨hmaps, hsize.symm, hsize ▸ himg.1, hsize ▸ himg.2⟩
  · ipureintro; rw [hsize]; exact hlen

omit hG in
/-- **The txid's receipt is the run's, not the generation's** (D6-T6, P7, 2026-11-25): a time receipt is
global ghost state (`GooseGlobalGS`'s receipts), so `boltImageRcpt` at a generation `L` is it at any other
`L'` (a crash keeps it: what a file kept whole across a crash needs, `backend.fileHoldsMDur_crash`). -/
theorem boltImageRcpt_gen (G : GooseGlobalGS hlc GF) (L L' : GooseLocalGS GF) (bs : List w8) :
    boltImageRcpt (hG := ⟨G, L⟩) bs ⊢ boltImageRcpt (hG := ⟨G, L'⟩) bs := by
  unfold boltImageRcpt fileRcpt
  exact .rfl

end vocab

section stat
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
/- Every bbolt spec is stated over OsFs's semantics (round 11, D22: the default `osFs_semantics`,
whose `pwrite` within one aligned OS page is all-or-nothing): the binder `∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]` at
the head of each triple (a section variable is dropped from a definition that does not use it),
and in the signature of each vocabulary predicate, so that every statement carries it (checked
with `#check`). -/
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- What pays for `statlock`'s reader slot in `DB.Stats`: the caller's `threadTok` (`none`), or
the whole of a transaction (`some (tx, T)`, S1a of `notes/bbolt-integration-plan.md`: a read or a
write transaction), whose slot covers `statlock` too: for a caller whose token a transaction
holds, as the backend's `begin` right after `Begin` (`notes/bbolt-spec-decisions.md`, D2). Sound
because the implementation's reader pool lends a *pair* per token, an `mmaplock` reader token and a
`statlock` one, so a read transaction's slot covers its `Stats`; a write transaction holds
`rwlock`, whose resource keeps the spare pair (for `Commit`'s `freepages`, which borrows it only
inside `Commit`, when no caller holds the transaction), whose `statlock` token covers its `Stats`.
It needs all of the transaction, since two holders of fractions calling `Stats` at once would need
two `statlock` tokens. -/
def statSlot [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] (γ : BoltName) : Option (Loc × TxView) → IProp GF
  | none => threadTok
  | some (tx, T) => boltTx tx γ 1 T

end stat

end bbolt
end EtcdGrove
end Perennial
