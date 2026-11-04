/-
The persistent database predicate (U0a of `notes/bbolt-proof-plan.md`; design §3.4, §3.8):
`isBoltCore` (everything `Open`'s core phase builds: the fixed fields, `metalock`, `mmaplock`,
`statlock`, the page store and the transactions) and `isBolt` (the core, `rwlock` and the reader
pool), over the names `B` and the client's namespace `N` (`Inv/Names.lean`).

The database's location and the receipts' base are pinned by discarded ghost-map fragments
(`dblAt`, `t0At`), so that two `isBolt`s of one name agree on the database (D-A's
`boltTx_later`).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Txs
public import Proof.go_etcd_io.bbolt.PkgInit
public import Spec.go_etcd_io.bbolt.Logger
public import Perennial.Proof.sync.PoolDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section bolt
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `B` is the database at `db` (persistent, agreeing). -/
def dblAt (B : BNs) (db : Loc) : IProp GF := iprop(ghostMapElem B.dbl () DFrac.discard db)

/-- `B`'s receipts' base (the opened file's txid) is `t0` (persistent, agreeing). -/
def t0At (B : BNs) (t0 : Nat) : IProp GF := iprop(ghostMapElem B.t0 () DFrac.discard t0)

/-- The database's logger: a `boltLogger` (batch 15: the option's, or bbolt's `discardLogger`'s
value, which `Open` sets when the option's is nil and which is one, `Open/Logger.discardLogger_boltLogger'`; so
`db.Logger()`'s nil test resolves and its result can be called). -/
def dbLogger (lg : GoInterface) : IProp GF :=
  iprop(boltLogger lg)

-- (`discardLogger` holds a `boltLogger`: `Open/Logger.discardLogger_boltLogger'`, proved over the
-- package's `Assumptions`; batch 38 deleted the stub here, stated without them.)

/-- What the page pool holds: zeroed page buffers. -/
def pageBuf (v : GoAny) : IProp GF :=
  iprop(∃ s : GoSlice, ⌜v = interface.mkOk (go.GoType.SliceType go.byte) #s⌝ ∗
    s ↦* List.replicate 4096 (W8 0))

/-- A logger whose dynamic type is a pointer type holds a location (batch 34: Go's `lg !=
discardLogger` compares at the dynamic type, a pointer type's `==` on locations; the model's
interface values pair a type with any value). -/
def logPtrTyped (lg : GoInterface) : Prop :=
  ∀ ii : GoInterfaceOk, lg = GoInterface.ok ii → ∀ T : go.GoType, ii.ty = go.GoType.PointerType T →
    ∃ l : Loc, ii.v = #l

/-- **`db`'s fields written only by `Open`** (persistent, design §3.4): the page size, the
statistics pointer, the logger, `readOnly`, the exported options (`StrictMode` and `Mlock` off),
`openFile`, the page pool (its `New` not nil, batch 29: `Open` sets it, and `Get().([]byte)`
asserts on its result), the never-used batch fields, and (batch 34, last so that the patterns
ending in `-` stand) the logger's value a location if its type is a pointer type (`logPtrTyped`). `MmapFlags` is `0` or `MAP_POPULATE` (batch 15: `OptsM.ok`'s, for
`mmap`'s `unix.Mmap`). `AllocSize` is `DefaultAllocSize` (16 MiB, batch 24: `Open` sets it;
`isBolt` forbids writing `DB`'s exported fields after `Open`), for `DB.grow`'s size. (Not `freelistLoad`'s `sync.Once`:
Perennial's `isOnce` is stated for `HasLC.hasLC` only, and the sealed predicates are over any
`hlc`; U11 decides how `loadFreelist`'s `Once.Do` is covered, `notes/bbolt-proof-plan.md`.) -/
def dbFixed (db sp : Loc) : IProp GF :=
  iprop(db.[DB, go!"pageSize"] ↦□ W64 4096 ∗ db.[DB, go!"stats"] ↦□ sp ∗
    (∃ lg, db.[DB, go!"logger"] ↦□ lg ∗ dbLogger lg) ∗
    db.[DB, go!"readOnly"] ↦□ false ∗ db.[DB, go!"StrictMode"] ↦□ false ∗
    db.[DB, go!"Mlock"] ↦□ false ∗
    (∃ x : Bool, db.[DB, go!"NoSync"] ↦□ x) ∗ (∃ x : Bool, db.[DB, go!"NoGrowSync"] ↦□ x) ∗
    (∃ x : Bool, db.[DB, go!"NoFreelistSync"] ↦□ x) ∗
    (∃ x : Bool, db.[DB, go!"PreLoadFreelist"] ↦□ x) ∗
    (∃ x : FreelistType, db.[DB, go!"FreelistType"] ↦□ x) ∗
    (∃ x : w64, db.[DB, go!"MmapFlags"] ↦□ x ∗ ⌜x = W64 0 ∨ x = W64 0x8000⌝) ∗ (∃ x : w64, db.[DB, go!"MaxBatchSize"] ↦□ x) ∗
    (∃ x : time.Duration, db.[DB, go!"MaxBatchDelay"] ↦□ x) ∗
    db.[DB, go!"AllocSize"] ↦□ W64 0x1000000 ∗ (∃ x : w64, db.[DB, go!"MaxSize"] ↦□ x) ∗
    (∃ x : GoFunc, db.[DB, go!"openFile"] ↦□ x) ∗
    (∃ f : GoFunc, sync.isPool db.[DB, go!"pagePool"] f pageBuf ∗ ⌜f ≠ func.nil⌝) ∗
    sync.isMutex db.[DB, go!"batchMu"] iprop(True) ∗ db.[DB, go!"batch"] ↦□ null ∗
    (∃ lg, db.[DB, go!"logger"] ↦□ lg ∗ ⌜logPtrTyped lg⌝))

/-- **The core of an open database** at `db` (design §3.8, round 2 F1), with its path `p`,
statistics pointer `sp` and receipts' base `t0`; its namespace disjoint from OsFs's (batch 37:
`Open`'s premise; `store_cells_agree` opens `pagesInv` around an OsFs step); the receipts' bound
at most `2 ^ 62` (maintainer 12, item 1: `Open`'s `ReceiptBoundLe GF (2 ^ 62)`, recorded so that
`Commit` bounds the next txid, `receipt_txid_lt`). -/
def isBoltCoreP (B : BNs) (N : Namespace) (db : Loc) (p : GoString) (sp : Loc) (t0 : Nat) :
    IProp GF :=
  iprop(dblAt B db ∗ t0At B t0 ∗
    ⌜(t0 < 2 ^ 62 ∧ receiptBound GF ≤ 2 ^ 62) ∧ db ≠ null ∧ (↑N : CoPset) ## ↑osN⌝ ∗
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ osInv ∗ dbFixed db sp ∗
    sync.isMutex db.[DB, go!"metalock"] (metaR B db p) ∗
    sync.isRWMutexGuard db.[DB, go!"mmaplock"] (Pm B db) ∗
    sync.isRWMutexGuard db.[DB, go!"statlock"] (Ps sp) ∗
    inv (pagesN N) (pagesInv B p) ∗ inv (txsN N) (txsInv B p sp t0))

/-- The core of an open database (what `beginTx`, `removeTx`, `freepages` and `loadFreelist`
need). -/
def isBoltCore (B : BNs) (N : Namespace) (db : Loc) : IProp GF :=
  iprop(∃ (p : GoString) (sp : Loc) (t0 : Nat), isBoltCoreP B N db p sp t0)

/-- The full database at `db`, with its parameters. -/
def isBoltP (B : BNs) (N : Namespace) (db : Loc) (p : GoString) (sp : Loc) (t0 : Nat) :
    IProp GF :=
  iprop(isBoltCoreP B N db p sp t0 ∗ sync.isMutex db.[DB, go!"rwlock"] (rwR B db p sp t0) ∗
    threadPool.isThreadPool (poolN N) B.pool (rdPair B db sp) ∗ opnShot B)

/-- **`db` is the database `B`/`N`** (design §3.8): what `isBolt db γ` is sealed to, with
`B = bnsOf γ.gs`, `N = γ.ns`. -/
def isBoltDef (B : BNs) (N : Namespace) (db : Loc) : IProp GF :=
  iprop(∃ (p : GoString) (sp : Loc) (t0 : Nat), isBoltP B N db p sp t0)

/-! ## Lemma statements (U5) -/

omit [GooseSemantics] go_gctx hos sem in
/-- **The writer's next txid does not wrap** (maintainer 12, item 1): the writer side's receipts
`⧗ (c - t0)` (`wdbOwn`, `wdbLive`) number fewer than `receiptBound GF ≤ 2 ^ 62`, and `t0 < 2 ^ 62`
(both in `isBoltCoreP`), so `c + 1 < 2 ^ 63`. -/
theorem receipt_txid_lt (t0 c : Nat) (ht0 : t0 < 2 ^ 62) (hrb : receiptBound GF ≤ 2 ^ 62) :
    receipt (GF := GF) (c - t0) ⊢ receipt (c - t0) ∗ ⌜c + 1 < 2 ^ 63⌝ :=
  persistent_entails_left ((receipt_lt (GF := GF) (c - t0)).trans (pure_mono fun h => by omega))

/-- The core's receipt facts: `t0 < 2 ^ 62` and `receiptBound GF ≤ 2 ^ 62`. -/
theorem isBoltCoreP_receipts (B : BNs) (N : Namespace) (db : Loc) (p : GoString) (sp : Loc)
    (t0 : Nat) : isBoltCoreP (GF := GF) B N db p sp t0 ⊢ ⌜t0 < 2 ^ 62 ∧ receiptBound GF ≤ 2 ^ 62⌝ := by
  unfold isBoltCoreP
  iintro ⟨-, -, %H, -⟩
  ipureintro; exact H.1

/-- **`receipt_txid_lt` from the core**: the receipts `⧗ (c - t0)` of the core's `t0`. -/
theorem isBoltCoreP_txid_lt (B : BNs) (N : Namespace) (db : Loc) (p : GoString) (sp : Loc)
    (t0 c : Nat) :
    isBoltCoreP (GF := GF) B N db p sp t0 ∗ receipt (c - t0) ⊢ receipt (c - t0) ∗ ⌜c + 1 < 2 ^ 63⌝ := by
  iintro ⟨Hc, Hr⟩
  ihave %H := isBoltCoreP_receipts B N db p sp t0 $$ Hc
  iapply receipt_txid_lt t0 c H.1 H.2
  iexact Hr

instance isBoltCoreP_persistent (B : BNs) (N : Namespace) (db : Loc) (p : GoString) (sp : Loc)
    (t0 : Nat) : Persistent (isBoltCoreP (GF := GF) B N db p sp t0) := by
  unfold isBoltCoreP dblAt t0At dbFixed dbLogger; infer_instance

instance isBoltCore_persistent (B : BNs) (N : Namespace) (db : Loc) :
    Persistent (isBoltCore (GF := GF) B N db) := by
  unfold isBoltCore; infer_instance

instance isBoltDef_persistent (B : BNs) (N : Namespace) (db : Loc) :
    Persistent (isBoltDef (GF := GF) B N db) := by
  unfold isBoltDef isBoltP; infer_instance

/-- The full database has its core. -/
theorem isBolt_core (B : BNs) (N : Namespace) (db : Loc) :
    isBoltDef (GF := GF) B N db ⊢ isBoltCore B N db := by
  unfold isBoltDef isBoltP isBoltCore
  iintro ⟨%p, %sp, %t0, Hc, -⟩
  iexists p, sp, t0; iexact Hc

/-- Two databases of one name are one database. -/
theorem isBolt_db_agree (B : BNs) (N : Namespace) (db db' : Loc) :
    isBoltDef (GF := GF) B N db ∗ isBoltCore B N db' ⊢ ⌜db = db'⌝ := by
  unfold isBoltDef isBoltP isBoltCore isBoltCoreP dblAt
  iintro ⟨⟨%p, %sp, %t0, ⟨H1, -⟩, -⟩, ⟨%p', %sp', %t0', H2, -⟩⟩
  icombine H1 H2 gives %h
  ipureintro; exact h.2

/-- The core's parameters agree with the full database's. -/
theorem isBoltP_agree (B : BNs) (N : Namespace) (db : Loc) (p p' : GoString) (sp sp' : Loc)
    (t0 t0' : Nat) :
    isBoltP (GF := GF) B N db p sp t0 ∗ isBoltCoreP B N db p' sp' t0' ⊢ ⌜sp = sp' ∧ t0 = t0'⌝ := by
  unfold isBoltP isBoltCoreP dbFixed t0At
  iintro ⟨⟨⟨-, Ht, -, -, -, ⟨-, Hsp, -⟩, -⟩, -⟩, ⟨-, Ht', -, -, -, ⟨-, Hsp', -⟩, -⟩⟩
  icombine Ht Ht' gives %h1
  icombine Hsp Hsp' gives %h2
  ipureintro; exact ⟨h2, h1.2⟩

/-- **The database's logger is `logPtrTyped`** (batch 34; `dbFixed`'s last clause, read against the
caller's copy of the logger field). -/
theorem dbFixed_logPtrTyped (db sp : Loc) (lg : GoInterface) :
    dbFixed (GF := GF) db sp ⊢ db.[DB, go!"logger"] ↦□ lg -∗ ⌜logPtrTyped lg⌝ := by
  unfold dbFixed
  iintro ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, %lg', #H, %Ht⟩ #Hl
  ihave %Heq := typedPointsto_agree_wand _ _ _ _ _ $$ H Hl
  subst Heq
  ipureintro; exact Ht

end bolt

end bbolt
end EtcdGrove
end Perennial
