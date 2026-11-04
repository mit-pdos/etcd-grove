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
value, which `Open` sets when the option's is nil and which is one, `discardLogger_boltLogger`; so
`db.Logger()`'s nil test resolves and its result can be called). -/
def dbLogger (lg : GoInterface) : IProp GF :=
  iprop(boltLogger lg)

/-- **`discardLogger` holds a `boltLogger`** (batch 15; for `Open`, U11): bbolt's package
initializer stores `&nopLogger{}` (the fork's no-op logger, `discardlogger.diff`) in it, whose
methods return at once. Needs the package's facts (`bboltRootInit`) to say what the global holds:
`etc/gen-init.py`'s `SPECIAL` entry for bbolt, and its `Init.lean` to prove it. Owner: U11. -/
theorem discardLogger_boltLogger :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ⊢
      ∃ lg, globalAddr discardLogger ↦□ lg ∗ boltLogger lg := by
  sorry

/-- What the page pool holds: zeroed page buffers. -/
def pageBuf (v : GoAny) : IProp GF :=
  iprop(∃ s : GoSlice, ⌜v = interface.mkOk (go.GoType.SliceType go.byte) #s⌝ ∗
    s ↦* List.replicate 4096 (W8 0))

/-- **`db`'s fields written only by `Open`** (persistent, design §3.4): the page size, the
statistics pointer, the logger, `readOnly`, the exported options (`StrictMode` and `Mlock` off),
`openFile`, the page pool, the never-used batch fields. `MmapFlags` is `0` or `MAP_POPULATE` (batch 15: `OptsM.ok`'s, for
`mmap`'s `unix.Mmap`). (Not `freelistLoad`'s `sync.Once`:
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
    (∃ x : w64, db.[DB, go!"AllocSize"] ↦□ x) ∗ (∃ x : w64, db.[DB, go!"MaxSize"] ↦□ x) ∗
    (∃ x : GoFunc, db.[DB, go!"openFile"] ↦□ x) ∗
    (∃ f : GoFunc, sync.isPool db.[DB, go!"pagePool"] f pageBuf) ∗
    sync.isMutex db.[DB, go!"batchMu"] iprop(True) ∗ db.[DB, go!"batch"] ↦□ null)

/-- **The core of an open database** at `db` (design §3.8, round 2 F1), with its path `p`,
statistics pointer `sp` and receipts' base `t0`. -/
def isBoltCoreP (B : BNs) (N : Namespace) (db : Loc) (p : GoString) (sp : Loc) (t0 : Nat) :
    IProp GF :=
  iprop(dblAt B db ∗ t0At B t0 ∗ ⌜t0 < 2 ^ 62 ∧ db ≠ null⌝ ∗
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
    threadPool.isThreadPool (poolN N) B.pool (rdPair B db sp))

/-- **`db` is the database `B`/`N`** (design §3.8): what `isBolt db γ` is sealed to, with
`B = bnsOf γ.gs`, `N = γ.ns`. -/
def isBoltDef (B : BNs) (N : Namespace) (db : Loc) : IProp GF :=
  iprop(∃ (p : GoString) (sp : Loc) (t0 : Nat), isBoltP B N db p sp t0)

/-! ## Lemma statements (U5) -/

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

end bolt

end bbolt
end EtcdGrove
end Perennial
