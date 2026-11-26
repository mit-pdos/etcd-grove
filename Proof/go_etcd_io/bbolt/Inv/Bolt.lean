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
public import Proof.go_etcd_io.bbolt.Inv.BFileCrash
public import Proof.go_etcd_io.bbolt.PkgInit
public import Spec.go_etcd_io.bbolt.Logger
public import Perennial.Proof.sync.PoolDefs
public import Proof.go_etcd_io.bbolt.Inv.State

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section bolt
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `B` is the database at `db` (persistent, agreeing). -/
def dblAt (B : BNs) (db : Loc) : IProp GF := iprop(ghostMapElem B.dbl () DFrac.discard db)

/-- `B`'s receipts' base (the opened file's txid) is `t0` and its file's inode `i` (persistent,
agreeing; the inode since session bbolt-inv: what `boltIno` names, so that `Close` can give the
file back, `DB.Close_own.spec`). -/
def t0At (B : BNs) (t0 : Nat) (i : Ino) : IProp GF :=
  iprop(ghostMapElem B.t0 () DFrac.discard (t0, i))

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

/-- **What a caller of the page pool's `Get` lends its `New`** (U11i): a resource `P` that
excludes the whole of `boltState`'s validity token `γ` (the database's `B.bq`; `N` its namespace). Every caller of `Get` is inside a
`Commit`, which holds the client's commit update over `boltState γ 1` (an atomic update excludes
the whole state: opening it gives the state); `Open`, while it writes its named result `db`
(which `New` reads), holds the whole `boltState` itself, so no `New` runs then (`Open.lean`). The
caller gets `P` back (`Get` returns `R`). -/
def poolR (γ : GName) (N : Namespace) (P : IProp GF) : IProp GF :=
  iprop(P ∗ □ (P ∗ ghostVar γ 1 () ={⊤ \ ↑N}=∗ False))

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
def dbFixed (γ : GName) (N : Namespace) (db sp : Loc) : IProp GF :=
  iprop(db.[DB, go!"pageSize"] ↦□ W64 4096 ∗ db.[DB, go!"stats"] ↦□ sp ∗
    (∃ lg, db.[DB, go!"logger"] ↦□ lg ∗ dbLogger lg) ∗
    db.[DB, go!"readOnly"] ↦□ false ∗ db.[DB, go!"StrictMode"] ↦□ false ∗
    db.[DB, go!"Mlock"] ↦□ false ∗
    (∃ x : Bool, db.[DB, go!"NoSync"] ↦□ x) ∗ (∃ x : Bool, db.[DB, go!"NoGrowSync"] ↦□ x) ∗
    db.[DB, go!"NoFreelistSync"] ↦□ true ∗
    (∃ x : Bool, db.[DB, go!"PreLoadFreelist"] ↦□ x) ∗
    (∃ x : FreelistType, db.[DB, go!"FreelistType"] ↦□ x) ∗
    (∃ x : w64, db.[DB, go!"MmapFlags"] ↦□ x ∗ ⌜x = W64 0 ∨ x = W64 0x8000⌝) ∗ (∃ x : w64, db.[DB, go!"MaxBatchSize"] ↦□ x) ∗
    (∃ x : time.Duration, db.[DB, go!"MaxBatchDelay"] ↦□ x) ∗
    db.[DB, go!"AllocSize"] ↦□ W64 0x1000000 ∗ (∃ x : w64, db.[DB, go!"MaxSize"] ↦□ x) ∗
    (∃ x : GoFunc, db.[DB, go!"openFile"] ↦□ x) ∗
    (∃ f : GoFunc, (∀ P : IProp GF, sync.isPool db.[DB, go!"pagePool"] f (poolR γ N P) pageBuf) ∗
      ⌜f ≠ func.nil⌝) ∗
    sync.isMutex db.[DB, go!"batchMu"] iprop(True) ∗ db.[DB, go!"batch"] ↦□ null ∗
    (∃ lg, db.[DB, go!"logger"] ↦□ lg ∗ ⌜logPtrTyped lg⌝))

/-- **The file's mode** (W1 of `plans/bbolt-crash-plan.md` §7; persistent): outside a crash
invariant (`p.cs = none`), the sync options' values, of which, if the file system does not fail,
one is on; inside one
(`p.cs = some c`), its names are bbolt's (closing token `gbq`, namespace `N .@ "crash"`), the file
system does not fail, the crash invariant (`bCsInv`) and the sync options off (`bSyncs`). So crash
mode is on iff `NoSync` and `NoGrowSync` are off and the file system does not fail (`Open` chooses it
then). Either way the registry `gcn` (`B.cn`, `cnReg`) holds the crash invariant's client names
(W3), `none` outside crash mode. -/
def bMode (gbq gcn : GName) (N : Namespace) (db : Loc) (p : BFile) : IProp GF :=
  match p.cs with
  | none => iprop((∃ (ns ngs : Bool), db.[DB, go!"NoSync"] ↦□ ns ∗
      db.[DB, go!"NoGrowSync"] ↦□ ngs ∗ ⌜FsNoErr → ns = true ∨ ngs = true⌝) ∗
      dghostVar gcn DFrac.discard (none : Option CsG))
  | some c => iprop(⌜c.gc = gbq ∧ c.N = N .@ "crash" ∧ FsNoErr⌝ ∗ bCsInv p ∗ bSyncs db p ∗
      dghostVar gcn DFrac.discard (some c.cg))

instance bMode_persistent (gbq gcn : GName) (N : Namespace) (db : Loc) (p : BFile) :
    Persistent (bMode (GF := GF) gbq gcn N db p) := by
  unfold bMode; cases p.cs <;> dsimp only <;> infer_instance

/-- **The mode's registry** (W3): the crash invariant's client names, `none` outside crash mode. -/
theorem bMode_cnReg (B : BNs) (N : Namespace) (db : Loc) (p : BFile) :
    bMode (GF := GF) B.bq B.cn N db p ⊢ cnReg B (p.cs.map CsN.cg) := by
  unfold bMode cnReg
  cases p.cs with
  | none => dsimp only [Option.map]; iintro ⟨-, #H⟩; iexact H
  | some c => dsimp only [Option.map]; iintro ⟨-, -, -, #H⟩; iexact H

/-- **The mode's sync options** (W5): in crash mode `NoSync` and `NoGrowSync` are off (`bSyncs`). -/
theorem bMode_bSyncs (gbq gcn : GName) (N : Namespace) (db : Loc) (p : BFile) :
    bMode (GF := GF) gbq gcn N db p ⊢ bSyncs db p := by
  unfold bMode
  cases hc : p.cs with
  | none => dsimp only; iintro -; iapply (bSyncs_none (GF := GF) hc db)
  | some c => dsimp only; iintro ⟨-, -, #Hs, -⟩; iexact Hs

/-- The mode outside crash mode: the registry is `none`. -/
theorem bMode_none (B : BNs) (N : Namespace) (db : Loc) (p : BFile) (hc : p.cs = none) :
    bMode (GF := GF) B.bq B.cn N db p ⊢ cnReg B none := by
  have h := bMode_cnReg (GF := GF) B N db p
  rw [hc] at h; exact h

/-- The mode in crash mode: bbolt's names, the file system does not fail, the registry. -/
theorem bMode_some (B : BNs) (N : Namespace) (db : Loc) (p : BFile) (c : CsN) (hc : p.cs = some c) :
    bMode (GF := GF) B.bq B.cn N db p ⊢
      ⌜c.gc = B.bq ∧ c.N = N .@ "crash" ∧ FsNoErr⌝ ∗ cnReg B (some c.cg) := by
  unfold bMode cnReg
  rw [hc]; dsimp only
  iintro ⟨%h, -, -, #H⟩
  iframe H; ipureintro; exact h

/-- **The file out of its mode** (`Close`), at any mask holding its crash invariant's: the writer's
share of the `OsMeta`, bbolt's share of every byte and the closing token (`ghostVar gbq 1 ()`, the
two halves of `bq`: the closer's and the committed data's other half) give the file whole back; in
crash mode by closing the crash invariant, with the bytes outside the ranges `L` durable
(`bfile_close_dur`; with `L = []`, every byte). -/
theorem bfile_out_dur (gbq gcn : GName) (N : Namespace) (db : Loc) (p : BFile) (C : CommitSt)
    (L : List (Nat × Nat)) (m : OsMeta) (xs : List ByteG) (hl : xs.length = m.size) (E : CoPset)
    (hE : (↑(N .@ "crash") : CoPset) ⊆ E) :
    ⊢ bMode (GF := GF) gbq gcn N db p -∗ bMeta p C L m -∗ bBytes p 0 (DFrac.own 1) xs -∗
      ghostVar gbq 1 () ={E}=∗ osMeta p.ino (DFrac.own 1) m ∗ osBytes p.ino 0 (DFrac.own 1) xs ∗
        ⌜p.cs ≠ none → DurOut L xs⌝ := by
  iintro #Hmd Hm Hb Hq
  unfold bMode
  cases hc : p.cs with
  | none =>
    rw [bMeta_none hc]
    ihave Hb := (bBytes_none hc 0 (DFrac.own 1) xs).1 $$ Hb
    imodintro
    isplitl [Hm]
    · iexact Hm
    isplitl [Hb]
    · iexact Hb
    ipureintro; intro h; exact absurd rfl h
  | some c =>
    dsimp only
    icases Hmd with ⟨%hcn, #Hci, -⟩
    ihave Hd : csDone (GF := GF) c.gc $$ [Hq]
    · unfold csDone; rw [hcn.1]; iexact Hq
    imod bfile_close_dur p c hc C L m xs E (by rw [hcn.2.1]; exact hE) hl $$ Hci Hm Hb Hd
      with ⟨Hm, Hb, %hd⟩
    imodintro
    isplitl [Hm]
    · iexact Hm
    isplitl [Hb]
    · iexact Hb
    ipureintro; intro _; exact hd

/-- **The core of an open database** at `db` (design §3.8, round 2 F1), with its path `p`,
statistics pointer `sp` and receipts' base `t0`; its namespace disjoint from OsFs's (batch 37:
`Open`'s premise; `store_cells_agree` opens `pagesInv` around an OsFs step); the receipts' bound
at most `2 ^ 62` (maintainer 12, item 1: `Open`'s `ReceiptBoundLe GF (2 ^ 62)`, recorded so that
`Commit` bounds the next txid, `receipt_txid_lt`); the file's mode (`bMode`, W1). -/
def isBoltCoreP (B : BNs) (N : Namespace) (db : Loc) (p : BFile) (sp : Loc) (t0 : Nat) :
    IProp GF :=
  iprop(dblAt B db ∗ t0At B t0 p.ino ∗
    ⌜(t0 < 2 ^ 62 ∧ receiptBound GF ≤ 2 ^ 62) ∧ db ≠ null ∧ (↑N : CoPset) ## ↑osN⌝ ∗
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ osInv ∗ dbFixed B.bq N db sp ∗
    sync.isMutex db.[DB, go!"metalock"] (metaR B db p) ∗
    sync.isRWMutexGuard db.[DB, go!"mmaplock"] (Pm B db) ∗
    sync.isRWMutexGuard db.[DB, go!"statlock"] (Ps sp) ∗
    inv (pagesN N) (pagesInv B p) ∗ inv (txsN N) (txsInv B p sp t0) ∗ bMode B.bq B.cn N db p)

/-- The core of an open database (what `beginTx`, `removeTx`, `freepages` and `loadFreelist`
need). -/
def isBoltCore (B : BNs) (N : Namespace) (db : Loc) : IProp GF :=
  iprop(∃ (p : BFile) (sp : Loc) (t0 : Nat), isBoltCoreP B N db p sp t0)

/-- The full database at `db`, with its parameters. -/
def isBoltP (B : BNs) (N : Namespace) (db : Loc) (p : BFile) (sp : Loc) (t0 : Nat) :
    IProp GF :=
  iprop(isBoltCoreP B N db p sp t0 ∗ sync.isMutex db.[DB, go!"rwlock"] (rwR B db p sp t0) ∗
    threadPool.isThreadPool (poolN N) B.pool (rdPair B db sp) ∗ opnShot B)

/-- **`db` is the database `B`/`N`** (design §3.8): what `isBolt db γ` is sealed to, with
`B = bnsOf γ.gs`, `N = γ.ns`. -/
def isBoltDef (B : BNs) (N : Namespace) (db : Loc) : IProp GF :=
  iprop(∃ (p : BFile) (sp : Loc) (t0 : Nat), isBoltP B N db p sp t0)

/-! ## Lemma statements (U5) -/

omit [GooseSemantics] go_gctx hos sem in
/-- **The writer's next txid does not wrap** (maintainer 12, item 1): the writer side's receipts
`⧗ (c - t0)` (`wdbOwn`, `wdbLive`) number fewer than `receiptBound GF ≤ 2 ^ 62`, and `t0 < 2 ^ 62`
(both in `isBoltCoreP`), so `c + 1 < 2 ^ 63`. -/
theorem receipt_txid_lt (t0 c : Nat) (ht0 : t0 < 2 ^ 62) (hrb : receiptBound GF ≤ 2 ^ 62) :
    receipt (GF := GF) (c - t0) ⊢ receipt (c - t0) ∗ ⌜c + 1 < 2 ^ 63⌝ :=
  persistent_entails_left ((receipt_lt (GF := GF) (c - t0)).trans (pure_mono fun h => by omega))

/-- The core's receipt facts: `t0 < 2 ^ 62` and `receiptBound GF ≤ 2 ^ 62`. -/
theorem isBoltCoreP_receipts (B : BNs) (N : Namespace) (db : Loc) (p : BFile) (sp : Loc)
    (t0 : Nat) : isBoltCoreP (GF := GF) B N db p sp t0 ⊢ ⌜t0 < 2 ^ 62 ∧ receiptBound GF ≤ 2 ^ 62⌝ := by
  unfold isBoltCoreP
  iintro ⟨-, -, %H, -⟩
  ipureintro; exact H.1

/-- **`receipt_txid_lt` from the core**: the receipts `⧗ (c - t0)` of the core's `t0`. -/
theorem isBoltCoreP_txid_lt (B : BNs) (N : Namespace) (db : Loc) (p : BFile) (sp : Loc)
    (t0 c : Nat) :
    isBoltCoreP (GF := GF) B N db p sp t0 ∗ receipt (c - t0) ⊢ receipt (c - t0) ∗ ⌜c + 1 < 2 ^ 63⌝ := by
  iintro ⟨Hc, Hr⟩
  ihave %H := isBoltCoreP_receipts B N db p sp t0 $$ Hc
  iapply receipt_txid_lt t0 c H.1 H.2
  iexact Hr

instance isBoltCoreP_persistent (B : BNs) (N : Namespace) (db : Loc) (p : BFile) (sp : Loc)
    (t0 : Nat) : Persistent (isBoltCoreP (GF := GF) B N db p sp t0) := by
  unfold isBoltCoreP dblAt t0At dbFixed dbLogger; infer_instance

/-- The core's file mode. -/
theorem isBoltCoreP_mode (B : BNs) (N : Namespace) (db : Loc) (p : BFile) (sp : Loc) (t0 : Nat) :
    isBoltCoreP (GF := GF) B N db p sp t0 ⊢ bMode B.bq B.cn N db p := by
  unfold isBoltCoreP
  iintro ⟨-, -, -, -, -, -, -, -, -, -, -, #H⟩
  iexact H

/-- **The core's crash invariant**, if any, and its namespace outside OsFs's. -/
theorem isBoltCoreP_bfile (B : BNs) (N : Namespace) (db : Loc) (p : BFile) (sp : Loc) (t0 : Nat) :
    isBoltCoreP (GF := GF) B N db p sp t0 ⊢ bCsInv p ∗ ⌜bNsOk p⌝ := by
  unfold isBoltCoreP
  iintro ⟨-, -, %H, -, -, -, -, -, -, -, -, #Hm⟩
  have hN : (↑N : CoPset) ## ↑osN := H.2.2
  unfold bMode
  cases hc : p.cs with
  | none =>
    isplitl
    · iapply bCsInv_none hc
    · ipureintro; exact bNsOk_none hc
  | some c =>
    dsimp only
    icases Hm with ⟨%hcn, #Hci, -⟩
    iframe Hci
    ipureintro
    intro c' hc' x hx
    rw [hc] at hc'; cases hc'
    exact CoPset.in_diff.2 ⟨CoPset.subseteq_top x hx, fun hp =>
      hN x ⟨nclose_subseteq N "crash" x (hcn.2.1 ▸ hp), hx⟩⟩

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
theorem isBoltP_agree (B : BNs) (N : Namespace) (db : Loc) (p p' : BFile) (sp sp' : Loc)
    (t0 t0' : Nat) :
    isBoltP (GF := GF) B N db p sp t0 ∗ isBoltCoreP B N db p' sp' t0' ⊢ ⌜sp = sp' ∧ t0 = t0'⌝ := by
  unfold isBoltP isBoltCoreP dbFixed t0At
  iintro ⟨⟨⟨-, Ht, -, -, -, ⟨-, Hsp, -⟩, -⟩, -⟩, ⟨-, Ht', -, -, -, ⟨-, Hsp', -⟩, -⟩⟩
  icombine Ht Ht' gives %h1
  icombine Hsp Hsp' gives %h2
  ipureintro; exact ⟨h2, (Prod.mk.inj h1.2).1⟩

/-- The core's `t0At`, with its file's inode. -/
theorem isBoltCoreP_t0At (B : BNs) (N : Namespace) (db : Loc) (p : BFile) (sp : Loc) (t0 : Nat) :
    isBoltCoreP (GF := GF) B N db p sp t0 ⊢ t0At B t0 p.ino := by
  unfold isBoltCoreP
  iintro ⟨-, Ht, -⟩
  iexact Ht

/-- **The inode of `t0At` agrees** with the core's file (`boltIno`'s law, session bbolt-inv). -/
theorem isBoltCoreP_ino (B : BNs) (N : Namespace) (db : Loc) (p : BFile) (sp : Loc) (t0 t0' : Nat)
    (i : Ino) : isBoltCoreP (GF := GF) B N db p sp t0 ∗ t0At B t0' i ⊢ ⌜p.ino = i⌝ := by
  unfold isBoltCoreP t0At
  iintro ⟨⟨-, Ht, -⟩, Ht'⟩
  icombine Ht Ht' gives %h
  ipureintro; exact (Prod.mk.inj h.2).2

/-- **The database's logger is `logPtrTyped`** (batch 34; `dbFixed`'s last clause, read against the
caller's copy of the logger field). -/
theorem dbFixed_logPtrTyped (γ : GName) (N : Namespace) (db sp : Loc) (lg : GoInterface) :
    dbFixed (GF := GF) γ N db sp ⊢ db.[DB, go!"logger"] ↦□ lg -∗ ⌜logPtrTyped lg⌝ := by
  unfold dbFixed
  iintro ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, %lg', #H, %Ht⟩ #Hl
  ihave %Heq := typedPointsto_agree_wand _ _ _ _ _ $$ H Hl
  subst Heq
  ipureintro; exact Ht

end bolt

end bbolt
end EtcdGrove
end Perennial
