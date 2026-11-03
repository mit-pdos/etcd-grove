/-
The contexts bbolt's internal specs are stated over (U0b of `notes/bbolt-proof-plan.md`; design
§4.2, "the frozen shared contracts"): what a writer's internal function runs over (`wtxW`, or
`wtxLost` after a failed remap), the database side a writer holds in `Commit` (`wdbW`), a
transaction ready to close (`wtxEnd`), a reader with its view exposed (`rdTxK`), the statistics'
token (`statsTok`), and the database's parameters as one record (`BC`).

The lemma statements are the accessors the units share (the view's cells, the writer's heap
objects) and the unfolding of a writer's `boltTx` into `wtxW` and of a reader's `rdTx` into
`rdTxK`; each docstring names the unit that proves it.
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Tx
public import Proof.go_etcd_io.bbolt.Model.WOps

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

/-- **A database's parameters** (what `isBoltCoreP` takes): its decoded names, the client's
namespace, its location, its file's path, its statistics pointer and its receipts' base. -/
structure BC where
  B : BNs
  N : Namespace
  db : Loc
  p : GoString
  sp : Loc
  t0 : Nat

section ctx
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The core of the database `K` (persistent). -/
def BC.core (K : BC) : IProp GF := isBoltCoreP K.B K.N K.db K.p K.sp K.t0

/-- The full database `K` (persistent). -/
def BC.full (K : BC) : IProp GF := isBoltP K.B K.N K.db K.p K.sp K.t0

/-- **A live transaction's token for its statistics** (`txsInv` holds them; `TxStats`'s atomic
methods need it): with `m = true` a share `q` of its `ex` token (a holder of a fraction of
`boltTx`); with `m = false` its exclusive part's `done` half (the holder of `txExcl`, inside
`Commit`, `Rollback` and `DeleteBucket`; `q` unused). -/
def statsTok (r : TxReg) (m : Bool) (q : Qp) : IProp GF :=
  if m then ghostVar r.n.ex q () else ghostVar r.n.done (1 : Qp).half false

/-- The writer's state but the view's cells and its mapping fields' quarter: the database's core,
its registration, its heap `X` at `1`, its handles' fills, its handle and node registries'
auths, `tx.db`'s share, the view's `viewOf`, and its statistics' token (mode `m`). -/
def wtxCore (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) : IProp GF :=
  iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ K.core ∗
    ⌜r.db = K.db ∧ r.rw = true⌝ ∗ reg tx K.B r ∗
    wtxHeap tx (DFrac.own 1) X ∗ fills X.handles (DFrac.own 1) ∗
    ghostMapAuth r.n.bk 1 X.handles ∗ ghostMapAuth r.n.nl 1 X.nloc ∗
    tx.[Tx, go!"db"] ↦{DFrac.own (txDbQ 1)} r.db ∗ viewOf r X.v ∗ statsTok r m 1)

/-- **The writer's working state** (U0b): what a writer's internal functions run over, from its
operations through `Commit`'s rebalance and spill. It is `wtxFrac` at `1` without its facts
(which `rebalance` and `spill` break and re-establish) and without the committed data's quarter,
plus the core and the statistics' token: `wtxCore`, the base view's cells at `wq`, and the
mapping fields' writer quarter, mapped at the view's base. -/
def wtxW (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) : IProp GF :=
  iprop(wtxCore K tx r m X ∗ viewCells wq X.v ∗
    ∃ l : Nat, mapFields r.db (DFrac.own (1 : Qp).half.half) (some (X.v.base, l) : MapSt))

/-- **The writer's state after a failed remap** (the mapping lost, design §4.2): `wtxCore`, no
view cells, the mapping fields' quarter unmapped. -/
def wtxLost (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) : IProp GF :=
  iprop(wtxCore K tx r m X ∗ mapFields r.db (DFrac.own (1 : Qp).half.half) (none : MapSt))

/-- The store's writer state of a live writer on the view `v`, of the committed state `C`, before
its publish, its view lent. -/
def wLive (v : View) (C : CommitSt) : WSt := (some v, some (C.txid + 1), false, true)

/-- **The writer's database side in `Commit`** (its exclusive part's `wdbLive`, with its facts):
the store's writer state live on the view `v`, which is the committed state `w.C`'s at the
mapping. -/
def wdbW (K : BC) (tx : Loc) (v : View) (w : WDb) : IProp GF :=
  iprop(wdbLive K.B K.db K.p K.sp K.t0 tx (wLive v w.C) w ∗
    ⌜wdbOK w ∧ w.ms = some (v.base, mapLen w.ms) ∧ v = View.ofC v.base w.C⌝)

/-- The writer's database side after a failed remap: no mapping, its view returned (parked). -/
def wdbLost (K : BC) (tx : Loc) (v : View) (w : WDb) : IProp GF :=
  iprop(wdbLive K.B K.db K.p K.sp K.t0 tx (some v, some (w.C.txid + 1), false, false) w ∗
    ⌜wdbOK w ∧ w.ms = none⌝)

/-- **A write transaction ready to close** (`Tx.close`'s pre, design §4.2's three cases: before
the publish, after it, after a failed remap): the full database, the writer's records (mapped or
not), its database side live with the store's writer state `ws`, its exclusive part's other
contents (the locked `rwlock`, its page tokens, both halves of its agreed state), and the data's
quarter of the committed state `w.C` (the new one after the publish). -/
def wtxEnd (K : BC) (tx : Loc) (r : TxReg) (X : WX) (ws : WSt) (w : WDb) : IProp GF :=
  iprop(K.full ∗ (wtxW K tx r false X ∨ wtxLost K tx r false X) ∗
    wdbLive K.B K.db K.p K.sp K.t0 tx ws w ∗ sync.ownMutex K.db.[DB, go!"rwlock"] ∗
    (∃ extra : GMap Nat Unit, txShape r.n.pg X extra) ∗
    (∃ c : TxViewC, ghostVar r.n.v 1 (c, TxX.wr X)) ∗
    ghostVar K.B.st (1 : Qp).half.half (treeData w.C) ∗ ⌜wdbOK w⌝)

/-- **A reader with its view `v`** (`rdTx` with its parameters fixed: the database `K`, the view
`v`): what the read path's internal specs over readers are stated over (`rdTx_rdTxK`). -/
def rdTxK (K : BC) (tx : Loc) (src : PairSrc) (q : Qp) (T : TxView) (v : View) : IProp GF :=
  iprop(∃ (r : TxReg) (c : TxViewC) (mv : Meta) (k : Nat),
    ⌜T = TxView.ofC c ∧ r.db = K.db ∧ r.rw = false ∧ r.src = src⌝ ∗ reg tx K.B r ∗
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ K.core ∗
    ghostVar r.n.v q.half (c, TxX.rd v mv k) ∗ ghostVar r.n.ex q () ∗
    rtxFrac K.B tx r q T v mv ∗
    (if src = .loan then threadPool.isThreadPool (poolN K.N) K.B.pool (rdPair K.B K.db K.sp)
     else emp))

/-- Bytes at `p` (a page, an inline page) from the source `src`: in a page of the view `v`, or
persistent heap bytes (never stale). -/
def srcLoc (v : View) (p : Loc) (src : Src) (bs : List w8) : IProp GF :=
  match src with
  | .view => iprop(⌜inViewLoc v p bs⌝)
  | .own _ => iprop(bytesPointsto p DFrac.discard bs)
  | .stale => iprop(False)

/-- Bytes at `p` (a page, an inline page): in a page of the view `v`, or persistent heap bytes. -/
def locOwn (v : View) (p : Loc) (bs : List w8) : IProp GF :=
  iprop(⌜inViewLoc v p bs⌝ ∨ bytesPointsto p DFrac.discard bs)

/-- **A reader's bucket** `b` whose value is `bv` (the root bucket's: its header encoded), at
`dq` (the root bucket: a share of the transaction's `root` field; an opened bucket: persistent):
its fields (no caches, no root node), its header (a persistent copy, or the view's bytes), its
inline page (the view's bytes, or persistent heap bytes of a clone). -/
def rBkt (v : View) (tx b : Loc) (dq : DFrac) (bv : List w8) : IProp GF :=
  iprop(∃ (ibp pp : Loc), b.[Bucket, go!"InBucket"] ↦{dq} ibp ∗ b.[Bucket, go!"tx"] ↦{dq} tx ∗
    b.[Bucket, go!"buckets"] ↦{dq} null ∗ b.[Bucket, go!"page"] ↦{dq} pp ∗
    b.[Bucket, go!"rootNode"] ↦{dq} null ∗ b.[Bucket, go!"nodes"] ↦{dq} null ∗
    ((∃ ib : InBucket, ibp ↦□ ib ∗ ⌜ib.root' = (inBucketOf bv).root'⌝) ∨
      ⌜inViewLoc v ibp (bytesAt bv 0 16)⌝) ∗
    (if inBucketRoot bv = 0 then iprop(⌜pp ≠ null⌝ ∗ locOwn v pp (inlinePage bv))
     else iprop(⌜pp = null⌝)))

/-- The value a reader's root bucket stands for: its header (root page `v.root`, sequence `0`
as far as the readers' code cares) encoded. -/
def rootVal (v : View) : List w8 := encode (⟨W64 (v.root : Int), W64 0⟩ : InBucket)

/-- What a reader's pair source gives back at its close: the caller's `threadTok` for a pool
loan, the spare pair itself. -/
def pairBack (K : BC) : PairSrc → IProp GF
  | .loan => threadTok
  | .spare => rdPair K.B K.db K.sp

/-- **`tx.allocate(count)`'s success** for the writer's txid `txid`, from `X` (writer side's
freelist `fl`) to `X'` (`fl'`): the page `id` from the freelist (`fl.canAlloc`, the high-water
mark unchanged) or at the high-water mark (which grows by `count`), in the buffer `p`; possibly
after a remap, before which the coverage contract held (`derefOK`), `X` re-based on the new
mapping. -/
def allocRes (X X' : WX) (fl fl' : FLPg) (txid : w64) (count : Nat) (p : Loc) (id : w64) :
    Prop :=
  0 < count ∧ p ≠ null ∧
  ∃ Xr, (Xr = X ∨ (derefOK X ∧ ∃ b, Xr = X.rebase b)) ∧
    ((fl.canAlloc id count ∧ fl' = fl.alloc txid id count ∧
        X' = Xr.addPage id p count X.t.mv.pgid') ∨
     (id = X.t.mv.pgid' ∧ fl' = fl ∧ id.toNat + count < 2 ^ 62 ∧
        X' = Xr.addPage id p count (id + W64 (count : Int))))

/-- A remap's effect on the writer side (`DB.mmap` through `DB.allocate`): the committed state,
freelist and slots' bytes kept; the mapping, the file's maps and the `W` slots the new mapping's. -/
def wdbRemap (w w' : WDb) : Prop :=
  w'.C = w.C ∧ w'.fl = w.fl ∧ w'.fli = w.fli ∧ w'.f = w.f ∧ w'.fd = w.fd ∧
  w'.m.size = w.m.size ∧ ∀ s, s ∈ w.W → s ∈ w'.W ∧ w'.wb s = w.wb s

/-! ## Lemma statements -/

/-- **A page of the view, read** (U6 proves; every reader of a page uses it): its bytes at
the view's cells' fraction, and back. -/
theorem viewCells_page_acc (q : Qp) (v : View) (id : Nat) (pg : List w8)
    (h : v.pages !! id = some pg) :
    viewCells (GF := GF) q v ⊢ bytesPointsto (pageLoc v id) (DFrac.own q) pg ∗
      (bytesPointsto (pageLoc v id) (DFrac.own q) pg -∗ viewCells q v) := by
  sorry

/-- **Bytes of the view at a location, read** (U6): any bytes `inViewLoc` places in a page of the
view (an inline page, a key), at some fraction, and back. -/
theorem viewCells_loc_acc (q : Qp) (v : View) (l : Loc) (bs : List w8) (h : inViewLoc v l bs) :
    viewCells (GF := GF) q v ⊢ ∃ dq : DFrac, bytesPointsto l dq bs ∗
      (bytesPointsto l dq bs -∗ viewCells q v) := by
  sorry

/-- **Slices of the view, read together** (U6; `node.write`'s and `bytes.Compare`'s callers):
every slice of the list at one fraction, and back. -/
theorem viewCells_slices_acc (q : Qp) (v : View) (L : List (GoSlice × List w8))
    (h : ∀ x ∈ L, inViewAt v x.1 x.2) :
    viewCells (GF := GF) q v ⊢ ∃ dq : DFrac, ([∗list] x ∈ L, x.1 ↦*{dq} x.2) ∗
      (([∗list] x ∈ L, x.1 ↦*{dq} x.2) -∗ viewCells q v) := by
  sorry

/-- **A node of the writer's heap, out and back** (U5): its object at `dq`, and the heap with
any new record of it. -/
theorem wtxHeap_node_acc (tx : Loc) (dq : DFrac) (X : WX) (bl l : Loc) (r : NRec)
    (hn : X.node bl l = some r) (ho : X.t.objs !! l = some (WObj.node bl r)) (hl : l ∈ X.live) :
    wtxHeap (GF := GF) tx dq X ⊢ objOwn X.v l dq true (WObj.node bl r) ∗
      (∀ r', objOwn X.v l dq true (WObj.node bl r') -∗ wtxHeap tx dq (X.setNode bl l r')) := by
  sorry

/-- **A bucket of the writer's heap, out and back** (U5). -/
theorem wtxHeap_bkt_acc (tx : Loc) (dq : DFrac) (X : WX) (bl : Loc) (B : BRec)
    (hb : X.t.bs !! bl = some B) (hl : bl ∈ X.live) :
    wtxHeap (GF := GF) tx dq X ⊢ objOwn X.v bl dq true (WObj.bkt B) ∗
      (∀ B', objOwn X.v bl dq true (WObj.bkt B') -∗
        wtxHeap tx dq (X.setBkt bl { B' with ns := B.ns })) := by
  sorry

/-- **A whole write transaction is its working state** (U5 proves; U7, U8, U9, U10 open their
`boltTx` with it): `wtxW` in mode `true`, its agreed state's half, the full database, the
committed data's quarter, and `wtxFrac`'s facts. -/
theorem boltTxDef_wtxW (B : BNs) (N : Namespace) (tx : Loc) (T : TxView) (hrw : T.rw = true) :
    boltTxDef (GF := GF) B N tx 1 T ⊣⊢
      ∃ (K : BC) (r : TxReg) (c : TxViewC) (X : WX),
        ⌜K.B = B ∧ K.N = N ∧ T = TxView.ofC c⌝ ∗ K.full ∗
        ghostVar r.n.v (1 : Qp).half (c, TxX.wr X) ∗ wtxW K tx r true X ∗
        ghostVar B.st (1 : Qp).half.half T.base ∗
        ⌜wOK X ∧ T.cur = wtxData X ∧ T.base = X.v.data ∧ gensOK T X⌝ := by
  sorry

/-- **A reader is a reader with its view** (U6 proves; the read path's internal reader specs are
over `rdTxK`). -/
theorem rdTx_rdTxK (B : BNs) (N : Namespace) (tx : Loc) (src : PairSrc) (q : Qp) (T : TxView) :
    rdTx (GF := GF) B N tx src q T ⊣⊢
      ∃ (K : BC) (v : View), ⌜K.B = B ∧ K.N = N⌝ ∗ rdTxK K tx src q T v := by
  sorry

/-- **A reader's root bucket** (U6): `tx.root` at the reader's fraction, as `rBkt` of the view's
root, and back. -/
theorem rdTxK_root (K : BC) (tx : Loc) (src : PairSrc) (q : Qp) (T : TxView) (v : View) :
    rdTxK (GF := GF) K tx src q T v ⊢ rBkt v tx (txRoot (GF := GF) tx) (DFrac.own q) (rootVal v) ∗
      (rBkt v tx (txRoot (GF := GF) tx) (DFrac.own q) (rootVal v) -∗ rdTxK K tx src q T v) := by
  sorry

/-- A reader's view: `T` is its snapshot, of a `treeOK` committed state (U6). -/
theorem rdTxK_view (K : BC) (tx : Loc) (src : PairSrc) (q : Qp) (T : TxView) (v : View) :
    rdTxK (GF := GF) K tx src q T v ⊢ ⌜T = TxView.ro v.data ∧ viewWF v⌝ := by
  sorry

end ctx

end bbolt
end EtcdGrove
end Perennial
