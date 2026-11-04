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

instance BC.core_persistent (K : BC) : Persistent (K.core (GF := GF)) := by
  unfold BC.core; infer_instance

instance BC.full_persistent (K : BC) : Persistent (K.full (GF := GF)) := by
  unfold BC.full isBoltP; infer_instance

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
    ⌜r.db = K.db ∧ r.rw = true ∧ tx ≠ null ∧ X.t.t.managed' = false ∧
      txRoot (GF := GF) tx ≠ null⌝ ∗ reg tx K.B r ∗
    wtxHeap tx (DFrac.own 1) X ∗ fills X.handles (DFrac.own 1) ∗
    ghostMapAuth r.n.bk 1 X.handles ∗ ghostMapAuth r.n.nl 1 X.nloc ∗
    tx.[Tx, go!"db"] ↦{DFrac.own (txDbQ 1)} r.db ∗ viewOf r X.v ∗ statsTok r m 1)

/-- **The writer's working state** (U0b): what a writer's internal functions run over, from its
operations through `Commit`'s rebalance and spill. It is `wtxFrac` at `1` without its facts
(which `rebalance` and `spill` break and re-establish) and without the committed data's quarter,
plus the core and the statistics' token: `wtxCore`, the base view's cells at `wq`, and the
mapping fields' writer quarter, mapped at the view's base, every page of the view inside the
mapping (so that `Tx.page` of a view page meets `id·4096 < 0xFFFFFFFFFFFF`, with `mapFields`'
length bound: `pageIdx_lt_maxMap`; a page of `tx.pages` needs no bound). -/
def wtxW (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) : IProp GF :=
  iprop(wtxCore K tx r m X ∗ viewCells wq X.v ∗
    ∃ l : Nat, mapFields r.db (DFrac.own (1 : Qp).half.half) (some (X.v.base, l) : MapSt) ∗
      ⌜∀ id pg, X.v.pages !! id = some pg → (id + 1) * 4096 ≤ l⌝)

/-- **The writer's state after a failed remap** (the mapping lost, design §4.2): `wtxCore`, no
view cells, the mapping fields' quarter unmapped. -/
def wtxLost (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) : IProp GF :=
  iprop(wtxCore K tx r m X ∗ mapFields r.db (DFrac.own (1 : Qp).half.half) (none : MapSt))

/-- The live writer's txid, the next after the committed state's (`tx.meta.txid`). -/
def WDb.wtxid (w : WDb) : w64 := W64 ((w.C.txid + 1 : Nat) : Int)

/-- The writer side with the freelist `fl`. -/
def WDb.withFl (w : WDb) (fl : FLPg) : WDb := { w with fl := fl }

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

/-- What a reader's pair source gives back at its close: the caller's `threadTok` for a pool
loan, the spare pair itself. -/
def pairBack (K : BC) : PairSrc → IProp GF
  | .loan => threadTok
  | .spare => rdPair K.B K.db K.sp

/-- A remap's effect on the writer side (`DB.mmap` through `DB.allocate`): the committed state,
freelist and slots' bytes kept; the mapping, the file's maps and the `W` slots the new mapping's. -/
def wdbRemap (w w' : WDb) : Prop :=
  w'.C = w.C ∧ w'.fl = w.fl ∧ w'.fli = w.fli ∧ w'.f = w.f ∧ w'.fd = w.fd ∧
  w'.m.size = w.m.size ∧ ∀ s, s ∈ w.W → s ∈ w'.W ∧ w'.wb s = w.wb s

/-- **`dereference`'s effect** (`tx.root.dereference()`): every live node's keys and values
copied to the heap (the coverage contract, `derefOK`), by data unchanged; nothing else
(`derefStep`, batch 12: so that the records' structure, which `allocate`'s premises
`derefPre`/`liveReach` are about, is known after a remap). -/
def derefRel (X X' : WX) : Prop :=
  derefOK X' ∧ X'.v = X.v ∧ X'.live = X.live ∧ X'.handles = X.handles ∧ X'.nloc = X.nloc ∧
  X'.rl = X.rl ∧ X'.t.mv = X.t.mv ∧ X'.t.pm = X.t.pm ∧ X'.t.bufs = X.t.bufs ∧
  (∀ bl l, (X'.node bl l).map (fun r => (r.ws.map wDat, r.key, r.nv.pgid', r.nv.isLeaf')) =
    (X.node bl l).map (fun r => (r.ws.map wDat, r.key, r.nv.pgid', r.nv.isLeaf'))) ∧
  (∀ bl pid, (ltree X' bl pid).map (fun x => (x.1, x.2.map wDat)) =
    (ltree X bl pid).map (fun x => (x.1, x.2.map wDat))) ∧
  wtxData X' = wtxData X ∧ (wOK X → wOK X') ∧ derefStep X X'

/-- **`tx.allocate(count)`'s success** for the writer's txid `txid`, from `X` (writer side's
freelist `fl`) to `X'` (`fl'`): the page `id` from the freelist (`fl.canAlloc`, the high-water
mark unchanged) or at the high-water mark (which grows by `count`), in the buffer `p`; possibly
after a remap, before which `dereference` ran (`derefRel`, the coverage contract), the records
re-based on the new mapping. -/
def allocRes (X X' : WX) (fl fl' : FLPg) (txid : w64) (count : Nat) (p : Loc) (id : w64) :
    Prop :=
  0 < count ∧ p ≠ null ∧
  ∃ Xr, (Xr = X ∨ ∃ Xd b, derefRel X Xd ∧ Xr = Xd.rebase b) ∧
    ((fl.canAlloc id count ∧ fl' = fl.alloc txid id count ∧
        X' = Xr.addPage id p count X.t.mv.pgid') ∨
     (id = X.t.mv.pgid' ∧ fl' = fl ∧ id.toNat + count < 2 ^ 62 ∧
        X' = Xr.addPage id p count (id + W64 (count : Int))))

-- `allocate` keeps its own premises: U9c's `allocRes_derefPre'` and `derefRel_rebase_derefPre'`
-- (`Spill/AllocDeref`, proved, with `objsDisj X.t`: batch 27; the stubs here were false without it).

/-- **`DB.grow`'s effect on the writer side**: the file's size grows (or stays), its pages'
bytes kept; nothing else changes (the new slots inside the mapping become `W` slots). -/
def wdbGrown (w w' : WDb) : Prop :=
  w'.C = w.C ∧ w'.fl = w.fl ∧ w'.ms = w.ms ∧ w'.fli = w.fli ∧ w'.f = w.f ∧ w'.fd = w.fd ∧
  w'.junk = w.junk ∧ w'.m.maps = w.m.maps ∧ w.m.size ≤ w'.m.size ∧
  ∀ s, s ∈ w.W → s ∈ w'.W ∧ w'.wb s = w.wb s

/-! ## Lemma statements -/

/-- A registration is persistent. -/
instance reg_persistent' (tx : Loc) (B : BNs) (r : TxReg) :
    Persistent (reg (GF := GF) tx B r) := by
  unfold reg; infer_instance

private theorem isBoltCoreP_pkgInit (B : BNs) (N : Namespace) (db : Loc) (p : GoString) (sp : Loc)
    (t0 : Nat) :
    isBoltCoreP (GF := GF) B N db p sp t0 ⊢ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt := by
  unfold isBoltCoreP
  iintro ⟨-, -, -, H, -⟩
  iexact H

private theorem bytesPointsto_sub_acc (l : Loc) (dq : DFrac) (pg bs : List w8) (off : Nat)
    (hlen : off + bs.length ≤ pg.length) (hbs : bytesAt pg off bs.length = bs) :
    bytesPointsto (GF := GF) l dq pg ⊢ bytesPointsto (l +ₗ (off : Int)) dq bs ∗
      (bytesPointsto (l +ₗ (off : Int)) dq bs -∗ bytesPointsto l dq pg) := by
  have e : pg = pg.take off ++ (bs ++ (pg.drop off).drop bs.length) := by
    unfold bytesAt at hbs
    conv => lhs; rw [← List.take_append_drop off pg]
    conv => lhs; arg 2; rw [← List.take_append_drop bs.length (pg.drop off), hbs]
  have hk : (pg.take off).length = off := by simp; omega
  have Hs := (bytesPointsto_app (GF := GF) l dq (pg.take off) (bs ++ (pg.drop off).drop bs.length))
  have Hs2 := (bytesPointsto_app (GF := GF) (l +ₗ ((pg.take off).length : Int)) dq bs
    ((pg.drop off).drop bs.length))
  rw [← e, hk] at Hs
  rw [hk] at Hs2
  iintro Hp
  icases Hs.1 $$ Hp with ⟨H1, Hp⟩
  icases Hs2.1 $$ Hp with ⟨H2, H3⟩
  iframe H2
  iintro H2
  iapply Hs.2
  iframe H1
  iapply Hs2.2
  iframe


/-- **A page of the view, read** (U6 proves; every reader of a page uses it): its bytes at
the view's cells' fraction, and back. -/
theorem viewCells_page_acc (q : Qp) (v : View) (id : Nat) (pg : List w8)
    (h : v.pages !! id = some pg) :
    viewCells (GF := GF) q v ⊢ bytesPointsto (pageLoc v id) (DFrac.own q) pg ∗
      (bytesPointsto (pageLoc v id) (DFrac.own q) pg -∗ viewCells q v) := by
  unfold viewCells pageLoc
  exact (BigSepM.bigSepM_lookup_acc h).1

/-- **Bytes of the view at a location, read** (U6): any bytes `inViewLoc` places in a page of the
view (an inline page, a key), at some fraction, and back. -/
theorem viewCells_loc_acc (q : Qp) (v : View) (l : Loc) (bs : List w8) (h : inViewLoc v l bs) :
    viewCells (GF := GF) q v ⊢ ∃ dq : DFrac, bytesPointsto l dq bs ∗
      (bytesPointsto l dq bs -∗ viewCells q v) := by
  obtain ⟨id, pg, off, hpg, hlen, hbs, rfl⟩ := h
  have Ha := bytesPointsto_sub_acc (GF := GF) (v.base +ₗ ((id * 4096 : Nat) : Int)) (DFrac.own q)
    pg bs off hlen hbs
  rw [loc_add_assoc,
    show (((id * 4096 : Nat) : Int) + (off : Int)) = ((id * 4096 + off : Nat) : Int) by omega] at Ha
  iintro Hv
  unfold viewCells
  icases (BigSepM.bigSepM_lookup_acc hpg).1 $$ Hv with ⟨Hp, Hback⟩
  icases Ha $$ Hp with ⟨H2, Hpb⟩
  iexists DFrac.own q
  iframe H2
  iintro H2
  iapply Hback
  iapply Hpb
  iexact H2

/-- **Slices of the view, read together** (U6; `node.write`'s and `bytes.Compare`'s callers):
every slice of the list at one fraction, and back. -/
theorem viewCells_slices_acc (q : Qp) (v : View) (L : List (GoSlice × List w8))
    (h : ∀ x ∈ L, inViewAt v x.1 x.2) :
    viewCells (GF := GF) q v ⊢ ∃ dq : DFrac, ([∗list] x ∈ L, x.1 ↦*{dq} x.2) ∗
      (([∗list] x ∈ L, x.1 ↦*{dq} x.2) -∗ viewCells q v) := by
  sorry

-- `wtxHeap_node_acc` (false: a new record's parent could be itself): U8's `wtxHeap_setNode`
-- (`Rebalance/Heap.lean`); `wtxHeap_bkt_acc` (with the new record's `tx` field): U5's
-- `Txn/Heap.lean` (batch 11).

private instance isBoltP_persistent_c (B : BNs) (N : Namespace) (db : Loc) (p : GoString)
    (sp : Loc) (t0 : Nat) : Persistent (isBoltP (GF := GF) B N db p sp t0) := by
  unfold isBoltP; infer_instance

private instance BC_full_persistent_c (K : BC) : Persistent (K.full (GF := GF)) := by
  unfold BC.full isBoltP; infer_instance

private instance viewOf_persistent_c (r : TxReg) (v : View) :
    Persistent (viewOf (GF := GF) r v) := by
  unfold viewOf; infer_instance

private theorem QpMul_one_left_c (q : Qp) : QpMul 1 q = q :=
  Subtype.ext (by simp [QpMul])

open Iris.ProofMode in
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
  unfold boltTxDef
  simp only [hrw, ↓reduceIte]
  constructor
  · iintro ⟨%db, %p, %sp, %t0, %r, %c, %X, %Hc, #Hreg, #Hb, Hv, Hex, Hw⟩
    unfold wtxFrac
    simp only [QpMul_one_left_c]
    icases Hw with ⟨Hh, Hf, Hvc, Hst, Hbk, Hnl, Hdb, ⟨%l, Hmf, %Hl⟩, #Hvo, %Hfacts⟩
    iexists ⟨B, N, db, p, sp, t0⟩, r, c, X
    obtain ⟨hT, hdb, hrw'⟩ := Hc
    obtain ⟨h1, -, h3, h4, h5, h6⟩ := Hfacts
    isplitr
    · ipureintro; exact ⟨rfl, rfl, hT⟩
    unfold BC.full
    iframe Hb Hv Hst
    isplitl [Hh Hf Hvc Hbk Hnl Hdb Hex Hmf]
    · unfold wtxW wtxCore statsTok BC.core
      simp only [↓reduceIte]
      ihave #Hpk : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt $$ []
      · unfold isBoltP isBoltCoreP
        icases Hb with ⟨⟨-, -, -, $, -⟩, -⟩
      ihave #Hc : isBoltCoreP B N db p sp t0 $$ []
      · unfold isBoltP; icases Hb with ⟨$, -⟩
      iframe Hpk Hc Hreg Hh Hf Hbk Hnl Hvc Hvo Hex
      iframe Hdb
      isplitr
      · ipureintro; exact ⟨hdb, hrw', h6⟩
      iexists l; iframe Hmf; ipureintro; exact Hl
    ipureintro; exact ⟨h1, h3, h4, h5⟩
  · iintro ⟨%K, %r, %c, %X, %HK, #Hb, Hv, Hw, Hst, %Hfacts⟩
    obtain ⟨rfl, rfl, hT⟩ := HK
    unfold wtxW wtxCore statsTok
    simp only [↓reduceIte]
    icases Hw with ⟨⟨-, -, %Hr, #Hreg, Hh, Hf, Hbk, Hnl, Hdb, #Hvo, Hex⟩, Hvc, %l, Hmf, %Hl⟩
    iexists K.db, K.p, K.sp, K.t0, r, c, X
    isplitr
    · ipureintro; exact ⟨hT, Hr.1, Hr.2.1⟩
    unfold BC.full
    iframe Hreg Hb Hv Hex
    unfold wtxFrac
    simp only [QpMul_one_left_c]
    iframe Hh Hf Hvc Hst Hbk Hnl Hvo
    isplitl [Hdb]
    · iexact Hdb
    isplitl [Hmf]
    · iexists l; iframe Hmf; ipureintro; exact Hl
    ipureintro
    exact ⟨Hfacts.1, hrw, Hfacts.2.1, Hfacts.2.2.1, Hfacts.2.2.2, Hr.2.2⟩

/-- **A reader is a reader with its view** (U6 proves; the read path's internal reader specs are
over `rdTxK`). -/
theorem rdTx_rdTxK (B : BNs) (N : Namespace) (tx : Loc) (src : PairSrc) (q : Qp) (T : TxView) :
    rdTx (GF := GF) B N tx src q T ⊣⊢
      ∃ (K : BC) (v : View), ⌜K.B = B ∧ K.N = N⌝ ∗ rdTxK K tx src q T v := by
  constructor
  · unfold rdTx
    iintro ⟨%db, %p, %sp, %t0, %r, %c, %v, %mv, %k, %Hc, #Hreg, #Hcore, Hv, Hex, Hrt, Hpool⟩
    iexists ⟨B, N, db, p, sp, t0⟩, v
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    unfold rdTxK BC.core
    iexists r, c, mv, k
    obtain ⟨h1, h2, h3, h4⟩ := Hc
    isplitr
    · ipureintro; exact ⟨h1, h2, h3, h4⟩
    ihave #Hpk := isBoltCoreP_pkgInit B N db p sp t0 $$ Hcore
    simp only
    iframe; iframe #
  · unfold rdTx rdTxK BC.core
    iintro ⟨%K, %v, %HK, %r, %c, %mv, %k, %Hc, #Hreg, -, #Hcore, Hv, Hex, Hrt, Hpool⟩
    obtain ⟨rfl, rfl⟩ := HK
    iexists K.db, K.p, K.sp, K.t0, r, c, v, mv, k
    isplitr
    · ipureintro; exact Hc
    iframe; iframe #

/-- **A reader's root bucket** (U6): `tx.root` at the reader's fraction, as `rBkt` of the view's
root, and back. -/
theorem rdTxK_root (K : BC) (tx : Loc) (src : PairSrc) (q : Qp) (T : TxView) (v : View) :
    rdTxK (GF := GF) K tx src q T v ⊢ rBkt v tx (txRoot (GF := GF) tx) (DFrac.own q) (rootVal v) ∗
      (rBkt v tx (txRoot (GF := GF) tx) (DFrac.own q) (rootVal v) -∗ rdTxK K tx src q T v) := by
  unfold rdTxK rtxFrac
  iintro ⟨%r, %c, %mv, %k, %Hc, Hreg, Hpk, Hcore, Hv, Hex,
    ⟨%t, Hw, Hm, Hme, Hrb, Hfp, Hpg, Hch, Hwf, Hdb, Hmv, Hvc, Hmap, Hvo, %Hf⟩, Hpool⟩
  isplitl [Hrb]
  · iexact Hrb
  iintro Hrb
  iexists r, c, mv, k
  isplitr
  · ipureintro; exact Hc
  iframe
  ipureintro; exact Hf

/-- A reader's view: `T` is its snapshot, of a `treeOK` committed state (U6). -/
theorem rdTxK_view (K : BC) (tx : Loc) (src : PairSrc) (q : Qp) (T : TxView) (v : View) :
    rdTxK (GF := GF) K tx src q T v ⊢ ⌜T = TxView.ro v.data ∧ viewWF v⌝ := by
  unfold rdTxK rtxFrac
  iintro ⟨%r, %c, %mv, %k, -, -, -, -, -, -, ⟨%t, -, -, -, -, -, -, -, -, -, -, -, -, -, %Hf⟩, -⟩
  ipureintro; exact ⟨Hf.1, Hf.2.1⟩

end ctx

end bbolt
end EtcdGrove
end Perennial
