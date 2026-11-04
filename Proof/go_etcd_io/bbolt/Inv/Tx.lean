/-
The transaction predicates (U0a of `notes/bbolt-proof-plan.md`; design §3.10, §3.13): the
definitions `Spec/go_etcd_io/bbolt/Api.lean` seals its transaction predicates to (`boltTxDef`,
`txDBDef`, `txDoneDef`, `boltBktDef`, `txBytesDef`, `boltCurDef`), the internal reader predicate
over the core (`rdTx`, A2), their parts (`rtxFrac`, `wtxFrac`, `viewOf`, `nodeLoc`, `handleFrag`)
and every `Api.lean` law restated over the definitions (U5, U6 prove them).

Each takes the name's decoded names `B` and namespace `N` (`bnsOf γ.gs`, `γ.ns`) in place of `γ`.
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Bolt
public import Proof.go_etcd_io.bbolt.Model.Cursor
public import Proof.go_etcd_io.bbolt.Model.WOps

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section tx
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `tx`'s share of `tx.db` at fraction `q` (`q · ¾`: `txsInv` holds the other quarter). -/
def txDbQ (q : Qp) : Qp := QpMul q (1 : Qp).half + QpMul q (1 : Qp).half.half

/-- The transaction's view at the base `v.base` is `v` (persistent, agreeing). -/
def viewOf (r : TxReg) (v : View) : IProp GF := iprop(v.base ↪[r.n.vw]□ v)

/-- A cursor stack element's node is in the writer's node-location registry (`nl`) at `y`. -/
def nodeLoc (r : TxReg) (nl : Loc → Option (Loc × Nat)) (e : elemRef) : IProp GF :=
  if e.node' = null then iprop(emp)
  else iprop(∃ y, ⌜nl e.node' = some y⌝ ∗ e.node' ↪[r.n.nl]□ y)

/-- The handle `b` of bucket `n` at generation `g` (a writer's registry, or a reader's at
generation 0). -/
def handleFrag (r : TxReg) (b : Loc) (n : GoString) (g : Nat) : IProp GF :=
  if r.rw then iprop(b ↪[r.n.bk]□ (n, g))
  else iprop(⌜g = 0⌝ ∗ ∃ h : InBucket, b ↪[r.n.rbk]□ ((n, h) : RHandle))

/-- Bytes at `p` (a page, an inline page): in a page of the view `v`, or persistent heap bytes. -/
def locOwn (v : View) (p : Loc) (bs : List w8) : IProp GF :=
  iprop(⌜inViewLoc v p bs⌝ ∨ bytesPointsto p DFrac.discard bs)

/-- **A reader's bucket** `b` whose value is `bv` (the root bucket's: its header encoded), at
`dq` (the root bucket: a share of the transaction's `root` field; an opened bucket: persistent):
its fields (no caches, no root node), its header (a persistent copy, or the view's bytes), its
inline page (the view's bytes, or persistent heap bytes of a clone). Its `FillPercent` is not
here (a reader never reads it). -/
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

/-- **A reader's part at fraction `q`** (design §3.10): its fields (`db` at `q · ¾`), its meta
copy, its view's cells at `q · rq`, `mmaplock`'s fields at `q · rfrac` (its `mtok` deposited:
`PmNoTok`'s parts, at the view's mapping `(v.base, l)`, every page of the view inside it), and
its view's facts: `T` is the snapshot of the view. Its root bucket (`Tx.init`'s `tx.root`, what
every read starts from) is `rBkt` of the view's root (U6 fix: the header may be the view's
bytes, as for any reader bucket, so that `rdTxK_root`'s wand takes back any `rBkt`), with its
`FillPercent`; its page cache is nil. -/
def rtxFrac (B : BNs) (tx : Loc) (r : TxReg) (q : Qp) (T : TxView) (v : View) (mv : Meta) :
    IProp GF :=
  iprop(∃ t : Tx,
    tx.[Tx, go!"writable"] ↦{DFrac.own q} false ∗ tx.[Tx, go!"managed"] ↦{DFrac.own q} t.managed' ∗
    tx.[Tx, go!"meta"] ↦{DFrac.own q} t.meta' ∗
    rBkt v tx (txRoot (GF := GF) tx) (DFrac.own q) (rootVal v) ∗
    (∃ f : w64, (txRoot (GF := GF) tx).[Bucket, go!"FillPercent"] ↦{DFrac.own q} f) ∗
    tx.[Tx, go!"pages"] ↦{DFrac.own q} t.pages' ∗
    tx.[Tx, go!"commitHandlers"] ↦{DFrac.own q} t.commitHandlers' ∗
    tx.[Tx, go!"WriteFlag"] ↦{DFrac.own q} t.WriteFlag' ∗
    tx.[Tx, go!"db"] ↦{DFrac.own (txDbQ q)} r.db ∗ t.meta' ↦{DFrac.own q} mv ∗
    viewCells (QpMul q rq) v ∗
    (∃ l : Nat, ghostVar B.map (QpMul q sync.rfrac).half.half (some (v.base, l) : MapSt) ∗
      mapFields r.db (DFrac.own (QpMul q sync.rfrac).half) (some (v.base, l) : MapSt) ∗
      ⌜∀ id pg, v.pages !! id = some pg → (id + 1) * 4096 ≤ l⌝) ∗
    viewOf r v ∗
    ⌜T = TxView.ro v.data ∧ viewWF v ∧ mv.txid'.toNat = v.txid ∧ t.pages' = null⌝)

/-- The writer's handles' generations (the `buckets` caches): every handle's generation is at
most its name's, and the opened bucket of a name is its current handle. -/
def gensOK (T : TxView) (X : WX) : Prop :=
  (∀ b n g, X.handles !! b = some (n, g) → g ≤ T.gen n) ∧
  ∀ n b, bktLoc X n = some b → X.handles !! b = some (n, T.gen n)

/-- **A writer's part at fraction `q`** (design §3.10, F3): its heap at `q`, its handles'
`FillPercent`s at `q`, its base view's cells at `q · wq`, the library's quarter of the committed
data at `q`, its handle and node registries' auths at `q`, its fields' share, `mmaplock`'s
mapping fields at `q · ¼`, and its facts. -/
def wtxFrac (B : BNs) (tx : Loc) (r : TxReg) (q : Qp) (T : TxView) (X : WX) : IProp GF :=
  iprop(wtxHeap tx (DFrac.own q) X ∗ fills X.handles (DFrac.own q) ∗
    viewCells (QpMul q wq) X.v ∗ ghostVar B.st (QpMul q (1 : Qp).half.half) T.base ∗
    ghostMapAuth r.n.bk q X.handles ∗ ghostMapAuth r.n.nl q X.nloc ∗
    tx.[Tx, go!"db"] ↦{DFrac.own (txDbQ q)} r.db ∗
    (∃ l : Nat, mapFields r.db (DFrac.own (QpMul q (1 : Qp).half.half))
      (some (X.v.base, l) : MapSt)) ∗
    viewOf r X.v ∗
    ⌜wOK X ∧ T.rw = true ∧ T.cur = wtxData X ∧ T.base = X.v.data ∧ gensOK T X⌝)

/-- **A read transaction over the core** (A2, round 4 N5): `boltTx`'s reader part with
`isBoltCore` in place of `isBolt`, its pair's source `src` (a pool loan carries the pool). -/
def rdTx (B : BNs) (N : Namespace) (tx : Loc) (src : PairSrc) (q : Qp) (T : TxView) :
    IProp GF :=
  iprop(∃ (db : Loc) (p : GoString) (sp : Loc) (t0 : Nat) (r : TxReg) (c : TxViewC) (v : View)
      (mv : Meta) (k : Nat),
    ⌜T = TxView.ofC c ∧ r.db = db ∧ r.rw = false ∧ r.src = src⌝ ∗ reg tx B r ∗
    isBoltCoreP B N db p sp t0 ∗ ghostVar r.n.v q.half (c, TxX.rd v mv k) ∗
    ghostVar r.n.ex q () ∗ rtxFrac B tx r q T v mv ∗
    (if src = .loan then threadPool.isThreadPool (poolN N) B.pool (rdPair B db sp) else emp))

/-- **`tx` is a transaction of `B`/`N` with the view `T` at fraction `q`** (design §3.10; what
`boltTx tx γ q T` is sealed to): a writer's registration, database and part; or a reader's
`rdTx` with a pool loan, and the database. -/
def boltTxDef (B : BNs) (N : Namespace) (tx : Loc) (q : Qp) (T : TxView) : IProp GF :=
  if T.rw then
    iprop(∃ (db : Loc) (p : GoString) (sp : Loc) (t0 : Nat) (r : TxReg) (c : TxViewC) (X : WX),
      ⌜T = TxView.ofC c ∧ r.db = db ∧ r.rw = true⌝ ∗ reg tx B r ∗ isBoltP B N db p sp t0 ∗
      ghostVar r.n.v q.half (c, TxX.wr X) ∗ ghostVar r.n.ex q () ∗ wtxFrac B tx r q T X)
  else iprop(∃ db : Loc, rdTx B N tx .loan q T ∗ isBoltDef B N db)

/-- `tx` is a transaction of the database `db` (persistent; `Tx.DB` compares physical values,
design §3.10). -/
def txDBDef (tx db : Loc) : IProp GF :=
  iprop(∃ (B : BNs) (N : Namespace) (r : TxReg), isBoltDef B N db ∗ reg tx B r ∗ ⌜r.db = db⌝)

/-- `tx` was committed or rolled back: its statistics, frozen. -/
def txDoneDef (tx : Loc) : IProp GF := iprop(∃ s : TxStats, tx.[Tx, go!"stats"] ↦□ s)

/-- `b` is `tx`'s handle of bucket `n` at generation `g` (persistent); a reader's handle also
holds its bucket's fields, persistently (`rBkt … DFrac.discard`, what `Bucket.Bucket_r` gives for
a top-level bucket `n` of the reader's view), so that the public reader triples reach them. -/
def boltBktDef (B : BNs) (tx b : Loc) (n : GoString) (g : Nat) : IProp GF :=
  iprop(∃ r : TxReg, reg tx B r ∗ b.[Bucket, go!"tx"] ↦□ tx ∗ handleFrag r b n g ∗
    (if r.rw then iprop(emp)
     else iprop(∃ (v : View) (bv : List w8), viewOf r v ∗ rBkt v tx b DFrac.discard bv ∗
       ⌜bktEntry v.pages (rootVal v) n bv⌝)))

/-- The slice `s` holds `b` while `tx` is live: persistent heap bytes, or bytes of the
transaction's view. -/
def txBytesDef (B : BNs) (tx : Loc) (s : GoSlice) (b : GoString) : IProp GF :=
  iprop(s ↦*□ b ∨ ∃ (r : TxReg) (v : View), reg tx B r ∗ viewOf r v ∗ ⌜inViewAt v s b⌝)

/-- **A cursor** (timeless; design §3.13, B5): its handle, its stack, and the stack's position
relative to the view (a reader's) or to the base view and the node registry (a writer's). -/
def boltCurDef (B : BNs) (tx c : Loc) (T : TxView) (es : List BoltEnt) (pos : Option Nat) :
    IProp GF :=
  iprop(∃ (r : TxReg) (b : Loc) (n : GoString) (g : Nat) (stk : GoSlice) (els : List elemRef)
      (v : View),
    reg tx B r ∗ handleFrag r b n g ∗ c ↦ (Cursor.mk b stk) ∗ stk ↦* els ∗
    ownSliceCap elemRef stk (DFrac.own 1) ∗ viewOf r v ∗
    ⌜es = bktEnts ((T.cur !! n).getD ∅) ∧ g = T.gen n⌝ ∗
    (if r.rw then iprop(∃ nl : Loc → Option (Loc × Nat), ([∗list] e ∈ els, nodeLoc r nl e) ∗
        ⌜wStackAt nl v T b n els pos⌝)
     else iprop(⌜rStackAt v n els pos⌝)))

/-! ## The laws over the definitions (U5, U6) -/

theorem boltTxDef_later (B : BNs) (N : Namespace) (db tx : Loc) (q : Qp) (T : TxView) :
    isBoltDef (GF := GF) B N db ⊢ ▷ boltTxDef B N tx q T -∗ ◇ boltTxDef B N tx q T := by
  sorry

theorem boltTxDef_fractional (B : BNs) (N : Namespace) (tx : Loc) (T : TxView) :
    Fractional (fun q => boltTxDef (GF := GF) B N tx q T) := by
  sorry

theorem boltTxDef_agree (B : BNs) (N : Namespace) (tx : Loc) (q1 q2 : Qp) (T1 T2 : TxView) :
    boltTxDef (GF := GF) B N tx q1 T1 ∗ boltTxDef B N tx q2 T2 ⊢ ⌜T1 = T2⌝ := by
  sorry

theorem boltTxDef_valid (B : BNs) (N : Namespace) (tx : Loc) (q : Qp) (T : TxView) :
    boltTxDef (GF := GF) B N tx q T ⊢ ⌜q ≤ 1⌝ := by
  sorry

theorem boltTxDef_nonnull (B : BNs) (N : Namespace) (tx : Loc) (q : Qp) (T : TxView) :
    boltTxDef (GF := GF) B N tx q T ⊢ ⌜tx ≠ Loc.null⌝ := by
  sorry

theorem boltTxDef_base (B : BNs) (N : Namespace) (tx : Loc) (q q' : Qp) (T : TxView)
    (D : Data) :
    boltTxDef (GF := GF) B N tx q T ∗ boltStateDef B q' D ⊢ ⌜T.rw = true → T.base = D⌝ := by
  sorry

instance txDBDef_persistent (tx db : Loc) : Persistent (txDBDef (GF := GF) tx db) := by
  sorry

instance txDoneDef_persistent (tx : Loc) : Persistent (txDoneDef (GF := GF) tx) := by
  sorry

instance boltBktDef_persistent (B : BNs) (tx b : Loc) (n : GoString) (g : Nat) :
    Persistent (boltBktDef (GF := GF) B tx b n g) := by
  sorry

instance txBytesDef_persistent (B : BNs) (tx : Loc) (s : GoSlice) (b : GoString) :
    Persistent (txBytesDef (GF := GF) B tx s b) := by
  sorry

instance boltCurDef_timeless (B : BNs) (tx c : Loc) (T : TxView) (es : List BoltEnt)
    (pos : Option Nat) : Timeless (boltCurDef (GF := GF) B tx c T es pos) := by
  sorry

theorem txBytesDef_acc (B : BNs) (N : Namespace) (tx : Loc) (q : Qp) (T : TxView)
    (s : GoSlice) (b : GoString) :
    txBytesDef (GF := GF) B tx s b ∗ boltTxDef B N tx q T ⊢
      ∃ dq : DFrac, s ↦*{dq} b ∗ (s ↦*{dq} b -∗ boltTxDef B N tx q T) := by
  sorry

theorem boltTxDef_fill (B : BNs) (N : Namespace) (tx b : Loc) (T : TxView) (n : GoString)
    (g : Nat) (hrw : T.rw = true) :
    boltTxDef (GF := GF) B N tx 1 T ∗ boltBktDef B tx b n g ⊢
      ∃ f : w64, b.[Bucket, go!"FillPercent"] ↦ f ∗
        (∀ f' : w64, ⌜¬ float64IsNaN f'⌝ -∗ b.[Bucket, go!"FillPercent"] ↦ f' -∗
          boltTxDef B N tx 1 T) := by
  sorry

/-- **A reader's `boltTx` is its `rdTx` with a pool loan, and the database** (design §3.13):
the public reader triples are corollaries of the internal ones over `rdTx`. -/
theorem boltTx_rdTx (B : BNs) (N : Namespace) (tx : Loc) (q : Qp) (T : TxView)
    (hro : T.rw = false) :
    boltTxDef (GF := GF) B N tx q T ⊣⊢ ∃ db, rdTx B N tx .loan q T ∗ isBoltDef B N db := by
  sorry

end tx

end bbolt
end EtcdGrove
end Perennial
