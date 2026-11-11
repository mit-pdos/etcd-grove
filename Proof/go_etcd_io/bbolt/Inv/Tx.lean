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
public import Proof.go_etcd_io.bbolt.Model.WrCur
public import Proof.go_etcd_io.bbolt.Model.WOps
public import Proof.go_etcd_io.bbolt.Read.PosDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section tx
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `tx`'s share of `tx.db` at fraction `q` (`q · ¾`: `txsInv` holds the other quarter). -/
def txDbQ (q : Qp) : Qp := QpMul q (1 : Qp).half + QpMul q (1 : Qp).half.half

/-- **The transaction's view is `v`** (persistent, agreeing): its registry's entry at the fixed
key `null`, for both kinds (maintainer R's U6g item 2 for readers; U6w, the review's F2, for
writers: two fragments agree, so a cursor's, a handle's or a slice's view is the writer's current
`X.v` on a later call). A writer's base view, minted at `beginRWTx`; its re-based views (a remap
in `Commit`) are `viewBase`. -/
def viewOf (r : TxReg) (v : View) : IProp GF :=
  iprop(null ↪[r.n.vw]□ v)

/-- **A writer's view registered at its base** (batch 37.3: what a remap re-bases, `vwOwn`'s
entries at their keys). -/
def viewBase (r : TxReg) (v : View) : IProp GF :=
  iprop(v.base ↪[r.n.vw]□ v)

/-- A writer's views (`wtxFrac`'s): the fixed one and the one at its base. -/
def viewW (r : TxReg) (v : View) : IProp GF :=
  iprop(viewOf r v ∗ viewBase r v)

instance viewBase_persistent (r : TxReg) (v : View) : Persistent (viewBase (GF := GF) r v) := by
  unfold viewBase; infer_instance

instance viewBase_timeless (r : TxReg) (v : View) : Timeless (viewBase (GF := GF) r v) := by
  unfold viewBase; infer_instance

instance viewW_persistent (r : TxReg) (v : View) : Persistent (viewW (GF := GF) r v) := by
  unfold viewW viewOf viewBase; infer_instance

instance viewW_timeless (r : TxReg) (v : View) : Timeless (viewW (GF := GF) r v) := by
  unfold viewW viewOf viewBase; infer_instance

omit go_gctx hos in
/-- A reader's `viewOf`: its view at `null`. -/
theorem viewOf_ro (r : TxReg) (v : View) (h : r.rw = false) :
    viewOf (GF := GF) r v = iprop(null ↪[r.n.vw]□ v) := by
  unfold viewOf; rfl

/-- A cursor stack element's node is in the writer's node-location registry (`nl`) at `y`. -/
def nodeLoc (r : TxReg) (nl : Loc → Option (Loc × Nat)) (e : elemRef) : IProp GF :=
  if e.node' = null then iprop(emp)
  else iprop(∃ y, ⌜nl e.node' = some y⌝ ∗ e.node' ↪[r.n.nl]□ y)

/-- The handle `b` of bucket `n` at generation `g`: a writer's registry's; a reader's is at
generation 0 (its bucket is in `boltBktDef`'s and `boltCurDef`'s reader branches; maintainer R's
U6g item 3: no registry, so that a reader's new handle needs no fresh registry key). -/
def handleFrag (r : TxReg) (b : Loc) (n : GoString) (g : Nat) : IProp GF :=
  if r.rw then iprop(b ↪[r.n.bk]□ (n, g))
  else iprop(⌜g = 0⌝)

/-- **The writer's handles' registry fragments** (persistent; maintainer R's U6g item 4, moved here
by U6w): one per handle of `H`. What `Bucket.Bucket_w` gives a cached child's fragment from. -/
def hdlFrags (r : TxReg) (H : GMap Loc (GoString × Nat)) : IProp GF :=
  iprop([∗map] b ↦ h ∈ H, b ↪[r.n.bk]□ h)

instance hdlFrags_persistent (r : TxReg) (H : GMap Loc (GoString × Nat)) :
    Persistent (hdlFrags (GF := GF) r H) := by
  unfold hdlFrags; infer_instance

/-- **The writer's handle registry at `q`**: its auth at `q` and every handle's fragment (the
coordinator's decision on maintainer R's proposal, U6w: `wtxCore`, `wtxCoreQ` and `wtxFrac` hold
it in place of the bare auth, so that a writer always has its handles' fragments). -/
def hdlAuth (r : TxReg) (q : Qp) (H : GMap Loc (GoString × Nat)) : IProp GF :=
  iprop(ghostMapAuth r.n.bk q H ∗ hdlFrags r H)

open Iris.ProofMode in
omit hos in
/-- A handle's fragment out of `hdlFrags`. -/
theorem hdlFrags_lookup (r : TxReg) (H : GMap Loc (GoString × Nat)) (b : Loc) (h : GoString × Nat)
    (hb : H !! b = some h) : hdlFrags (GF := GF) r H ⊢ b ↪[r.n.bk]□ h := by
  unfold hdlFrags
  iintro #Hf
  iapply (BigSepM.bigSepM_lookup (Φ := fun k u => (k ↪[r.n.bk]□ u : IProp GF)) hb) $$ Hf

open Iris.ProofMode in
omit hos in
/-- A new handle's fragment added to `hdlFrags`. -/
theorem hdlFrags_insert (r : TxReg) (H : GMap Loc (GoString × Nat)) (b : Loc) (h : GoString × Nat)
    (hb : H !! b = none) : hdlFrags (GF := GF) r H ∗ b ↪[r.n.bk]□ h ⊢ hdlFrags r (H.insert b h) := by
  unfold hdlFrags
  iintro ⟨#Hf, #Hb⟩
  iapply (BigSepM.bigSepM_insert (Φ := fun k u => (k ↪[r.n.bk]□ u : IProp GF)) hb).2
  iframe #

open Iris.ProofMode in
omit hos in
/-- The empty registry's fragments. -/
theorem hdlFrags_empty (r : TxReg) : ⊢ hdlFrags (GF := GF) r ∅ := by
  unfold hdlFrags
  iapply BigSepM.bigSepM_empty.2
  iempintro

open Iris.ProofMode in
omit hos in
/-- The empty registry, with its (no) fragments. -/
theorem hdlAuth_of_empty (r : TxReg) :
    ghostMapAuth (GF := GF) r.n.bk 1 (∅ : GMap Loc (GoString × Nat)) ⊢ hdlAuth r 1 ∅ := by
  unfold hdlAuth
  iintro Ha
  iframe Ha
  iapply hdlFrags_empty

instance hdlFrags_timeless (r : TxReg) (H : GMap Loc (GoString × Nat)) :
    Timeless (hdlFrags (GF := GF) r H) := by
  unfold hdlFrags; infer_instance

instance hdlAuth_timeless (r : TxReg) (q : Qp) (H : GMap Loc (GoString × Nat)) :
    Timeless (hdlAuth (GF := GF) r q H) := by
  unfold hdlAuth; infer_instance

open Iris.ProofMode in
omit hos in
instance hdlAuth_fractional (r : TxReg) (H : GMap Loc (GoString × Nat)) :
    Fractional (fun q => hdlAuth (GF := GF) r q H) where
  fractional p q := by
    unfold hdlAuth
    constructor
    · iintro ⟨Ha, #Hf⟩
      icases ((ghostMapAuth_fractional r.n.bk H).fractional p q).1 $$ Ha with ⟨H1, H2⟩
      isplitl [H1]
      · iframe; iframe #
      · iframe; iframe #
    · iintro ⟨⟨H1, #Hf⟩, ⟨H2, -⟩⟩
      iframe #
      iapply ((ghostMapAuth_fractional r.n.bk H).fractional p q).2
      iframe

/-- **The writer's node-location registry's fragments** (persistent; U6y's F1): one per entry of
`M` (`X.nloc`). What a writer cursor's `nodeLoc` takes its node elements' fragments from. -/
def nlFrags (r : TxReg) (M : GMap Loc (Loc × Nat)) : IProp GF :=
  iprop([∗map] l ↦ y ∈ M, l ↪[r.n.nl]□ y)

instance nlFrags_persistent (r : TxReg) (M : GMap Loc (Loc × Nat)) :
    Persistent (nlFrags (GF := GF) r M) := by
  unfold nlFrags; infer_instance

instance nlFrags_timeless (r : TxReg) (M : GMap Loc (Loc × Nat)) :
    Timeless (nlFrags (GF := GF) r M) := by
  unfold nlFrags; infer_instance

/-- **The writer's node-location registry at `q`** (U6y's F1, as `hdlAuth`): its auth at `q` and
every entry's persistent fragment (`wtxCore`, `wtxCoreQ`, `wtxFrac`). -/
def nlAuth (r : TxReg) (q : Qp) (M : GMap Loc (Loc × Nat)) : IProp GF :=
  iprop(ghostMapAuth r.n.nl q M ∗ nlFrags r M)

open Iris.ProofMode in
omit hos in
/-- An entry's fragment out of `nlFrags`. -/
theorem nlFrags_lookup (r : TxReg) (M : GMap Loc (Loc × Nat)) (l : Loc) (y : Loc × Nat)
    (hl : M !! l = some y) : nlFrags (GF := GF) r M ⊢ l ↪[r.n.nl]□ y := by
  unfold nlFrags
  iintro #Hf
  iapply (BigSepM.bigSepM_lookup (Φ := fun k u => (k ↪[r.n.nl]□ u : IProp GF)) hl) $$ Hf

open Iris.ProofMode in
omit hos in
/-- A new entry's fragment added to `nlFrags`. -/
theorem nlFrags_insert (r : TxReg) (M : GMap Loc (Loc × Nat)) (l : Loc) (y : Loc × Nat)
    (hl : M !! l = none) : nlFrags (GF := GF) r M ∗ l ↪[r.n.nl]□ y ⊢ nlFrags r (M.insert l y) := by
  unfold nlFrags
  iintro ⟨#Hf, #Hb⟩
  iapply (BigSepM.bigSepM_insert (Φ := fun k u => (k ↪[r.n.nl]□ u : IProp GF)) hl).2
  iframe #

open Iris.ProofMode in
omit hos in
/-- The empty node registry, with its (no) fragments. -/
theorem nlAuth_of_empty (r : TxReg) :
    ghostMapAuth (GF := GF) r.n.nl 1 (∅ : GMap Loc (Loc × Nat)) ⊢ nlAuth r 1 ∅ := by
  unfold nlAuth nlFrags
  iintro Ha
  iframe Ha
  iapply BigSepM.bigSepM_empty.2
  iempintro

instance nlAuth_timeless (r : TxReg) (q : Qp) (M : GMap Loc (Loc × Nat)) :
    Timeless (nlAuth (GF := GF) r q M) := by
  unfold nlAuth; infer_instance

open Iris.ProofMode in
omit hos in
instance nlAuth_fractional (r : TxReg) (M : GMap Loc (Loc × Nat)) :
    Fractional (fun q => nlAuth (GF := GF) r q M) where
  fractional p q := by
    unfold nlAuth
    constructor
    · iintro ⟨Ha, #Hf⟩
      icases ((ghostMapAuth_fractional r.n.nl M).fractional p q).1 $$ Ha with ⟨H1, H2⟩
      isplitl [H1]
      · iframe; iframe #
      · iframe; iframe #
    · iintro ⟨⟨H1, #Hf⟩, ⟨H2, -⟩⟩
      iframe #
      iapply ((ghostMapAuth_fractional r.n.nl M).fractional p q).2
      iframe

/-- Bytes at `p` (a page, an inline page): in a page of the view `v`, or persistent heap bytes. -/
def locOwn (v : View) (p : Loc) (bs : List w8) : IProp GF :=
  iprop(⌜inViewLoc v p bs⌝ ∨ bytesPointsto p DFrac.discard bs)

/-- **A writer cursor's inline root page** (persistent; U6y's design): if the stack's first element
is a page reference at the inline root (`rt = 0`), the bytes `ipg` at its page (the view's, or
persistent heap bytes of a clone). -/
def wInlOwn (v : View) (rt : Nat) (ipg : List w8) (els : List elemRef) : IProp GF :=
  match els with
  | e :: _ => if rt = 0 ∧ e.node' = null then locOwn v e.page' ipg else iprop(emp)
  | [] => iprop(emp)

instance wInlOwn_timeless (v : View) (rt : Nat) (ipg : List w8) (els : List elemRef) :
    Timeless (wInlOwn (GF := GF) v rt ipg els) := by
  unfold wInlOwn locOwn
  split
  · split <;> infer_instance
  · infer_instance

instance wInlOwn_persistent (v : View) (rt : Nat) (ipg : List w8) (els : List elemRef) :
    Persistent (wInlOwn (GF := GF) v rt ipg els) := by
  unfold wInlOwn locOwn
  have : ∀ (p : Loc) (bs : List w8), Persistent (bytesPointsto (GF := GF) p DFrac.discard bs) :=
    fun p bs => (bytesPointsto_dfractional (GF := GF) p bs).dfractional_persistent
  split
  · split <;> infer_instance
  · infer_instance

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

/-- A reader's bucket with its header at `ibp` and its inline page at `pp` (`rBkt`'s body). -/
def rBktP (v : View) (tx b : Loc) (dq : DFrac) (bv : List w8) (ibp pp : Loc) : IProp GF :=
  iprop(b.[Bucket, go!"InBucket"] ↦{dq} ibp ∗ b.[Bucket, go!"tx"] ↦{dq} tx ∗
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
    ⌜T = TxView.ro v.data ∧ viewWF v ∧ mv.txid'.toNat = v.txid ∧ t.pages' = null ∧ tx ≠ null ∧
      t.managed' = false ∧ txRoot (GF := GF) tx ≠ null ∧
      (∀ id pg, v.pages !! id = some pg → id + (1 + pageOverflow pg) ≤ mv.pgid'.toNat)⌝)

/-- **A page of a view inside a mapping is within `db.page`'s range**: with `mapFields`' bound
(`l ≤ maxMapSize`), `Tx.page`'s premise `id·4096 < 0xFFFFFFFFFFFF`. -/
theorem pageIdx_lt_maxMap (id l : Nat) (h : (id + 1) * 4096 ≤ l) (hl : l ≤ 0xFFFFFFFFFFFF) :
    id * 4096 < 0xFFFFFFFFFFFF := by
  omega

/-- The writer's handles' generations (the `buckets` caches): every handle's generation is at
most its name's, the opened bucket of a name is its current handle, and (D1, maintainer 14,
decided by the coordinator) a handle of its name's current generation is the bucket the root
bucket's cache holds for the name (without it `Put`/`Delete`/`Get` through the handle cannot be
tied to `T.cur`: `X.handles = {b ↦ (n, 0)}` with `bktLoc X n = none` satisfies the first two). -/
def gensOK (T : TxView) (X : WX) : Prop :=
  (∀ b n g, X.handles !! b = some (n, g) → g ≤ T.gen n) ∧
  (∀ n b, bktLoc X n = some b → X.handles !! b = some (n, T.gen n)) ∧
  ∀ b n, X.handles !! b = some (n, T.gen n) → bktLoc X n = some b

/-- `gensOK`'s third clause (D1): a handle of the current generation of `n` is the bucket `n`
opened in the root bucket. -/
theorem gensOK_handle_bktLoc (T : TxView) (X : WX) (h : gensOK T X) :
    ∀ b n, X.handles !! b = some (n, T.gen n) → bktLoc X n = some b :=
  h.2.2

/-- **The root bucket's cache is injective** (`gensOK`'s second clause: the handle registry
records each opened bucket's name). -/
theorem gensOK_bktLoc_inj (T : TxView) (X : WX) (h : gensOK T X) (n n' : GoString) (b : Loc)
    (hn : bktLoc X n = some b) (hn' : bktLoc X n' = some b) : n' = n := by
  have h1 := h.2.1 n b hn
  have h2 := h.2.1 n' b hn'
  rw [h1] at h2
  simp only [Option.some.injEq, Prod.mk.injEq] at h2
  exact h2.1.symm

/-- **The writer's records' carried facts** (batches 43.3, 44.2, 44.5 of `notes/bbolt-proof-plan.md`,
U10g's findings; the last conjunct of `wtxFrac`'s facts): every live object reached from the root
bucket (`liveReach`: `rebalance`'s and `spill`'s premise; the operations only add reached objects),
no commit handler (`beginRWTx`'s zero value; `OnCommit` is outside the verified API: `Commit` runs
the list after the close), and no cached child of the root bucket is the root itself. -/
def wrFacts (X : WX) : Prop :=
  liveReach X ∧ X.t.t.commitHandlers' = slice.nil ∧
  ∀ B, X.t.bs !! X.rl = some B → ∀ k c, B.bm !! k = some c → c ≠ X.rl

/-- **A writer's part at fraction `q`** (design §3.10, F3): its heap at `q`, its handles'
`FillPercent`s at `q`, its base view's cells at `q · wq`, the library's quarter of the committed
data at `q`, its handle and node registries' auths at `q`, its fields' share, `mmaplock`'s
mapping fields at `q · ¼` (the base view's pages inside the mapping, as a reader's), and its
facts (batch 43/44: `wrFacts`; maintainer 16: ending with the cursor facts `wrCurFacts`). -/
def wtxFrac (B : BNs) (tx : Loc) (r : TxReg) (q : Qp) (T : TxView) (X : WX) : IProp GF :=
  iprop(wtxHeap tx (DFrac.own q) X ∗ fills X.handles (DFrac.own q) ∗
    viewCells (QpMul q wq) X.v ∗ ghostVar B.st (QpMul q (1 : Qp).half.half) T.base ∗
    hdlAuth r q X.handles ∗ nlAuth r q X.nloc ∗
    tx.[Tx, go!"db"] ↦{DFrac.own (txDbQ q)} r.db ∗
    (∃ l : Nat, mapFields r.db (DFrac.own (QpMul q (1 : Qp).half.half))
      (some (X.v.base, l) : MapSt) ∗ ⌜∀ id pg, X.v.pages !! id = some pg → (id + 1) * 4096 ≤ l⌝) ∗
    viewW r X.v ∗
    ⌜wOK X ∧ T.rw = true ∧ T.cur = wtxData X ∧ T.base = X.v.data ∧ gensOK T X ∧ tx ≠ null ∧
      X.t.t.managed' = false ∧ txRoot (GF := GF) tx ≠ null ∧ 0 < X.t.t.meta'.addr ∧ wrFacts X ∧
      wrCurFacts T X⌝)

/-- **A read transaction over the core** (A2, round 4 N5): `boltTx`'s reader part with
`isBoltCore` in place of `isBolt`, its pair's source `src` (a pool loan carries the pool). -/
def rdTx (B : BNs) (N : Namespace) (tx : Loc) (src : PairSrc) (q : Qp) (T : TxView) :
    IProp GF :=
  iprop(∃ (db : Loc) (p : GoString) (sp : Loc) (t0 : Nat) (r : TxReg) (c : TxViewC) (v : View)
      (mv : Meta) (k : Nat),
    ⌜T = TxView.ofC c ∧ r.db = db ∧ r.rw = false ∧ r.src = src⌝ ∗ reg tx B r ∗
    isBoltCoreP B N db p sp t0 ∗ ghostVar r.n.v q.half (c, TxX.rd v mv k) ∗
    ghostVar r.n.ex q () ∗ rtxFrac B tx r q T v mv ∗
    (if src = .loan then threadPool.isThreadPool (poolN N) B.pool (rdPair B db sp)
     else ghostVar B.spr q.half (some k)))

/-- **`tx` is a transaction of `B`/`N` with the view `T` at fraction `q`** (design §3.10; what
`boltTx tx γ q T` is sealed to): a writer's registration, database and part; or a reader's
`rdTx` with a pool loan, and the database. -/
def boltTxDef (B : BNs) (N : Namespace) (tx : Loc) (q : Qp) (T : TxView) : IProp GF :=
  if T.rw then
    iprop(∃ (db : Loc) (p : GoString) (sp : Loc) (t0 : Nat) (r : TxReg) (c : TxViewC) (X : WX),
      ⌜T = TxView.ofC c ∧ r.db = db ∧ r.rw = true⌝ ∗ reg tx B r ∗ isBoltP B N db p sp t0 ∗
      ghostVar r.n.v q.half (c, TxX.wr X) ∗ ghostVar r.n.ex q () ∗ wtxFrac B tx r q T X)
  else iprop(∃ db : Loc, rdTx B N tx .loan q T ∗ isBoltDef B N db)

/-- `tx` is a transaction of the database `db` of names `B` and namespace `N` (persistent;
`Tx.DB` compares physical values, design §3.10; batch 21: the database's names are the
client's, so the entry of `tx` in `B`'s registry is found by opening `B`'s invariant). -/
def txDBDef (B : BNs) (N : Namespace) (tx db : Loc) : IProp GF :=
  iprop(∃ r : TxReg, isBoltDef B N db ∗ reg tx B r ∗ ⌜r.db = db⌝)

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
relative to the view (a reader's: its bucket's fields, persistent, of the top-level bucket `n` of
the view, as `boltBktDef`'s, and `rCurPos` over them; maintainer R's U6g item 1) or to the base
view and the node registry (a writer's: `wCurAt` from the bucket's root `wRoot`, its node
references' registry fragments and its inline root page's bytes, U6z; independent of the
writer's heap, so that it survives a same-value `Put`). -/
def boltCurDef (B : BNs) (tx c : Loc) (T : TxView) (es : List BoltEnt) (pos : Option Nat) :
    IProp GF :=
  iprop(∃ (r : TxReg) (b : Loc) (n : GoString) (g : Nat) (stk : GoSlice) (els : List elemRef)
      (v : View),
    reg tx B r ∗ handleFrag r b n g ∗ c ↦ (Cursor.mk b stk) ∗ stk ↦* els ∗
    ownSliceCap elemRef stk (DFrac.own 1) ∗ viewOf r v ∗
    ⌜es = bktEnts ((T.cur !! n).getD ∅) ∧ g = T.gen n⌝ ∗
    (if r.rw then iprop(∃ (nl : Loc → Option (Loc × Nat)) (ipg : List w8),
        ([∗list] e ∈ els, nodeLoc r nl e) ∗ wInlOwn v (wRoot v T n) ipg els ∗
        ⌜wCurAt nl v es b (wRoot v T n) ipg els pos⌝)
     else iprop(∃ (bv : List w8) (ibp pp : Loc), rBktP v tx b DFrac.discard bv ibp pp ∗
       ⌜bktEntry v.pages (rootVal v) n bv ∧ rCurPos v bv pp els pos⌝)))

/-! ## The laws over the definitions (U5, U6) -/

private instance ite_persistent' {c : Prop} [Decidable c] (P Q : IProp GF) [Persistent P] [Persistent Q] :
    Persistent (if c then P else Q) := by
  split <;> infer_instance

private instance ite_timeless' {c : Prop} [Decidable c] (P Q : IProp GF) [Timeless P] [Timeless Q] :
    Timeless (if c then P else Q) := by
  split <;> infer_instance

private instance bytesPointsto_discard_persistent' (l : Loc) (bs : List w8) :
    Persistent (bytesPointsto (GF := GF) l DFrac.discard bs) :=
  (bytesPointsto_dfractional (GF := GF) l bs).dfractional_persistent

private instance ownSliceCap_timeless' (V : Type) [ZeroVal V] [TypedPointsto (GF := GF) V] (s : GoSlice)
    (dq : DFrac) : Timeless (ownSliceCap (GF := GF) V s dq) := by
  rw [ownSliceCap_unseal]; unfold ownSliceCapDef; infer_instance

private instance nodeLoc_timeless' (r : TxReg) (nl : Loc → Option (Loc × Nat)) (e : elemRef) :
    Timeless (nodeLoc (GF := GF) r nl e) := by
  unfold nodeLoc; split <;> infer_instance

private instance nodeLocs_timeless' (r : TxReg) (nl : Loc → Option (Loc × Nat)) (els : List elemRef) :
    Timeless ([∗list] e ∈ els, nodeLoc (GF := GF) r nl e) :=
  BigSepL.bigSepL_timeless (fun _ => inferInstance)

open Iris.ProofMode in
/-- The `ex` token's share of a `boltTx`. -/
private theorem boltTxDef_ex (B : BNs) (N : Namespace) (tx : Loc) (q : Qp) (T : TxView) :
    boltTxDef (GF := GF) B N tx q T ⊢ ∃ r : TxReg, reg tx B r ∗ ghostVar r.n.ex q () ∗
      (∃ (c : TxViewC) (x : TxX), ghostVar r.n.v q.half (c, x) ∗ ⌜T = TxView.ofC c⌝) ∗
      ∃ d : Loc, tx.[Tx, go!"db"] ↦{DFrac.own (txDbQ q)} d := by
  unfold boltTxDef
  split
  · iintro ⟨%db, %p, %sp, %t0, %r, %c, %X, %Hc, Hreg, -, Hv, Hex, Hw⟩
    iexists r; iframe Hreg Hex
    unfold wtxFrac
    icases Hw with ⟨-, -, -, -, -, -, Hdb, -⟩
    isplitl [Hv]
    · iexists c, (TxX.wr X); iframe Hv; ipureintro; exact Hc.1
    iexists r.db; iexact Hdb
  · iintro ⟨%db', Hr, -⟩
    unfold rdTx
    icases Hr with ⟨%db, %p, %sp, %t0, %r, %c, %v, %mv, %k, %Hc, Hreg, -, Hv, Hex, Hrt, -⟩
    iexists r; iframe Hreg Hex
    unfold rtxFrac
    icases Hrt with ⟨%t, -, -, -, -, -, -, -, -, Hdb, -⟩
    isplitl [Hv]
    · iexists c, (TxX.rd v mv k); iframe Hv; ipureintro; exact Hc.1
    iexists r.db; iexact Hdb


private instance mapFields_timeless_l (db : Loc) (dq : DFrac) (ms : MapSt) :
    Timeless (mapFields (GF := GF) db dq ms) := by
  unfold mapFields; split <;> infer_instance

private instance viewCells_timeless_l (q : Qp) (v : View) : Timeless (viewCells (GF := GF) q v) := by
  unfold viewCells; infer_instance

private instance rBkt_timeless_l (v : View) (tx b : Loc) (dq : DFrac) (bv : List w8) :
    Timeless (rBkt (GF := GF) v tx b dq bv) := by
  unfold rBkt locOwn; infer_instance

private instance rtxFrac_timeless_l (B : BNs) (tx : Loc) (r : TxReg) (q : Qp) (T : TxView)
    (v : View) (mv : Meta) : Timeless (rtxFrac (GF := GF) B tx r q T v mv) := by
  unfold rtxFrac viewOf; infer_instance

private instance reg_timeless_l (tx : Loc) (B : BNs) (r : TxReg) :
    Timeless (reg (GF := GF) tx B r) := by
  unfold reg; infer_instance

private instance reg_persistent_l (tx : Loc) (B : BNs) (r : TxReg) :
    Persistent (reg (GF := GF) tx B r) := by
  unfold reg; infer_instance

private instance isBoltP_persistent_l (B : BNs) (N : Namespace) (db : Loc) (p : GoString)
    (sp : Loc) (t0 : Nat) : Persistent (isBoltP (GF := GF) B N db p sp t0) := by
  unfold isBoltP; infer_instance

private instance dblAt_timeless_l (B : BNs) (db : Loc) : Timeless (dblAt (GF := GF) B db) := by
  unfold dblAt; infer_instance

private instance dblAt_persistent_l (B : BNs) (db : Loc) : Persistent (dblAt (GF := GF) B db) := by
  unfold dblAt; infer_instance

private instance ownSliceCap_timeless_l (V : Type) [ZeroVal V] [TypedPointsto (GF := GF) V]
    (s : GoSlice) (dq : DFrac) : Timeless (ownSliceCap (GF := GF) V s dq) := by
  rw [ownSliceCap_unseal]; unfold ownSliceCapDef; infer_instance

private instance srcOwn_timeless_l (v : View) (s : GoSlice) (src : Src) (bs : List w8) :
    Timeless (srcOwn (GF := GF) v s src bs) := by
  unfold srcOwn; split <;> infer_instance

private instance wOwn_timeless_l (v : View) (live : Bool) (it : Inode) (w : WEntry) :
    Timeless (wOwn (GF := GF) v live it w) := by
  unfold wOwn; infer_instance

private instance pageOwn_timeless_l (v : View) (B : BRec) : Timeless (pageOwn (GF := GF) v B) := by
  unfold pageOwn; split
  · infer_instance
  · split <;> infer_instance

private instance objOwn_timeless_l (v : View) (l : Loc) (dq : DFrac) (b : Bool) (o : WObj) :
    Timeless (objOwn (GF := GF) v l dq b o) := by
  cases b <;> cases o <;> unfold objOwn <;> infer_instance

private instance wtxHeap_timeless_l (tx : Loc) (dq : DFrac) (X : WX) :
    Timeless (wtxHeap (GF := GF) tx dq X) := by
  unfold wtxHeap txFields rootFill; infer_instance

private instance fills_timeless_l (H : GMap Loc (GoString × Nat)) (dq : DFrac) :
    Timeless (fills (GF := GF) H dq) := by
  unfold fills; infer_instance

private instance wtxFrac_timeless_l (B : BNs) (tx : Loc) (r : TxReg) (q : Qp) (T : TxView)
    (X : WX) : Timeless (wtxFrac (GF := GF) B tx r q T X) := by
  unfold wtxFrac viewW viewOf viewBase; infer_instance

open Iris.ProofMode in
theorem boltTxDef_later (B : BNs) (N : Namespace) (db tx : Loc) (q : Qp) (T : TxView) :
    isBoltDef (GF := GF) B N db ⊢ ▷ boltTxDef B N tx q T -∗ ◇ boltTxDef B N tx q T := by
  iintro #Hdb Ht
  ihave #Hdb' := Hdb
  unfold isBoltDef
  icases Hdb' with ⟨%p, %sp, %t0, #HbP⟩
  unfold boltTxDef
  split
  · icases Ht with ⟨%db1, %p1, %sp1, %t01, %r, %c, Ht⟩
    imod (later_exists_except0 (PROP := IProp GF)) $$ Ht with ⟨%X, Ht⟩
    icases Ht with ⟨>%Hc, >#Hreg, Hb1, >Hv, >Hex, >Hw⟩
    ihave >#Hdbl1 : ▷ dblAt B db1 $$ [Hb1]
    · inext; unfold isBoltP isBoltCoreP; icases Hb1 with ⟨⟨$, -⟩, -⟩
    ihave #Hdbl : dblAt B db $$ []
    · unfold isBoltP isBoltCoreP; icases HbP with ⟨⟨$, -⟩, -⟩
    unfold dblAt
    icombine Hdbl Hdbl1 gives %hd
    obtain ⟨-, rfl⟩ := hd
    imodintro
    iexists db, p, sp, t0, r, c, X
    isplitr
    · ipureintro; exact Hc
    iframe Hreg HbP
    iframe
  · icases Ht with ⟨%db', Hr, -⟩
    unfold rdTx
    icases Hr with ⟨%db1, %p1, %sp1, %t01, %r, %c, %v, Hr⟩
    imod (later_exists_except0 (PROP := IProp GF)) $$ Hr with ⟨%mv, Hr⟩
    imod (later_exists_except0 (PROP := IProp GF)) $$ Hr with ⟨%k, Hr⟩
    icases Hr with ⟨>%Hc, >#Hreg, Hc1, >Hv, >Hex, >Hrt, -⟩
    ihave >#Hdbl1 : ▷ dblAt B db1 $$ [Hc1]
    · inext; unfold isBoltCoreP; icases Hc1 with ⟨$, -⟩
    ihave #Hdbl : dblAt B db $$ []
    · unfold isBoltP isBoltCoreP; icases HbP with ⟨⟨$, -⟩, -⟩
    unfold dblAt
    icombine Hdbl Hdbl1 gives %hd
    obtain ⟨-, rfl⟩ := hd
    imodintro
    iexists db
    isplitl [Hv Hex Hrt]
    rotate_left
    · unfold isBoltDef; iexists p, sp, t0; iexact HbP
    iexists db, p, sp, t0, r, c, v, mv, k
    iframe
    isplitr
    · ipureintro; exact Hc
    unfold isBoltP
    icases HbP with ⟨#Hcore, -, #Hpool, -⟩
    iframe Hcore
    simp only [↓reduceIte]
    iframe Hreg Hpool

section txfrac
open Iris.ProofMode
set_option linter.unusedSectionVars false

/-! ## A transaction at a fraction (U5d's `Txn/TxFrac`, moved in by batch 37)

Splitting is component-wise; combining agrees on the existentials (the registration and the agreed
state by their ghost state, the fields' values and the mapping's length by their points-tos) and
adds the fractions (`txDbQ`, `QpMul`). The helpers are private. -/

/-! ## Fractions -/

private theorem QpMul_add_l (p q r : Qp) : QpMul (p + q) r = QpMul p r + QpMul q r :=
  Subtype.ext (by simp only [QpMul, Qp.val_add]; grind)

private theorem txDbQ_add (p q : Qp) : txDbQ (p + q) = txDbQ p + txDbQ q := by
  unfold txDbQ
  rw [QpMul_add_l, QpMul_add_l]
  apply Subtype.ext
  simp only [Qp.val_add]; grind

/-- A fractional predicate at a fraction that adds. -/
private theorem fractional_comp (Φ : Qp → IProp GF) [h : Fractional Φ] (f : Qp → Qp)
    (hf : ∀ p q, f (p + q) = f p + f q) : Fractional (fun q => Φ (f q)) :=
  ⟨fun p q => by rw [hf]; exact h.fractional _ _⟩

/-- An existential of fractional predicates whose witnesses can be made to agree. -/
private theorem fractional_exists' {X : Type} (Φ : X → Qp → IProp GF) (hf : ∀ x, Fractional (Φ x))
    (hc : ∀ x y p q, Φ x p ∗ Φ y q ⊢ Φ x p ∗ Φ x q) :
    Fractional (fun q => iprop(∃ x, Φ x q)) := by
  refine ⟨fun p q => ⟨?_, ?_⟩⟩
  · iintro ⟨%x, H⟩
    icases ((hf x).fractional p q).1 $$ H with ⟨H1, H2⟩
    isplitl [H1]
    · iexists x; iexact H1
    · iexists x; iexact H2
  · iintro ⟨⟨%x, H1⟩, ⟨%y, H2⟩⟩
    ihave H := hc x y p q $$ [H1 H2]
    · isplitl [H1]
      · iexact H1
      · iexact H2
    iexists x
    iapply ((hf x).fractional p q).2
    iexact H

private instance pointsto_fractional_tf {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (l : Loc)
    (v : V) [DFractional (fun dq => (l ↦{dq} v : IProp GF))] :
    Fractional (fun q : Qp => (l ↦{DFrac.own q} v : IProp GF)) :=
  fractional_of_dfractional (fun dq => (l ↦{dq} v : IProp GF))

private instance bytes_fractional_tf (l : Loc) (bs : List w8) :
    Fractional (fun q : Qp => bytesPointsto (GF := GF) l (DFrac.own q) bs) :=
  fractional_of_dfractional (h := bytesPointsto_dfractional (GF := GF) l bs) _

private instance viewCells_fractional_tf (v : View) :
    Fractional (fun q : Qp => viewCells (GF := GF) q v) := by
  unfold viewCells; infer_instance

/-- A `w64` field at a fraction, its value existential under a fact. -/
private theorem exField_fractional (l : Loc) (P : w64 → Prop) :
    Fractional (fun q : Qp => iprop(∃ v : w64, ⌜P v⌝ ∗ (l ↦{DFrac.own q} v : IProp GF))) := by
  refine fractional_exists' (fun v q => iprop(⌜P v⌝ ∗ (l ↦{DFrac.own q} v : IProp GF)))
    (fun v => inferInstance) (fun x y p q => ?_)
  iintro ⟨⟨%hx, H1⟩, ⟨%hy, H2⟩⟩
  icombine H1 H2 gives %h
  obtain ⟨-, rfl⟩ := h
  isplitl [H1]
  · iframe; ipureintro; exact hx
  · iframe; ipureintro; exact hx

private theorem QpMul_frac (Φ : Qp → IProp GF) [Fractional Φ] (c : Qp) :
    Fractional (fun q => Φ (QpMul q c)) :=
  fractional_comp Φ (fun q => QpMul q c) (fun p q => QpMul_add_l p q c)

private instance mapFields_some_fractional (db base : Loc) (l : Nat) :
    Fractional (fun q : Qp => mapFields (GF := GF) db (DFrac.own q) (some (base, l) : MapSt)) := by
  unfold mapFields; infer_instance

/-- Two mappings' fields at one base agree on the length. -/
private theorem mapFields_some_agree (db base : Loc) (l1 l2 : Nat) (dq1 dq2 : DFrac) :
    mapFields (GF := GF) db dq1 (some (base, l1) : MapSt) ∗
      mapFields db dq2 (some (base, l2) : MapSt) ⊢ ⌜l1 = l2⌝ := by
  unfold mapFields
  iintro ⟨⟨Ha1, -, -, -, %hm1⟩, ⟨Ha2, -, -, -, %hm2⟩⟩
  icombine Ha1 Ha2 gives %he
  ipureintro
  have e := congrArg (fun s : GoSlice => s.len.toNat) he
  simp only at e
  rw [toNat_W64_of_lt _ (by omega), toNat_W64_of_lt _ (by omega)] at e
  exact e

/-- **A writer's part is fractional** (same registration, view and records). -/
private theorem wtxFrac_fractional (B : BNs) (tx : Loc) (r : TxReg) (T : TxView) (X : WX) :
    Fractional (fun q => wtxFrac (GF := GF) B tx r q T X) := by
  have h1 := wtxHeap_fractional (GF := GF) tx X
  have h2 : Fractional (fun q : Qp => fills (GF := GF) X.handles (DFrac.own q)) := by
    unfold fills
    have : ∀ b : Loc, Fractional (fun q : Qp => iprop(∃ f : w64, ⌜¬ float64IsNaN f⌝ ∗
        (b.[Bucket, go!"FillPercent"] ↦{DFrac.own q} f : IProp GF))) :=
      fun b => exField_fractional _ _
    infer_instance
  have h3 := QpMul_frac (fun q => viewCells (GF := GF) q X.v) wq
  have h4 := QpMul_frac (fun q => ghostVar (GF := GF) B.st q T.base) (1 : Qp).half.half
  have h7 := fractional_comp (fun q => (tx.[Tx, go!"db"] ↦{DFrac.own q} r.db : IProp GF))
    txDbQ txDbQ_add
  have h8 : Fractional (fun q => iprop(∃ l : Nat,
      mapFields (GF := GF) r.db (DFrac.own (QpMul q (1 : Qp).half.half)) (some (X.v.base, l) : MapSt) ∗
      ⌜∀ id pg, X.v.pages !! id = some pg → (id + 1) * 4096 ≤ l⌝)) := by
    refine fractional_exists' _ (fun l => ?_) (fun l1 l2 p q => ?_)
    · have := QpMul_frac (fun q => mapFields (GF := GF) r.db (DFrac.own q) (some (X.v.base, l)))
        (1 : Qp).half.half
      infer_instance
    · iintro ⟨⟨H1, %h1⟩, ⟨H2, %h2⟩⟩
      icases (and_intro .rfl (mapFields_some_agree r.db X.v.base l1 l2 _ _) :
        mapFields (GF := GF) r.db (DFrac.own (QpMul p (1 : Qp).half.half)) (some (X.v.base, l1)) ∗
          mapFields r.db (DFrac.own (QpMul q (1 : Qp).half.half)) (some (X.v.base, l2)) ⊢ _ ∧ _)
        $$ [H1 H2] with ⟨⟨H1, H2⟩, %he⟩
      · isplitl [H1]
        · iexact H1
        · iexact H2
      subst he
      isplitl [H1]
      · iframe; ipureintro; exact h1
      · iframe; ipureintro; exact h1
  unfold wtxFrac viewW viewOf viewBase
  infer_instance

private instance bytes_discard_persistent_tf (l : Loc) (bs : List w8) :
    Persistent (bytesPointsto (GF := GF) l DFrac.discard bs) :=
  (bytesPointsto_dfractional (GF := GF) l bs).dfractional_persistent

private instance ite_persistent_tf {c : Prop} [Decidable c] (P Q : IProp GF) [Persistent P]
    [Persistent Q] : Persistent (if c then P else Q) := by
  split <;> infer_instance

private instance reg_persistent_tf (tx : Loc) (B : BNs) (r : TxReg) :
    Persistent (reg (GF := GF) tx B r) := by
  unfold reg; infer_instance

private instance isBoltP_persistent_tf (B : BNs) (N : Namespace) (db : Loc) (p : GoString)
    (sp : Loc) (t0 : Nat) : Persistent (isBoltP (GF := GF) B N db p sp t0) := by
  unfold isBoltP; infer_instance

/-- **A reader's bucket is fractional** (its header and page pointers agree). -/
private theorem rBkt_fractional (v : View) (tx b : Loc) (bv : List w8) :
    Fractional (fun q : Qp => rBkt (GF := GF) v tx b (DFrac.own q) bv) := by
  unfold rBkt locOwn
  refine fractional_exists' _ (fun ibp => ?_) (fun i1 i2 p q => ?_)
  · refine fractional_exists' _ (fun pp => ?_) (fun p1 p2 p q => ?_)
    · infer_instance
    · iintro ⟨⟨A1, B1, C1, D1, E1, F1, G1, H1⟩, ⟨A2, B2, C2, D2, E2, F2, G2, H2⟩⟩
      icombine D1 D2 gives %h
      obtain ⟨-, rfl⟩ := h
      isplitl [A1 B1 C1 D1 E1 F1 G1 H1]
      · iframe
      · iframe
  · iintro ⟨⟨%pp1, A1, B1, C1, D1, E1, F1, G1, H1⟩, ⟨%pp2, A2, B2, C2, D2, E2, F2, G2, H2⟩⟩
    icombine A1 A2 gives %h
    obtain ⟨-, rfl⟩ := h
    icombine D1 D2 gives %h'
    obtain ⟨-, rfl⟩ := h'
    isplitl [A1 B1 C1 D1 E1 F1 G1 H1]
    · iexists pp1; iframe
    · iexists pp1; iframe

/-- **A reader's part is fractional** (same registration, view and meta copy). -/
private theorem rtxFrac_fractional (B : BNs) (tx : Loc) (r : TxReg) (T : TxView) (v : View) (mv : Meta) :
    Fractional (fun q => rtxFrac (GF := GF) B tx r q T v mv) := by
  have h1 := rBkt_fractional (GF := GF) v tx (txRoot (GF := GF) tx) (rootVal v)
  have h2 : Fractional (fun q : Qp => iprop(∃ f : w64,
      ((txRoot (GF := GF) tx).[Bucket, go!"FillPercent"] ↦{DFrac.own q} f : IProp GF))) := by
    refine fractional_exists' _ (fun f => inferInstance) (fun x y p q => ?_)
    iintro ⟨H1, H2⟩
    icombine H1 H2 gives %h
    obtain ⟨-, rfl⟩ := h
    iframe
  have h3 := QpMul_frac (fun q => viewCells (GF := GF) q v) rq
  have h7 := fractional_comp (fun q => (tx.[Tx, go!"db"] ↦{DFrac.own q} r.db : IProp GF))
    txDbQ txDbQ_add
  have hq4 : ∀ p q : Qp, (QpMul (p + q) sync.rfrac).half.half =
      (QpMul p sync.rfrac).half.half + (QpMul q sync.rfrac).half.half := by
    intro p q; rw [QpMul_add_l, Qp_half_add, Qp_half_add]
  have hq2 : ∀ p q : Qp, (QpMul (p + q) sync.rfrac).half =
      (QpMul p sync.rfrac).half + (QpMul q sync.rfrac).half := by
    intro p q; rw [QpMul_add_l, Qp_half_add]
  have h8 : Fractional (fun q => iprop(∃ l : Nat,
      ghostVar (GF := GF) B.map (QpMul q sync.rfrac).half.half (some (v.base, l) : MapSt) ∗
      mapFields r.db (DFrac.own (QpMul q sync.rfrac).half) (some (v.base, l) : MapSt) ∗
      ⌜∀ id pg, v.pages !! id = some pg → (id + 1) * 4096 ≤ l⌝)) := by
    refine fractional_exists' _ (fun l => ?_) (fun l1 l2 p q => ?_)
    · have := fractional_comp (fun q => ghostVar (GF := GF) B.map q (some (v.base, l) : MapSt))
        (fun q => (QpMul q sync.rfrac).half.half) hq4
      have := fractional_comp (fun q => mapFields (GF := GF) r.db (DFrac.own q)
        (some (v.base, l) : MapSt)) (fun q => (QpMul q sync.rfrac).half) hq2
      infer_instance
    · iintro ⟨⟨G1, M1, %h1⟩, ⟨G2, M2, %h2⟩⟩
      icombine G1 G2 gives %h
      obtain ⟨-, he⟩ := h
      simp only [Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨-, rfl⟩ := he
      isplitl [G1 M1]
      · iframe; ipureintro; exact h1
      · iframe; ipureintro; exact h1
  unfold rtxFrac viewOf
  refine fractional_exists' _ (fun t => ?_) (fun t1 t2 p q => ?_)
  · infer_instance
  · iintro ⟨⟨A1, B1, C1, D1, E1, F1, G1, H1, I1, J1, K1, L1, M1, %P1⟩,
      ⟨A2, B2, C2, D2, E2, F2, G2, H2, I2, J2, K2, L2, M2, %P2⟩⟩
    icombine B1 B2 gives %e1
    icombine C1 C2 gives %e2
    icombine F1 F2 gives %e3
    icombine G1 G2 gives %e4
    icombine H1 H2 gives %e5
    replace e1 := by first | exact e1.2 | exact e1
    replace e2 := by first | exact e2.2 | exact e2
    replace e3 := by first | exact e3.2 | exact e3
    replace e4 := by first | exact e4.2 | exact e4
    replace e5 := by first | exact e5.2 | exact e5
    rw [e1, e2, e3, e4, e5]
    isplitl [A1 B1 C1 D1 E1 F1 G1 H1 I1 J1 K1 L1 M1]
    · iframe; ipureintro; rw [← e1, ← e3]; exact P1
    · iframe; ipureintro; exact P2

/-- **A reader over the core with a pool loan is fractional.** -/
private theorem rdTx_fractional (B : BNs) (N : Namespace) (tx : Loc) (T : TxView) :
    Fractional (fun q => rdTx (GF := GF) B N tx .loan q T) := by
  unfold rdTx
  simp only [↓reduceIte]
  refine ⟨fun p q => ⟨?_, ?_⟩⟩
  · iintro ⟨%db, %pa, %sp, %t0, %r, %c, %v, %mv, %k, %Hc, #Hreg, #Hb, Hv, Hex, Hw, #Hp⟩
    rw [Qp_half_add]
    icases ((ghostVar_fractional r.n.v (c, TxX.rd v mv k)).fractional _ _).1 $$ Hv with ⟨Hv1, Hv2⟩
    icases ((ghostVar_fractional r.n.ex ()).fractional p q).1 $$ Hex with ⟨He1, He2⟩
    icases ((rtxFrac_fractional B tx r T v mv).fractional p q).1 $$ Hw with ⟨Hw1, Hw2⟩
    isplitl [Hv1 He1 Hw1]
    · iexists db, pa, sp, t0, r, c, v, mv, k; iframe; iframe #; ipureintro; exact Hc
    · iexists db, pa, sp, t0, r, c, v, mv, k; iframe; iframe #; ipureintro; exact Hc
  · iintro ⟨⟨%db, %pa, %sp, %t0, %r, %c, %v, %mv, %k, %Hc, #Hreg, #Hb, Hv, Hex, Hw, #Hp⟩,
      ⟨%db2, %pa2, %sp2, %t02, %r2, %c2, %v2, %mv2, %k2, %Hc2, #Hreg2, -, Hv2, Hex2, Hw2, -⟩⟩
    iunfold reg at Hreg Hreg2
    icombine Hreg Hreg2 gives %hr
    obtain ⟨-, rfl⟩ := hr
    icombine Hv Hv2 gives %hv
    obtain ⟨-, hv⟩ := hv
    simp only [Prod.mk.injEq, TxX.rd.injEq] at hv
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hv
    iexists db, pa, sp, t0, r, c, v, mv, k
    isplitr
    · ipureintro; exact Hc
    iframe Hb Hp
    isplitr
    · iunfold reg; iexact Hreg
    rw [Qp_half_add]
    isplitl [Hv Hv2]
    · iapply ((ghostVar_fractional r.n.v (c, TxX.rd v mv k)).fractional _ _).2; iframe
    isplitl [Hex Hex2]
    · iapply ((ghostVar_fractional r.n.ex ()).fractional p q).2; iframe
    iapply ((rtxFrac_fractional B tx r T v mv).fractional p q).2; iframe

theorem boltTxDef_fractional (B : BNs) (N : Namespace) (tx : Loc) (T : TxView) :
    Fractional (fun q => boltTxDef (GF := GF) B N tx q T) := by
  unfold boltTxDef
  by_cases hrw : T.rw = true
  · simp only [hrw, ↓reduceIte]
    refine ⟨fun p q => ⟨?_, ?_⟩⟩
    · iintro ⟨%db, %pa, %sp, %t0, %r, %c, %X, %Hc, #Hreg, #Hb, Hv, Hex, Hw⟩
      rw [Qp_half_add]
      icases ((ghostVar_fractional r.n.v (c, TxX.wr X)).fractional _ _).1 $$ Hv with ⟨Hv1, Hv2⟩
      icases ((ghostVar_fractional r.n.ex ()).fractional p q).1 $$ Hex with ⟨He1, He2⟩
      icases ((wtxFrac_fractional B tx r T X).fractional p q).1 $$ Hw with ⟨Hw1, Hw2⟩
      isplitl [Hv1 He1 Hw1]
      · iexists db, pa, sp, t0, r, c, X; iframe; iframe #; ipureintro; exact Hc
      · iexists db, pa, sp, t0, r, c, X; iframe; iframe #; ipureintro; exact Hc
    · iintro ⟨⟨%db, %pa, %sp, %t0, %r, %c, %X, %Hc, #Hreg, #Hb, Hv, Hex, Hw⟩,
        ⟨%db2, %pa2, %sp2, %t02, %r2, %c2, %X2, %Hc2, #Hreg2, -, Hv2, Hex2, Hw2⟩⟩
      iunfold reg at Hreg Hreg2
      icombine Hreg Hreg2 gives %hr
      obtain ⟨-, rfl⟩ := hr
      icombine Hv Hv2 gives %hv
      obtain ⟨-, hv⟩ := hv
      simp only [Prod.mk.injEq, TxX.wr.injEq] at hv
      obtain ⟨rfl, rfl⟩ := hv
      iexists db, pa, sp, t0, r, c, X
      isplitr
      · ipureintro; exact Hc
      isplitr
      · iunfold reg; iexact Hreg
      iframe Hb
      rw [Qp_half_add]
      isplitl [Hv Hv2]
      · iapply ((ghostVar_fractional r.n.v (c, TxX.wr X)).fractional _ _).2; iframe
      isplitl [Hex Hex2]
      · iapply ((ghostVar_fractional r.n.ex ()).fractional p q).2; iframe
      iapply ((wtxFrac_fractional B tx r T X).fractional p q).2; iframe
  · have hrw' : T.rw = false := by simpa using hrw
    simp only [hrw', Bool.false_eq_true, ↓reduceIte]
    refine fractional_exists' _ (fun db => ?_) (fun d1 d2 p q => ?_)
    rotate_left
    · iintro ⟨⟨H1, #D1⟩, ⟨H2, -⟩⟩
      isplitl [H1]
      · iframe; iframe #
      · iframe; iframe #
    have := rdTx_fractional (GF := GF) B N tx T
    infer_instance

end txfrac

open Iris.ProofMode in
theorem boltTxDef_agree (B : BNs) (N : Namespace) (tx : Loc) (q1 q2 : Qp) (T1 T2 : TxView) :
    boltTxDef (GF := GF) B N tx q1 T1 ∗ boltTxDef B N tx q2 T2 ⊢ ⌜T1 = T2⌝ := by
  iintro ⟨H1, H2⟩
  icases boltTxDef_ex B N tx q1 T1 $$ H1 with ⟨%r1, Hr1, -, ⟨%c1, %x1, Hv1, %h1⟩, -⟩
  icases boltTxDef_ex B N tx q2 T2 $$ H2 with ⟨%r2, Hr2, -, ⟨%c2, %x2, Hv2, %h2⟩, -⟩
  unfold reg
  icombine Hr1 Hr2 gives %hr
  obtain ⟨-, rfl⟩ := hr
  icombine Hv1 Hv2 gives %hv
  ipureintro
  have : c1 = c2 := (Prod.mk.inj hv.2).1
  rw [h1, h2, this]

open Iris.ProofMode in
theorem boltTxDef_valid (B : BNs) (N : Namespace) (tx : Loc) (q : Qp) (T : TxView) :
    boltTxDef (GF := GF) B N tx q T ⊢ ⌜q ≤ 1⌝ := by
  iintro H
  icases boltTxDef_ex B N tx q T $$ H with ⟨%r, -, Hex, -⟩
  ihave ⟨H1, H2⟩ := (ghostVar_split_half r.n.ex q ()).1 $$ Hex
  icombine H1 H2 gives %h
  ipureintro; rw [Qp.half_add_half] at h; exact h.1

open Iris.ProofMode in
theorem boltTxDef_nonnull (B : BNs) (N : Namespace) (tx : Loc) (q : Qp) (T : TxView) :
    boltTxDef (GF := GF) B N tx q T ⊢ ⌜tx ≠ Loc.null⌝ := by
  unfold boltTxDef
  split
  · unfold wtxFrac
    iintro ⟨%db, %p, %sp, %t0, %r, %c, %X, -, -, -, -, -, ⟨-, -, -, -, -, -, -, -, -, %Hf⟩⟩
    ipureintro; exact Hf.2.2.2.2.2.1
  · unfold rdTx rtxFrac
    iintro ⟨%db', ⟨%db, %p, %sp, %t0, %r, %c, %v, %mv, %k, -, -, -, -, -,
      ⟨%t, -, -, -, -, -, -, -, -, -, -, -, -, -, %Hf⟩, -⟩, -⟩
    ipureintro; exact Hf.2.2.2.2.1

open Iris.ProofMode in
theorem boltTxDef_base (B : BNs) (N : Namespace) (tx : Loc) (q q' : Qp) (T : TxView)
    (D : Data) :
    boltTxDef (GF := GF) B N tx q T ∗ boltStateDef B q' D ⊢ ⌜T.rw = true → T.base = D⌝ := by
  unfold boltTxDef
  split
  · iintro ⟨⟨%db, %p, %sp, %t0, %r, %c, %X, %Hc, -, -, -, -, Hw⟩, Hs⟩
    unfold wtxFrac boltStateDef
    icases Hw with ⟨-, -, -, Hst, -⟩
    icases Hs with ⟨Hs, -⟩
    icombine Hst Hs gives %h
    ipureintro; intro _; exact h.2
  · rename_i h
    iintro -
    ipureintro; intro h'; exact absurd h' h

instance txDBDef_persistent (B : BNs) (N : Namespace) (tx db : Loc) :
    Persistent (txDBDef (GF := GF) B N tx db) := by
  unfold txDBDef isBoltDef isBoltP reg; infer_instance

instance txDoneDef_persistent (tx : Loc) : Persistent (txDoneDef (GF := GF) tx) := by
  unfold txDoneDef; infer_instance

instance boltBktDef_persistent (B : BNs) (tx b : Loc) (n : GoString) (g : Nat) :
    Persistent (boltBktDef (GF := GF) B tx b n g) := by
  unfold boltBktDef reg handleFrag viewOf rBkt locOwn
  refine @exists_persistent _ _ _ _ (fun r => ?_)
  rcases r with ⟨db, n, rw, src⟩
  cases rw <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> infer_instance

instance txBytesDef_persistent (B : BNs) (tx : Loc) (s : GoSlice) (b : GoString) :
    Persistent (txBytesDef (GF := GF) B tx s b) := by
  unfold txBytesDef reg viewOf; infer_instance

private instance rBktP_timeless_l (v : View) (tx b : Loc) (dq : DFrac) (bv : List w8) (ibp pp : Loc) :
    Timeless (rBktP (GF := GF) v tx b dq bv ibp pp) := by
  unfold rBktP locOwn; infer_instance

instance boltCurDef_timeless (B : BNs) (tx c : Loc) (T : TxView) (es : List BoltEnt)
    (pos : Option Nat) : Timeless (boltCurDef (GF := GF) B tx c T es pos) := by
  unfold boltCurDef
  refine @exists_timeless _ _ _ _ (fun r => ?_)
  rcases r with ⟨db, n, rw, src⟩
  unfold reg handleFrag viewOf
  cases rw <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> infer_instance

-- `txBytesDef_acc`: proved in `Read/TxBytes` (U6w; it needs the view's cells' accessors).

open Iris.ProofMode in
/-- **A writer's bucket's `FillPercent`** (`Api.lean`'s `boltTx_fill`): the handle's registry
fragment against `hdlAuth` puts it in `X.handles`, so its points-to is in `fills`, given back with
any non-NaN value. -/
theorem boltTxDef_fill (B : BNs) (N : Namespace) (tx b : Loc) (T : TxView) (n : GoString)
    (g : Nat) (hrw : T.rw = true) :
    boltTxDef (GF := GF) B N tx 1 T ∗ boltBktDef B tx b n g ⊢
      ∃ f : w64, b.[Bucket, go!"FillPercent"] ↦ f ∗
        (∀ f' : w64, ⌜¬ float64IsNaN f'⌝ -∗ b.[Bucket, go!"FillPercent"] ↦ f' -∗
          boltTxDef B N tx 1 T) := by
  unfold boltTxDef boltBktDef reg
  simp only [hrw, ↓reduceIte]
  iintro ⟨⟨%db, %p, %sp, %t0, %r, %c, %X, %Hc, #Hreg, Hb, Hv, Hex, Hw⟩,
    ⟨%r', #Hreg', -, Hh', -⟩⟩
  icombine Hreg Hreg' gives %hr
  obtain ⟨-, rfl⟩ := hr
  unfold handleFrag
  rw [if_pos Hc.2.2]
  unfold wtxFrac hdlAuth
  icases Hw with ⟨Hheap, Hfills, Hcells, Hst, ⟨Hbk, #Hf⟩, Hrest⟩
  ihave %Hl := ghost_map_lookup $$ Hbk Hh'
  unfold fills
  icases (BigSepM.bigSepM_lookup_acc Hl).1 $$ Hfills with ⟨⟨%f, %Hnan, Hfp⟩, Hfb⟩
  iexists f
  iframe Hfp
  iintro %f' %Hnan' Hfp
  iexists db, p, sp, t0, r, c, X
  isplitr
  · ipureintro; exact Hc
  isplitr
  · iexact Hreg
  iframe Hb Hv Hex Hheap Hcells Hst Hbk Hrest
  isplitl [Hfb Hfp]
  · iapply Hfb
    iexists f'; iframe Hfp; ipureintro; exact Hnan'
  iexact Hf

/-- **A reader's `boltTx` is its `rdTx` with a pool loan, and the database** (design §3.13):
the public reader triples are corollaries of the internal ones over `rdTx`. -/
theorem boltTx_rdTx (B : BNs) (N : Namespace) (tx : Loc) (q : Qp) (T : TxView)
    (hro : T.rw = false) :
    boltTxDef (GF := GF) B N tx q T ⊣⊢ ∃ db, rdTx B N tx .loan q T ∗ isBoltDef B N db := by
  unfold boltTxDef; simp only [hro, Bool.false_eq_true, ↓reduceIte]; exact .rfl

end tx

end bbolt
end EtcdGrove
end Perennial
