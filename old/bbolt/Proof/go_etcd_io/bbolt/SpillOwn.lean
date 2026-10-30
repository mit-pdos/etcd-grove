/-
A write transaction's objects during `Commit`'s spill, as resources.

`node.splitTwo` leaves the first part of a split node with a prefix of its old inodes slice and
no capacity of its own (the rest of the array is the second part's): such a node is not
`nodeOwn` (which holds its inodes' capacity). It is never appended to again (a spilled node is
not modified), but `dereference` (a remap inside `Tx.allocate`) still reaches it through its
parent's children. So during the spill a node is `nodeOwnX`: `nodeOwn` without the inodes'
capacity (`nodeOwn_X`), the buckets `bktOwnX`, the transaction `ownWriteTxGX`; the capacities
of the nodes that still have one are held apart (`capsOwn`).
-/
module

public import Proof.go_etcd_io.bbolt.WriteAlloc
public import Proof.go_etcd_io.bbolt.WriteTxLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [ext : FfiSyntax]

/-- `T'` (`T` dereferenced) keeps each node's struct but its key (in particular its inodes slice,
whose capacity is held apart: `capsOwn`). -/
def derefKeep (T T' : WTx) : Prop :=
  ∀ bl B B' l r r', T.bs !! bl = some B → T'.bs !! bl = some B' → B.ns !! l = some r →
    B'.ns !! l = some r' → r'.nv = { r.nv with key' := r'.nv.key' }

/-- The node keeps no byte of the view. -/
def noViewRec (r : NRec) : Prop :=
  (∀ w ∈ r.ws, w.ks ≠ Src.view ∧ w.vs ≠ Src.view) ∧ r.ksrc ≠ Src.view

/-- The live nodes of the bucket `B` (`liveNodes`), its root node's parent chain allowed to
start with nodes outside the tree `S` (`dereference` reaches them only through `node.root`):
those keep no byte of the view. During the spill of a split root, the old root is cut from its
new parent's children (`n.children = nil`) while still the bucket's `rootNode`. -/
def liveNodesX (B : BRec) (S : List Loc) : Prop :=
  ∃ p top, upPath B.ns B.bv.rootNode' p top ∧ p.Nodup ∧ kidsTree B.ns top S ∧
    ∀ l ∈ p, l ∉ S → ∃ r, B.ns !! l = some r ∧ noViewRec r

/-- What `dereference` of the root bucket `rl` needs during the spill (`derefReady`, its live
nodes `liveNodesX`). -/
def derefReadyX (T : WTx) (rl : Loc) : Prop :=
  (T.bs !! rl).isSome ∧ (∀ bl, (T.bs !! bl).isSome → bktReach T rl bl) ∧
  (∃ dep : Loc → Nat, ∀ bl B name c, T.bs !! bl = some B → B.bm !! name = some c → dep c < dep bl) ∧
  ∀ bl B, T.bs !! bl = some B →
    (B.bv.rootNode' = null ∨ ∃ S, liveNodesX B S ∧ ∀ l ∈ S, ∃ r, B.ns !! l = some r ∧ derefOK bl r) ∧
    ∀ name c, B.bm !! name = some c → (T.bs !! c).isSome

/-- An entry without the view's bytes. -/
def staleW (w : WEntry) : WEntry := { w with ks := staleOf w.ks, vs := staleOf w.vs }

/-- A node without the view's bytes. -/
def staleRec (r : NRec) : NRec := { r with ws := r.ws.map staleW, ksrc := staleOf r.ksrc }

theorem staleOf_ne_view (s : Src) : staleOf s ≠ Src.view := by
  cases s <;> simp [staleOf]

theorem staleRec_noView (r : NRec) : noViewRec (staleRec r) := by
  refine ⟨fun w hw => ?_, staleOf_ne_view _⟩
  obtain ⟨w0, -, rfl⟩ := List.mem_map.1 hw
  exact ⟨staleOf_ne_view _, staleOf_ne_view _⟩

/-- `r'` is `r` dereferenced (`derefNode`), a non-nil key with bytes kept non-nil. -/
def derefNodeX (r r' : NRec) : Prop :=
  derefNode r r' ∧ (r.nv.key' ≠ slice.nil → 0 < r.key.length → r'.nv.key' ≠ slice.nil)

/-- The bucket `B'` is `B` dereferenced (`derefBkt`): a node of the tree is dereferenced, one of
the root's parent chain outside it is as it was (it keeps no byte of the view). -/
def derefBktX (B B' : BRec) : Prop :=
  B'.bv = B.bv ∧ B'.ib = B.ib ∧ B'.nm = B.nm ∧ B'.bm = B.bm ∧ B'.ipg = B.ipg ∧
  B'.isrc = staleOf B.isrc ∧
  (∀ l r', B'.ns !! l = some r' → ∃ r, B.ns !! l = some r ∧
    (derefNodeX r r' ∨ (r' = r ∧ noViewRec r) ∨ r' = staleRec r)) ∧
  (B.bv.rootNode' ≠ null → ∀ S p top, upPath B.ns B.bv.rootNode' p top → p.Nodup →
    kidsTree B.ns top S → (∀ l ∈ p, l ∉ S → ∃ r, B.ns !! l = some r ∧ noViewRec r) →
    ∀ l, l ∈ S ∨ l ∈ p → (B'.ns !! l).isSome ∧ ∀ r r', B.ns !! l = some r → B'.ns !! l = some r' →
      (derefNodeX r r' ∨ (r' = r ∧ noViewRec r))) ∧
  (∀ l, (B.ns !! l).isSome → (B'.ns !! l).isSome)

/-- `T'` is `T` dereferenced (`derefRel`, its buckets `derefBktX`). -/
def derefRelX (T T' : WTx) : Prop :=
  T'.t = { T.t with stats' := T'.t.stats' } ∧ T'.mv = T.mv ∧ T'.pm = T.pm ∧ T'.bufs = T.bufs ∧
  (∀ bl, (T.bs !! bl).isSome ↔ (T'.bs !! bl).isSome) ∧
  ∀ bl B B', T.bs !! bl = some B → T'.bs !! bl = some B' → derefBktX B B'

end pure

section own
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- The node at `l` (record `r`) without its inodes' capacity. -/
def nodeOwnX (W : WView) (l : Loc) (r : NRec) : IProp GF :=
  iprop(l ↦ r.nv ∗ r.nv.inodes' ↦* r.ins ∗
    ([∗list] it;w ∈ r.ins;r.ws, wOwn W it w) ∗
    r.nv.children' ↦* r.cs ∗ ownSliceCap Loc r.nv.children' (DFrac.own 1) ∗
    (if r.nv.key' = slice.nil then iprop(True) else srcOwn W r.nv.key' r.ksrc r.key))

/-- A node's inodes' capacity. -/
def capOwn (r : NRec) : IProp GF := ownSliceCap Inode r.nv.inodes' (DFrac.own 1)

theorem nodeOwn_X (W : WView) (l : Loc) (r : NRec) :
    nodeOwn (GF := GF) W l r ⊣⊢ nodeOwnX W l r ∗ capOwn r := by
  unfold nodeOwn nodeOwnX capOwn
  constructor
  · iintro ⟨Hn, Hins, Hcap, Hents, Hch, Hchcap, Hkey⟩
    iframe
  · iintro ⟨⟨Hn, Hins, Hents, Hch, Hchcap, Hkey⟩, Hcap⟩
    iframe

/-- The bucket at `bl` (record `B`), its nodes `nodeOwnX`. -/
def bktOwnX (W : WView) (bl : Loc) (B : BRec) : IProp GF :=
  iprop(bl ↦ B.bv ∗ B.bv.InBucket' ↦ B.ib ∗ B.bv.nodes' ↦$ B.nm ∗ B.bv.buckets' ↦$ B.bm ∗
    pageOwn W B ∗ [∗map] l ↦ r ∈ B.ns, nodeOwnX W l r)

theorem bigSepM_nodeOwn_X (W : WView) (ns : GMap Loc NRec) :
    ([∗map] l ↦ r ∈ ns, nodeOwn (GF := GF) W l r) ⊣⊢
      ([∗map] l ↦ r ∈ ns, nodeOwnX W l r) ∗ [∗map] _l ↦ r ∈ ns, capOwn r := by
  rw [← BigSepM.bigSepM_sep_eq]
  exact ⟨BigSepM.bigSepM_mono_of_forall (fun {l r} => (nodeOwn_X W l r).1),
    BigSepM.bigSepM_mono_of_forall (fun {l r} => (nodeOwn_X W l r).2)⟩

theorem bktOwn_X (W : WView) (bl : Loc) (B : BRec) :
    bktOwn (GF := GF) W bl B ⊣⊢ bktOwnX W bl B ∗ [∗map] _l ↦ r ∈ B.ns, capOwn r := by
  unfold bktOwn bktOwnX
  constructor
  · iintro ⟨Hbv, Hib, Hnm, Hbm, Hpg, Hns⟩
    icases (bigSepM_nodeOwn_X W B.ns).1 $$ Hns with ⟨Hns, Hc⟩
    iframe
  · iintro ⟨⟨Hbv, Hib, Hnm, Hbm, Hpg, Hns⟩, Hc⟩
    ihave Hns := (bigSepM_nodeOwn_X W B.ns).2 $$ [Hns Hc]
    · iframe
    iframe

/-- The transaction's resources (`ownWriteTxG`), its nodes `nodeOwnX`. -/
def ownWriteTxGX (W : WView) (txl : Loc) (T : WTx) : IProp GF :=
  iprop(TxW_rest_root txl (DFrac.own 1) T.t ∗ T.t.meta' ↦ T.mv ∗ T.t.pages' ↦$ T.pm ∗
    ([∗map] id ↦ p ∈ T.pm, ∃ bs, ⌜T.bufs !! id = some bs⌝ ∗ bytesPointsto p (DFrac.own 1) bs) ∗
    [∗map] bl ↦ B ∈ T.bs, bktOwnX W bl B)

/-- The capacities of the nodes of `T` outside `K` (the nodes without one). -/
def capsOwn (T : WTx) (K : Loc → Bool) : IProp GF :=
  [∗map] _bl ↦ B ∈ T.bs, [∗map] l ↦ r ∈ B.ns, if K l then iprop(emp) else capOwn r

theorem ownWriteTxG_X (W : WView) (txl : Loc) (T : WTx) :
    ownWriteTxG (GF := GF) W txl T ⊣⊢ ownWriteTxGX W txl T ∗ capsOwn T (fun _ => false) := by
  unfold ownWriteTxG ownWriteTxGX capsOwn
  dsimp only
  have e : ([∗map] _bl ↦ B ∈ T.bs, [∗map] l ↦ r ∈ B.ns,
      (if false then iprop(emp) else capOwn (GF := GF) r)) =
      ([∗map] _bl ↦ B ∈ T.bs, [∗map] _l ↦ r ∈ B.ns, capOwn (GF := GF) r) :=
    BigSepM.bigSepM_eq_of_forall_eq (fun {_ B} =>
      BigSepM.bigSepM_eq_of_forall_eq (fun {_ _} => rfl))
  rw [e]
  have e2 : ([∗map] bl ↦ B ∈ T.bs, bktOwn (GF := GF) W bl B) ⊣⊢
      ([∗map] bl ↦ B ∈ T.bs, bktOwnX W bl B) ∗
        [∗map] _bl ↦ B ∈ T.bs, [∗map] _l ↦ r ∈ B.ns, capOwn (GF := GF) r := by
    rw [← BigSepM.bigSepM_sep_eq]
    exact ⟨BigSepM.bigSepM_mono_of_forall (fun {bl B} => (bktOwn_X W bl B).1),
      BigSepM.bigSepM_mono_of_forall (fun {bl B} => (bktOwn_X W bl B).2)⟩
  constructor
  · iintro ⟨Ht, Hm, Hpm, Hbufs, Hbs⟩
    icases e2.1 $$ Hbs with ⟨Hbs, Hc⟩
    iframe
  · iintro ⟨⟨Ht, Hm, Hpm, Hbufs, Hbs⟩, Hc⟩
    ihave Hbs := e2.2 $$ [Hbs Hc]
    · iframe
    iframe

theorem nodeOwnX_other (W W' : WView) (l : Loc) (r : NRec)
    (h : (∀ w ∈ r.ws, w.ks ≠ Src.view ∧ w.vs ≠ Src.view) ∧ r.ksrc ≠ Src.view) :
    nodeOwnX (GF := GF) W l r ⊢ nodeOwnX W' l r := by
  unfold nodeOwnX
  iintro ⟨Hn, Hins, Hents, Hch, Hchcap, Hkey⟩
  iframe Hn Hins Hch Hchcap
  isplitl [Hents]
  · iapply (BigSepL2.bigSepL2_mono (Φ := fun _ it w => wOwn (GF := GF) W it w)
      (Ψ := fun _ it w => wOwn (GF := GF) W' it w) ?_) $$ Hents
    intro k it w _ hw
    have hw' := h.1 w (List.mem_of_getElem? hw)
    unfold wOwn
    rw [srcOwn_other W W' _ _ _ hw'.1, srcOwn_other W W' _ _ _ hw'.2]
  · rw [srcOwn_other W W' _ _ _ h.2]
    iexact Hkey

/-- Buckets keeping no byte of the view stand over any view. -/
theorem bsX_reattach (W W' : WView) (bs : GMap Loc BRec)
    (h : ∀ bl B, bs !! bl = some B → B.isrc ≠ Src.view ∧
      ∀ l r, B.ns !! l = some r → (∀ w ∈ r.ws, w.ks ≠ Src.view ∧ w.vs ≠ Src.view) ∧
        r.ksrc ≠ Src.view) :
    ([∗map] bl ↦ B ∈ bs, bktOwnX (GF := GF) W bl B) ⊢ [∗map] bl ↦ B ∈ bs, bktOwnX W' bl B := by
  iintro Hbs
  iapply (BigSepM.bigSepM_mono (M := GMap Loc) (Φ := fun bl B => bktOwnX (GF := GF) W bl B)
    (Ψ := fun bl B => bktOwnX (GF := GF) W' bl B) ?_) $$ Hbs
  intro bl B hB
  obtain ⟨hi, hn⟩ := h bl B hB
  unfold bktOwnX
  iintro ⟨Hbv, Hib, Hnm, Hbm, Hpg, Hns⟩
  iframe Hbv Hib Hnm Hbm
  rw [pageOwn_other W W' B hi]
  iframe Hpg
  iapply (BigSepM.bigSepM_mono (M := GMap Loc) (Φ := fun l r => nodeOwnX (GF := GF) W l r)
    (Ψ := fun l r => nodeOwnX (GF := GF) W' l r) ?_) $$ Hns
  intro l r hr
  exact nodeOwnX_other W W' l r (hn l r hr)

theorem srcOwn_stale (W : WView) (sl : GoSlice) (src : Src) (bs : List w8) :
    srcOwn (GF := GF) W sl src bs ⊢ srcOwn W sl (staleOf src) bs := by
  cases src with
  | view => unfold srcOwn staleOf; iintro -; ipureintro; trivial
  | own d => exact .rfl
  | stale => exact .rfl

theorem keyOwn_stale (W : WView) (r : NRec) :
    (if r.nv.key' = slice.nil then iprop(True) else srcOwn (GF := GF) W r.nv.key' r.ksrc r.key) ⊢
      (if r.nv.key' = slice.nil then iprop(True) else srcOwn W r.nv.key' (staleOf r.ksrc) r.key) := by
  split
  · exact .rfl
  · exact srcOwn_stale W _ _ _

theorem nodeOwnX_stale (W : WView) (l : Loc) (r : NRec) :
    nodeOwnX (GF := GF) W l r ⊢ nodeOwnX W l (staleRec r) := by
  unfold nodeOwnX staleRec
  iintro ⟨Hn, Hi, Hents, Hch, Hcap, Hkey⟩
  iframe Hn Hi Hch Hcap
  isplitl [Hents]
  · iapply (BigSepL2.bigSepL2_map_right (f := staleW)).2
    iapply (BigSepL2.bigSepL2_mono (fun {k it w} _ _ => ?_)) $$ Hents
    unfold wOwn staleW
    iintro ⟨%h, Hk, Hv⟩
    isplitr
    · ipureintro; exact h
    isplitl [Hk]
    · iapply srcOwn_stale; iexact Hk
    · iapply srcOwn_stale; iexact Hv
  · iapply (keyOwn_stale W r); iexact Hkey

end own

end bbolt
end EtcdGrove
end Perennial
