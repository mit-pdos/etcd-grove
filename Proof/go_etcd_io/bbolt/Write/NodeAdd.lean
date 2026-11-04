/-
U7d's (`notes/bbolt-proof-plan.md`) heap steps of `Bucket.node`'s uncached case: a freshly
allocated node is no node object of the heap (`wtxHeap_fresh`), and the bucket's record changed
(its node cache, its root node, its branch parent's children) with the new node added
(`wtxHeap_nodeAdd_acc`), then registered (`wtxHeap_nloc_insert`).
-/
module

public import Proof.go_etcd_io.bbolt.Write.Heap
public import Proof.go_etcd_io.bbolt.Rebalance.HeapRbl
public import Proof.go_etcd_io.bbolt.Inv.Ctx

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

namespace Write

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [GooseExts]

/-- Every object of `objs` is a node. -/
theorem objs_isNode (T : WTx) (hd : objsDisj T) (l : Loc) (o : WObj) (h : T.objs !! l = some o) :
    ∃ bl r, o = .node bl r := by
  by_cases hk : ∃ c C rk, T.bs !! c = some C ∧ C.ns !! l = some rk
  · obtain ⟨c, C, rk, hC, hrk⟩ := hk
    rw [objs_node T c C l rk hd hC hrk] at h
    cases h; exact ⟨c, rk, rfl⟩
  · have hno : ∀ c C, T.bs !! c = some C → C.ns !! l = none := by
      intro c C hC
      cases h' : C.ns !! l with
      | none => rfl
      | some rk => exact absurd ⟨c, C, rk, hC, h'⟩ hk
    rw [objs_other T l hno] at h
    unfold WTx.deadObjs at h
    rw [GMap.lookup_fmap] at h
    cases hd' : T.dead !! l with
    | none => rw [hd'] at h; cases h
    | some p => rw [hd'] at h; cases h; exact ⟨p.1, p.2, rfl⟩

/-- A location no node object has stays none after a bucket's record changes at its own nodes
(`Ls`) only, `l` not among them. -/
theorem objs_setBkt_none (X : WX) (bl l : Loc) (B' : BRec) (hl : X.t.objs !! l = none) (hns : B'.ns !! l = none) :
    (X.setBkt bl B').t.objs !! l = none := by
  have hno := objs_none X.t l hl
  have hno' : ∀ c C, (X.setBkt bl B').t.bs !! c = some C → C.ns !! l = none := by
    intro c C hC
    by_cases hcb : c = bl
    · subst hcb
      simp only [WX.setBkt, GMap.lookup_insert, Option.some.injEq] at hC
      subst hC; exact hns
    · simp only [WX.setBkt, GMap.lookup_insert_ne _ _ (Ne.symm hcb)] at hC
      exact hno c C hC
  rw [objs_other _ l hno']
  rw [objs_other X.t l hno] at hl
  exact hl

end pure

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

omit hos in
/-- Two full points-tos of one pointer cell conflict. -/
theorem loc_pointsto_excl (p a b : Loc) :
    (p ↦ a : IProp GF) ∗ p ↦ b ⊢ False := by
  rw [typedPointsto_unseal]; unfold typedPointstoWrap
  iintro ⟨⟨H1, -⟩, ⟨H2, -⟩⟩
  rw [show @TypedPointsto.typedPointstoDef GF Loc _ p a (DFrac.own 1) =
    heapPointsto p (DFrac.own 1) #a from rfl]
  rw [show @TypedPointsto.typedPointstoDef GF Loc _ p b (DFrac.own 1) =
    heapPointsto p (DFrac.own 1) #b from rfl]
  icombine H1 H2 gives %He
  exact absurd He.1 (dfrac_own_one_op_invalid _)

omit hos in
/-- Two full points-tos of one node conflict. -/
theorem node_pointsto_excl (l : Loc) (a b : node) :
    (l ↦ a : IProp GF) ∗ l ↦ b ⊢ False := by
  iintro ⟨Ha, Hb⟩
  icases typedPointsto_split _ _ _ $$ Ha with Ha
  icases typedPointsto_split _ _ _ $$ Hb with Hb
  simp only [TypedPointsto.typedPointstoDef]
  icases Ha with ⟨Ha, -⟩
  icases Hb with ⟨Hb, -⟩
  iapply loc_pointsto_excl _ a.bucket' b.bucket'
  iframe

omit hos in
/-- **A fresh node is no node object** of the heap at `1` (every object is a node, whose struct
the heap owns). -/
theorem wtxHeap_fresh (tx : Loc) (X : WX) (l : Loc) (nv : node) :
    wtxHeap (GF := GF) tx (DFrac.own 1) X ∗ l ↦ nv ⊢
      wtxHeap tx (DFrac.own 1) X ∗ l ↦ nv ∗ ⌜X.t.objs !! l = none⌝ := by
  iintro ⟨H, Hl⟩
  ihave %Hd := wtxHeap_objsDisj tx (DFrac.own 1) X $$ H
  cases ho : X.t.objs !! l with
  | none => iframe; ipureintro; rfl
  | some o =>
    obtain ⟨bl, r, rfl⟩ := objs_isNode X.t Hd l o ho
    icases wtxHeap_node_ptr_acc tx (DFrac.own 1) X bl l r ho $$ H with ⟨Hn, -⟩
    iexfalso
    iapply node_pointsto_excl l r.nv nv
    iframe

omit hos in
/-- **The registry gains a node object** (`heapOK`'s registry clause). -/
theorem wtxHeap_nloc_insert (tx : Loc) (dq : DFrac) (X : WX) (l : Loc) (y : Loc × Nat)
    (hl : (X.t.objs !! l).isSome) :
    wtxHeap (GF := GF) tx dq X ⊢ wtxHeap tx dq { X with nloc := X.nloc.insert l y } := by
  unfold wtxHeap
  iintro ⟨%Hok, Hf, Hrf, Hm, Hbk⟩
  isplitr
  · ipureintro
    refine ⟨Hok.1, Hok.2.1, Hok.2.2.1, Hok.2.2.2.1, ?_, Hok.2.2.2.2.2⟩
    intro n y' hn
    by_cases hk : l = n
    · subst hk; exact hl
    · rw [GMap.lookup_insert_ne _ _ hk] at hn
      exact Hok.2.2.2.2.1 n y' hn
  isplitl [Hf]
  · unfold txFields; iexact Hf
  iframe

/-- **`Bucket.node`'s heap step**: the bucket's object and some of its live nodes (`Ls`, the
parent) out with the transaction's fields; back with a new record `B'` of the bucket (its nodes
`B`'s but at `Ls`), the nodes' new records, and the fresh node `l` (record `r`) added. -/
theorem wtxHeap_nodeAdd_acc (tx : Loc) (X : WX) (bl l : Loc) (B : BRec) (Ls : List Loc)
    (f : Loc → NRec) (hb : X.t.bs !! bl = some B) (hnd : Ls.Nodup)
    (hf : ∀ k ∈ Ls, B.ns !! k = some (f k)) (hl : X.t.objs !! l = none) :
    wtxHeap (GF := GF) tx (DFrac.own 1) X ⊢
      ([∗list] k ∈ Ls, objOwn X.v k (DFrac.own 1) (decide (k ∈ X.live)) (.node bl (f k))) ∗
      objOwn X.v bl (DFrac.own 1) (decide (bl ∈ X.liveB)) (.bkt B) ∗
      txFields tx (DFrac.own 1) X ∗ rootFill tx (DFrac.own 1) ∗
      (∀ (B' : BRec) (f' : Loc → NRec) (r : NRec), ⌜(∀ k ∈ Ls, B'.ns !! k = some (f' k)) ∧
          (∀ k, k ∉ Ls → B'.ns !! k = B.ns !! k) ∧ B'.bv.tx' = B.bv.tx' ∧
          (∀ k ∈ Ls, (f' k).nv.parent' ≠ k) ∧ r.nv.parent' ≠ l⌝ -∗
        ([∗list] k ∈ Ls, objOwn X.v k (DFrac.own 1) (decide (k ∈ X.live)) (.node bl (f' k))) -∗
        objOwn X.v bl (DFrac.own 1) (decide (bl ∈ X.liveB)) (.bkt B') -∗
        txFields tx (DFrac.own 1) X -∗ rootFill tx (DFrac.own 1) -∗
        objOwn X.v l (DFrac.own 1) true (.node bl r) -∗
        wtxHeap tx (DFrac.own 1) ((X.setBkt bl B').addNode bl l B' r)) := by
  iintro H
  ihave %Hd := wtxHeap_objsDisj tx (DFrac.own 1) X $$ H
  icases wtxHeap_setBkt_acc tx (DFrac.own 1) X bl B Ls f hb hnd hf $$ H
    with ⟨HL, Hb, Hf, Hrf, Hback⟩
  iframe HL Hb Hf Hrf
  iintro %B' %f' %r %Hc HL Hb Hf Hrf Hn
  obtain ⟨hf', hout, htx, hpar, hrp⟩ := Hc
  ihave H := Hback $$ %B' %f' [] [HL] [Hb] [Hf] [Hrf]
  · ipureintro; exact ⟨hf', hout, htx, hpar⟩
  · iexact HL
  · iexact Hb
  · iexact Hf
  · iexact Hrf
  have hlB : B.ns !! l = none := objs_none X.t l hl bl B hb
  have hlL : l ∉ Ls := by
    intro hk; rw [hf l hk] at hlB; cases hlB
  have hns : B'.ns !! l = none := by rw [hout l hlL]; exact hlB
  iapply wtxHeap_node_insert tx (DFrac.own 1) (X.setBkt bl B') bl l B' r
    (by simp [WX.setBkt]) (objs_setBkt_none X bl l B' hl hns) hrp
  iframe

/-- The source `Bucket.node` reads an inline page as: the view while the page is view-backed,
else the bucket's persistent bytes. -/
def inlSrc (B : BRec) : Src := if B.pst = PageSt.view then Src.view else Src.own DFrac.discard

omit hos in
/-- **An inline page's bytes, as `node.read` takes them** (`srcLoc`), from the bucket's
`pageOwn`. -/
theorem pageOwn_srcLoc (v : View) (B : BRec)
    (hsrc : B.pst = PageSt.view ∨ ∃ dq, B.isrc = Src.own dq) (hp : B.bv.page' ≠ null) :
    pageOwn (GF := GF) v B ⊢ pageOwn v B ∗ srcLoc v B.bv.page' (inlSrc B) B.ipg := by
  by_cases hv : B.pst = PageSt.view
  · unfold pageOwn inlSrc srcLoc
    rw [hv]
    simp only [↓reduceIte]
    iintro %H
    isplitl [] <;> ipureintro <;> exact H
  · obtain ⟨dq0, hdq⟩ := hsrc.resolve_left hv
    have e : pageOwn (GF := GF) v B = bytesPointsto B.bv.page' DFrac.discard B.ipg := by
      unfold pageOwn; cases h : B.pst <;> simp_all
    rw [e]
    unfold inlSrc srcLoc
    simp only [hv, ↓reduceIte]
    iintro #H
    iframe #

end heap

end Write

end bbolt
end EtcdGrove
end Perennial
