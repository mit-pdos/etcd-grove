/-
The writer's search (U6d, `notes/bbolt-proof-plan.md`), its resources: `wtxW` opened on the view's
cells (with the view's base positive), on a live node with the cells, and the bytes of the page at
a position of a live bucket with their source (`srcLoc`; `pgSrc`: the view, or an inline page's
source as `Bucket.node` reads it), and a page's bytes together with a key's.
-/
module

public import Proof.go_etcd_io.bbolt.Read.WPos
public import Proof.go_etcd_io.bbolt.Read.Base
public import Proof.go_etcd_io.bbolt.Write.NodeAdd
public import Proof.go_etcd_io.bbolt.Write.ReadPage
public import Proof.go_etcd_io.bbolt.Rebalance.Base
public import Proof.go_etcd_io.bbolt.Rebalance.BktRbl

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pgsrc
variable [GooseExts]

/-- The source of the bytes of the page at a position of `B` (`wpageAt`): the view's, or an inline
page's as `Bucket.node` reads it (`Write.inlSrc`). -/
def pgSrc (B : BRec) : Src := if B.ib.root' = W64 0 then Write.inlSrc B else Src.view

theorem pgSrc_ne_stale (B : BRec) : pgSrc B ≠ Src.stale := by
  unfold pgSrc Write.inlSrc; split <;> (try split) <;> intro h <;> cases h

/-- Under `inlSrcOK`, an inline page's source is its bucket's (`leafSrc`'s). -/
theorem pgSrc_inl (X : WX) (bl : Loc) (B : BRec) (hB : X.t.bs !! bl = some B) (hi : inlSrcOK X bl)
    (h0 : B.ib.root' = W64 0) (hrn : B.bv.rootNode' = null) : pgSrc B = B.isrc := by
  unfold pgSrc Write.inlSrc
  rw [if_pos h0]
  rcases hi B hB h0 hrn with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [if_pos h2, h1]
  · rw [h2, h1]; rfl

end pgsrc

section wctx
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The view's cells, out of `wtxW`** (the view's base positive), and back. -/
theorem wtxW_cells_acc (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) :
    wtxW (GF := GF) K tx r m X ⊢ ⌜0 < X.v.base.addr⌝ ∗ viewCells wq X.v ∗
      (viewCells wq X.v -∗ wtxW K tx r m X) := by
  unfold wtxW
  iintro ⟨Hcore, Hcells, ⟨%l, Hmf, %Hl⟩⟩
  ihave %Hnn := mapFields_base_nonnull _ _ _ _ $$ Hmf
  iframe Hcells
  isplitr
  · ipureintro; exact Hnn
  iintro Hcells
  iframe
  ipureintro; exact Hl

/-- **A live node and the view's cells, out of `wtxW`**, and back. -/
theorem wtxW_node_cells_acc (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (bl : Loc)
    (B : BRec) (n : Loc) (rn : NRec) (hb : X.t.bs !! bl = some B) (hn : B.ns !! n = some rn)
    (hl : n ∈ X.live) :
    wtxW (GF := GF) K tx r m X ⊢ ⌜0 < X.v.base.addr⌝ ∗ objOwn X.v n (DFrac.own 1) true (.node bl rn) ∗
      viewCells wq X.v ∗
      (objOwn X.v n (DFrac.own 1) true (.node bl rn) -∗ viewCells wq X.v -∗ wtxW K tx r m X) := by
  unfold wtxW wtxCore
  iintro ⟨⟨#Hpkg, #Hcore, %Hr, #Hreg, Hh, Hfills, Hbk, Hnl, Hdb, Hview, Hst⟩, Hc, ⟨%l, Hmf, %Hl⟩⟩
  ihave %Hnn := mapFields_base_nonnull _ _ _ _ $$ Hmf
  icases wtxHeap_live_node_acc tx (DFrac.own 1) X bl B n rn hb hn hl $$ Hh with ⟨Ho, Hback⟩
  iframe Ho Hc
  isplitr
  · ipureintro; exact Hnn
  iintro Ho Hc
  ihave Hh := Hback $$ Ho
  iframe; iframe #
  isplitr
  · ipureintro; exact Hr
  ipureintro; exact Hl

omit [GooseSemantics] go_gctx sem hos in
/-- The view page `id`'s bytes are bytes of the view. -/
theorem srcLoc_view_page (v : View) (id : Nat) (pg : List w8) (h : v.pages !! id = some pg) :
    ⊢ srcLoc (GF := GF) v (pageLoc v id) Src.view pg := by
  unfold srcLoc
  ipureintro
  have := inViewLoc_page v id pg h 0 pg.length (by omega)
  rw [bytesAt_drop' pg] at this
  simpa [pageLoc] using this

/-- **The page at a position of a live bucket, with its source** (`srcLoc`, persistent). -/
theorem wtxW_page_srcLoc (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (bl : Loc) (B : BRec)
    (pid : w64) (pa : Loc) (pg : List w8) (hb : X.t.bs !! bl = some B) (hl : bl ∈ X.liveB)
    (hw : wpageAt X.v B pid = some (pa, pg))
    (hsrc : B.ib.root' = W64 0 → B.pst = PageSt.view ∨ ∃ dq, B.isrc = Src.own dq)
    (hpa : B.ib.root' = W64 0 → B.bv.page' ≠ null) :
    wtxW (GF := GF) K tx r m X ⊢ wtxW K tx r m X ∗ srcLoc X.v pa (pgSrc B) pg := by
  by_cases hin : B.ib.root' = W64 0
  · unfold wpageAt at hw
    rw [if_pos hin] at hw
    split at hw
    · simp only [Option.some.injEq, Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      unfold pgSrc
      rw [if_pos hin]
      iintro Hw
      icases wtxW_bkt_acc K tx r m X bl B hb $$ Hw with ⟨Ho, Hback⟩
      rw [show decide (bl ∈ X.liveB) = true from decide_eq_true hl]
      unfold objOwn
      icases Ho with ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, Hpo⟩
      try simp only [↓reduceIte]
      icases Write.pageOwn_srcLoc X.v B (hsrc hin) (hpa hin) $$ Hpo with ⟨Hpo, #Hs⟩
      iframe Hs
      iapply Hback
      iframe
    · cases hw
  · unfold wpageAt at hw
    rw [if_neg hin] at hw
    obtain ⟨pg0, hpg, e⟩ := Option.map_eq_some_iff.1 hw
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    unfold pgSrc
    rw [if_neg hin]
    iintro Hw
    iframe Hw
    have := srcLoc_view_page (GF := GF) X.v pid.toNat pg0 hpg
    unfold pageLoc at this
    iapply this

/-- **A page's bytes and a key's, through their sources and the view's cells**, and back. -/
theorem cells_page_key_acc (q : Qp) (v : View) (hb : 0 < v.base.addr) (pa : Loc) (s : Src)
    (pg : List w8) (key : GoSlice) (ks : Src) (kb : List w8) (hks : ks ≠ Src.stale) :
    srcLoc (GF := GF) v pa s pg ∗ srcOwn v key ks kb ∗ viewCells q v ⊢ ∃ dq dk,
      bytesPointsto pa dq pg ∗ key ↦*{dk} kb ∗
      (bytesPointsto pa dq pg -∗ key ↦*{dk} kb -∗ viewCells q v) := by
  iintro ⟨#Hs, #Hk, Hc⟩
  icases (viewCells_halves q v).1 $$ Hc with ⟨Hc1, Hc2⟩
  icases Write.srcLoc_acc q.half v pa s pg $$ [Hc1] with ⟨%dq, Hp, Hpb⟩
  · iframe; iframe #
  icases srcOwn_acc q.half v key ks kb hks hb $$ [Hc2] with ⟨%dk, Hkey, Hkb⟩
  · iframe; iframe #
  iexists dq, dk
  iframe Hp Hkey
  iintro Hp Hkey
  ihave Hc1 := Hpb $$ Hp
  icases Hkb $$ Hkey with ⟨-, Hc2⟩
  iapply (viewCells_halves q v).2
  iframe

/-- **Every view page is within `db.page`'s range** (`Tx.page`'s premise), from `wtxW`'s mapping. -/
theorem wtxW_page_maxMap (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) :
    wtxW (GF := GF) K tx r m X ⊢
      ⌜∀ id pg, X.v.pages !! id = some pg → id * 4096 < 0xFFFFFFFFFFFF⌝ := by
  unfold wtxW
  iintro ⟨-, -, ⟨%l, Hmf, %Hl⟩⟩
  isimp only [mapFields] at Hmf
  icases Hmf with ⟨-, -, -, -, %Hlen⟩
  ipureintro
  intro id pg h
  exact pageIdx_lt_maxMap id l (Hl id pg h) Hlen.1

/-- A writer bucket's node cache is not nil. -/
theorem wtxW_nodes_nonnull (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (bl : Loc)
    (B : BRec) (hb : X.t.bs !! bl = some B) :
    wtxW (GF := GF) K tx r m X ⊢ wtxW K tx r m X ∗ ⌜B.bv.nodes' ≠ null⌝ := by
  iintro Hw
  icases wtxW_nm_acc K tx r m X bl B hb B.bv.nodes' B.nm rfl rfl $$ Hw with ⟨Hm, Hback⟩
  ihave %Hn := ownMap_not_nil _ _ _ $$ Hm
  ihave Hw := Hback $$ Hm
  iframe
  ipureintro; exact Hn

end wctx

end bbolt
end EtcdGrove
end Perennial
