/-
The writer's working state at a fraction (U6w, "Writer reads at a fraction" of
`notes/bbolt-proof-plan.md`): `wtxWQ`'s accessors, the read-only writer specs' resources at any
fraction `q` (the `wtxW_*` accessors of `Read/WCtx`, `Rebalance/BktRbl` and `Write/CurNodeH`, which
are their cases `q = 1`): a bucket's object, its node cache, a live node with the view's cells,
the view's cells, a page at a position with its source, the mapping's bound, the package's
initialization.
-/
module

public import Proof.go_etcd_io.bbolt.Read.WCtx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section wq
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **A bucket's object, out of `wtxWQ` at `q`** and back unchanged. -/
theorem wtxWQ_bkt_acc (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (q : Qp) (X : WX) (bl : Loc)
    (B : BRec) (hb : X.t.bs !! bl = some B) :
    wtxWQ (GF := GF) K tx r m q X ⊢
      objOwn X.v bl (DFrac.own q) (decide (bl ∈ X.liveB)) (.bkt B) ∗
      (objOwn X.v bl (DFrac.own q) (decide (bl ∈ X.liveB)) (.bkt B) -∗ wtxWQ K tx r m q X) := by
  unfold wtxWQ wtxCoreQ
  iintro ⟨⟨Hpkg, Hcore, %Hr, Hreg, Hh, Hfills, Hbk, Hnl, Hdb, Hview, Hst⟩, Hcells, Hmap⟩
  icases wtxHeap_bkt_obj_acc tx (DFrac.own q) X bl B (bobjs_bkt X.t bl B hb) $$ Hh
    with ⟨Ho, Hback⟩
  iframe Ho
  iintro Ho
  ihave Hh := Hback $$ Ho
  iframe; ipureintro; exact Hr

/-- A bucket's node cache, out of `wtxWQ` and back. -/
theorem wtxWQ_nm_acc (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (q : Qp) (X : WX) (bl : Loc)
    (B : BRec) (hb : X.t.bs !! bl = some B) (p : Loc) (nm : GMap w64 Loc) (hp : B.bv.nodes' = p)
    (hnm : B.nm = nm) :
    wtxWQ (GF := GF) K tx r m q X ⊢ p ↦${DFrac.own q} nm ∗
      (p ↦${DFrac.own q} nm -∗ wtxWQ K tx r m q X) := by
  subst hp hnm
  iintro Hw
  icases wtxWQ_bkt_acc K tx r m q X bl B hb $$ Hw with ⟨Ho, Hback⟩
  isimp only [objOwn] at Ho
  icases Ho with ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, H10⟩
  iframe H8
  iintro H8
  iapply Hback
  simp only [objOwn]
  iframe

/-- **The view's cells, out of `wtxWQ`** at `q · wq` (the view's base positive), and back. -/
theorem wtxWQ_cells_acc (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (q : Qp) (X : WX) :
    wtxWQ (GF := GF) K tx r m q X ⊢ ⌜0 < X.v.base.addr⌝ ∗ viewCells (QpMul q wq) X.v ∗
      (viewCells (QpMul q wq) X.v -∗ wtxWQ K tx r m q X) := by
  unfold wtxWQ
  iintro ⟨Hcore, Hcells, ⟨%l, Hmf, %Hl⟩⟩
  ihave %Hnn := mapFields_base_nonnull _ _ _ _ $$ Hmf
  iframe Hcells
  isplitr
  · ipureintro; exact Hnn
  iintro Hcells
  iframe
  ipureintro; exact Hl

/-- **A live node and the view's cells, out of `wtxWQ`**, and back. -/
theorem wtxWQ_node_cells_acc (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (q : Qp) (X : WX)
    (bl : Loc) (B : BRec) (n : Loc) (rn : NRec) (hb : X.t.bs !! bl = some B)
    (hn : B.ns !! n = some rn) (hl : n ∈ X.live) :
    wtxWQ (GF := GF) K tx r m q X ⊢ ⌜0 < X.v.base.addr⌝ ∗
      objOwn X.v n (DFrac.own q) true (.node bl rn) ∗ viewCells (QpMul q wq) X.v ∗
      (objOwn X.v n (DFrac.own q) true (.node bl rn) -∗ viewCells (QpMul q wq) X.v -∗
        wtxWQ K tx r m q X) := by
  unfold wtxWQ wtxCoreQ
  iintro ⟨⟨#Hpkg, #Hcore, %Hr, #Hreg, Hh, Hfills, Hbk, Hnl, Hdb, Hview, Hst⟩, Hc, ⟨%l, Hmf, %Hl⟩⟩
  ihave %Hnn := mapFields_base_nonnull _ _ _ _ $$ Hmf
  icases wtxHeap_live_node_acc tx (DFrac.own q) X bl B n rn hb hn hl $$ Hh with ⟨Ho, Hback⟩
  iframe Ho Hc
  isplitr
  · ipureintro; exact Hnn
  iintro Ho Hc
  ihave Hh := Hback $$ Ho
  iframe; iframe #
  isplitr
  · ipureintro; exact Hr
  ipureintro; exact Hl

/-- **A live node's entries are fewer than `2^63`** (its `inodes` slice's length). -/
theorem wtxWQ_node_len (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (q : Qp) (X : WX) (bl : Loc)
    (B : BRec) (n : Loc) (rn : NRec) (hb : X.t.bs !! bl = some B) (hn : B.ns !! n = some rn)
    (hl : n ∈ X.live) :
    wtxWQ (GF := GF) K tx r m q X ⊢ wtxWQ K tx r m q X ∗ ⌜rn.ws.length < 2 ^ 63⌝ := by
  unfold wtxWQ wtxCoreQ
  iintro ⟨⟨#Hpkg, #Hcore, %Hr, #Hreg, Hh, Hfills, Hbk, Hnl, Hdb, Hview, Hst⟩, Hcells, Hmap⟩
  icases wtxHeap_live_node_acc tx (DFrac.own q) X bl B n rn hb hn hl $$ Hh with ⟨Ho, Hback⟩
  unfold objOwn
  icases Ho with ⟨Hn, Hs, Hcap, Hws, Hch, Hchcap, Hkey⟩
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  ihave %Hwl := BigSepL2.bigSepL2_length $$ Hws
  ihave Hh := Hback $$ [Hn Hs Hcap Hws Hch Hchcap Hkey]
  · simp only [objOwn]; iframe
  isplitl
  · iframe; iframe #; ipureintro; exact Hr
  ipureintro
  rw [← Hwl, Hsl.1]
  have := Hsl.2
  word

/-- **The page at a position of a live bucket, with its source** (`srcLoc`, persistent). -/
theorem wtxWQ_page_srcLoc (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (q : Qp) (X : WX) (bl : Loc)
    (B : BRec) (pid : w64) (pa : Loc) (pg : List w8) (hb : X.t.bs !! bl = some B)
    (hl : bl ∈ X.liveB) (hw : wpageAt X.v B pid = some (pa, pg))
    (hsrc : B.ib.root' = W64 0 → B.pst = PageSt.view ∨ ∃ dq, B.isrc = Src.own dq)
    (hpa : B.ib.root' = W64 0 → B.bv.page' ≠ null) :
    wtxWQ (GF := GF) K tx r m q X ⊢ wtxWQ K tx r m q X ∗ srcLoc X.v pa (pgSrc B) pg := by
  by_cases hin : B.ib.root' = W64 0
  · unfold wpageAt at hw
    rw [if_pos hin] at hw
    split at hw
    · simp only [Option.some.injEq, Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      unfold pgSrc
      rw [if_pos hin]
      iintro Hw
      icases wtxWQ_bkt_acc K tx r m q X bl B hb $$ Hw with ⟨Ho, Hback⟩
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

/-- **Every view page is within `db.page`'s range** (`Tx.page`'s premise), from the mapping. -/
theorem wtxWQ_page_maxMap (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (q : Qp) (X : WX) :
    wtxWQ (GF := GF) K tx r m q X ⊢
      ⌜∀ id pg, X.v.pages !! id = some pg → id * 4096 < 0xFFFFFFFFFFFF⌝ := by
  unfold wtxWQ
  iintro ⟨-, -, ⟨%l, Hmf, %Hl⟩⟩
  isimp only [mapFields] at Hmf
  icases Hmf with ⟨-, -, -, -, %Hlen⟩
  ipureintro
  intro id pg h
  exact pageIdx_lt_maxMap id l (Hl id pg h) Hlen.1

/-- A writer bucket's node cache is not nil. -/
theorem wtxWQ_nodes_nonnull (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (q : Qp) (X : WX)
    (bl : Loc) (B : BRec) (hb : X.t.bs !! bl = some B) :
    wtxWQ (GF := GF) K tx r m q X ⊢ wtxWQ K tx r m q X ∗ ⌜B.bv.nodes' ≠ null⌝ := by
  iintro Hw
  icases wtxWQ_nm_acc K tx r m q X bl B hb B.bv.nodes' B.nm rfl rfl $$ Hw with ⟨Hm, Hback⟩
  ihave %Hn := ownMap_not_nil _ _ _ $$ Hm
  ihave Hw := Hback $$ Hm
  iframe
  ipureintro; exact Hn

/-- `wtxWQ` holds bbolt's package initialization. -/
theorem wtxWQ_pkgInit (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (q : Qp) (X : WX) :
    wtxWQ (GF := GF) K tx r m q X ⊢
      wtxWQ K tx r m q X ∗ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt := by
  unfold wtxWQ wtxCoreQ
  iintro ⟨⟨#Hpkg, Hrest⟩, Hc, Hm⟩
  iframe; iframe #

/-- **The handles' fragments, out of `wtxW`** (persistent; `hdlAuth`'s). -/
theorem wtxW_hdlFrags (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) :
    wtxW (GF := GF) K tx r m X ⊢ wtxW K tx r m X ∗ hdlFrags r X.handles := by
  unfold wtxW wtxCore hdlAuth
  iintro ⟨⟨Hpkg, Hcore, Hr, Hreg, Hh, Hfills, ⟨Hbk, #Hf⟩, Hrest⟩, Hcells, Hmap⟩
  iframe; iframe #

/-- The handles' fragments, out of `wtxWQ`. -/
theorem wtxWQ_hdlFrags (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (q : Qp) (X : WX) :
    wtxWQ (GF := GF) K tx r m q X ⊢ wtxWQ K tx r m q X ∗ hdlFrags r X.handles := by
  unfold wtxWQ wtxCoreQ hdlAuth
  iintro ⟨⟨Hpkg, Hcore, Hr, Hreg, Hh, Hfills, ⟨Hbk, #Hf⟩, Hrest⟩, Hcells, Hmap⟩
  iframe; iframe #

end wq

end bbolt
end EtcdGrove
end Perennial
