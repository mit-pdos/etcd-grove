/-
`node.spill` after its children's loop (U9l, `notes/bbolt-proof-plan.md`): **a piece's inline
free** (`pieceFree_wp`: `if node.pgid > 0 { tx.db.freelist.Free(tx.meta.Txid(),
tx.page(node.pgid)); node.pgid = 0 }`, the fork's inlined `node.free()`), as `node.free.spec`
(`node__free`'s proof, over the cells of `tx` and `node`).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.NodeSpillPiecesCode
public import Spec.go_etcd_io.bbolt.Tx__page
public import Spec.go_etcd_io.bbolt.internal.common.Meta__Txid
public import Spec.go_etcd_io.bbolt.internal.freelist.Interface__Free
public import Proof.go_etcd_io.bbolt.Rebalance.Heap
public import Proof.go_etcd_io.bbolt.Rebalance.Free
public import Proof.go_etcd_io.bbolt.internal.common.Lemmas.Layout
public import Proof.go_etcd_io.bbolt.Read.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **A piece's inline free** (see the module doc). -/
theorem pieceFree_wp (hTxid : internal.common.Meta.Txid.spec (GF := GF) (hG := hG))
    (hPage : Tx.page.spec (GF := GF) (hG := hG))
    (hFree : internal.freelist.Interface.Free.spec (GF := GF) (hG := hG))
    (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (w : WDb) (bl n : Loc) (rn : NRec)
    (txp nodep : Loc) (hn : X.node bl n = some rn) (hbl : rn.nv.bucket' = bl)
    (hpre : rn.nv.pgid' ≠ W64 0 → X.t.pm !! rn.nv.pgid' = none ∧ X.t.mv.txid' = w.wtxid ∧
      ∃ pg, X.v.pages !! rn.nv.pgid'.toNat = some pg ∧
        16 ≤ pg.length ∧ pageId pg = rn.nv.pgid'.toNat ∧
        (pageFlags pg = branchPageFlag ∨ pageFlags pg = leafPageFlag) ∧
        w.fl.canFree w.wtxid rn.nv.pgid' (1 + pageOverflow pg))
    (Φ : val → IProp GF) :
    wtxW K tx r m X ∗ wdbW K tx X.v w ∗ txp ↦ tx ∗ nodep ↦ n ∗
      (∀ (X' : WX) (w' : WDb), wtxW K tx r m X' ∗ wdbW K tx X.v w' ∗ txp ↦ tx ∗ nodep ↦ n ∗
        ⌜(rn.nv.pgid' = W64 0 ∧ X' = X ∧ w' = w) ∨
         (∃ pg, rn.nv.pgid' ≠ W64 0 ∧ X.v.pages !! rn.nv.pgid'.toNat = some pg ∧
           X' = X.setNode bl n { rn with nv := { rn.nv with pgid' := W64 0 } } ∧
           w' = w.withFl (w.fl.freePages w.wtxid rn.nv.pgid' (1 + pageOverflow pg)))⌝ -∗
        Φ executeVal) ⊢
    WP (pieceFree txp nodep) {{ Φ }} := by
  iintro ⟨Hw, Hdb, Htxp, Hnodep, HΦ⟩
  obtain ⟨B, hb, hr⟩ : ∃ B, X.t.bs !! bl = some B ∧ B.ns !! n = some rn := by
    unfold WX.node at hn
    cases h : X.t.bs !! bl with
    | none => rw [h] at hn; cases hn
    | some B => rw [h] at hn; exact ⟨B, rfl, hn⟩
  unfold pieceFree
  unfold wtxW wtxCore
  icases Hw with ⟨⟨#Hpkg', #Hcore, %Hr, #Hreg, Hh, Hfills, Hbk, Hnl, Hdbf, Hview, Hst⟩, Hcells, Hmap⟩
  ihave %Hok := wtxHeap_heapOK tx (DFrac.own 1) X $$ Hh
  have Ho := objs_node X.t bl B n rn Hok.2.1 hb hr
  icases wtxHeap_node_ptr_acc tx (DFrac.own 1) X bl n rn Ho $$ Hh with ⟨Hn, Hback⟩
  icases typedPointsto_not_null_dup _ _ _ $$ Hn with ⟨Hn, %Hnn⟩
  iStructNamed Hn
  wp_auto
  ihave Hn : (n ↦ rn.nv : IProp GF) $$ [bucket isLeaf unbalanced spilled key pgid parent children inodes]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  ihave Hh := Hback $$ Hn
  by_cases hp0 : rn.nv.pgid' = W64 0
  · rw [decide_eq_false (show ¬ uint.Z (W64 0) < uint.Z rn.nv.pgid' by rw [hp0]; exact Int.lt_irrefl _)]
    wp_auto
    iapply HΦ $$ %X %w
    iframe; iframe #
    ipureintro
    exact ⟨Hr, Or.inl ⟨hp0, rfl, rfl⟩⟩
  rw [decide_eq_true (show uint.Z (W64 0) < uint.Z rn.nv.pgid' by
    have : rn.nv.pgid' ≠ 0 := hp0
    word)]
  obtain ⟨hpm, htxid, pg, hpg, hlen, hid, hfl, hcan⟩ := hpre hp0
  icases wtxHeap_setNode_bkt tx (DFrac.own 1) X bl B n rn hb hr $$ Hh with ⟨Hno, Hbo, Hf, Hback⟩
  icases objOwn_node_pgid_upd X.v n (DFrac.own 1) _ bl rn $$ Hno with ⟨Hn, Hnback⟩
  have hbtx : B.bv.tx' = tx := (Hok.2.2.1 bl B hb).1
  unfold objOwn
  icases Hbo with ⟨Hb1, Hbtx, Hbo⟩
  unfold txFields
  icases Hf with ⟨Hf1, Hf2, Hmeta, Hpages, Hf5, Hf6, Hmv, Hpm, Hbufs⟩
  icases typedPointsto_not_null_dup _ _ _ $$ Hn with ⟨Hn, %Hnn'⟩
  iStructNamed Hn
  ihave Htxf : (∃ dqb : DFrac, bl.[Bucket, go!"tx"] ↦{dqb} tx ∗
      (bl.[Bucket, go!"tx"] ↦{dqb} tx -∗
        if bl = B.bv.tx'.[Tx, go!"root"] then bl.[Bucket, go!"tx"] ↦ B.bv.tx'
        else bl.[Bucket, go!"tx"] ↦□ B.bv.tx') : IProp GF) $$ [Hbtx]
  · rw [hbtx]
    by_cases hroot : bl = tx.[Tx, go!"root"]
    · rw [if_pos hroot]
      iexists DFrac.own 1
      iframe
      iintro H; iexact H
    · rw [if_neg hroot]
      icases Hbtx with #Hbtx
      iexists DFrac.discard
      isplitr
      · iexact Hbtx
      · iintro _; iexact Hbtx
  icases Htxf with ⟨%dqb, Htx, Htxb⟩
  rw [hbl]
  wp_auto
  wp_apply hTxid $$ [Hmv] as Hmv
  · iframe
  -- `tx.page(n.pgid)`: the page of the view
  icases Hmap with ⟨%l, Hmf, %Hl⟩
  ihave %Hbnn := mapFields_base_nonnull _ _ _ _ $$ Hmf
  simp only [mapFields]
  icases Hmf with ⟨Hdref, Hdata, Hm0, Hm1, %Hlen⟩
  have hbound := Hl rn.nv.pgid'.toNat pg hpg
  ihave #Hps := isBoltCoreP_pageSize K.B K.N K.db K.p K.sp K.t0 $$ [Hcore]
  · unfold BC.core; iexact Hcore
  icases viewCells_page_acc _ X.v rn.nv.pgid'.toNat pg hpg $$ Hcells with ⟨Hpg, Hcells⟩
  have Hsp := typedPointsto_frac_add (GF := GF) (tx.[Tx, go!"pages"]) X.t.t.pages'
    (QpMul 1 (1 : Qp).half) (QpMul 1 (1 : Qp).half)
  rw [qpMul_half_add] at Hsp
  icases Hsp.1 $$ Hpages with ⟨Hp1, Hp2⟩
  have Hsd := typedPointsto_frac_add (GF := GF) (tx.[Tx, go!"db"]) r.db
    (QpMul 1 (1 : Qp).half) (QpMul 1 (1 : Qp).half.half)
  rw [← txDbQ_eq] at Hsd
  rw [Hr.1] at Hsd ⊢
  icases Hsd.1 $$ Hdbf with ⟨Hd1, Hd2⟩
  ihave Hpmi : (if X.t.t.pages' = null then iprop(⌜(if X.t.t.pages' = null then ∅ else X.t.pm) = (∅ : GMap w64 Loc)⌝)
      else iprop(X.t.t.pages' ↦$ (if X.t.t.pages' = null then ∅ else X.t.pm)) : IProp GF) ∗
      ((if X.t.t.pages' = null then iprop(⌜(if X.t.t.pages' = null then ∅ else X.t.pm) = (∅ : GMap w64 Loc)⌝)
      else iprop(X.t.t.pages' ↦$ (if X.t.t.pages' = null then ∅ else X.t.pm))) -∗ X.t.t.pages' ↦$ X.t.pm)
    $$ [Hpm]
  · by_cases hpn : X.t.t.pages' = null
    · simp only [hpn, ↓reduceIte]
      isplitr
      · ipureintro; simp
      · iintro _; rw [← hpn]; iexact Hpm
    · simp only [hpn, ↓reduceIte]
      iframe
      iintro H; iexact H
  icases Hpmi with ⟨Hpmi, Hpmb⟩
  have hpm' : (if X.t.t.pages' = null then (∅ : GMap w64 Loc) else X.t.pm) !! rn.nv.pgid' = none := by
    split
    · rfl
    · exact hpm
  wp_apply (hPage tx K.db X.t.t.pages' _ X.v.base rn.nv.pgid' (pageLoc X.v rn.nv.pgid'.toNat) pg
    (DFrac.own (QpMul 1 (1 : Qp).half)) (DFrac.own 1) (DFrac.own (1 : Qp).half.half) (DFrac.own wq)
    (Or.inr ⟨hpm', Hbnn, by omega, rfl⟩) hlen hid (by rcases hfl with h | h <;> simp [h]))
    $$ [Hp1 Hd1 Hdata Hpg Hpmi] as ⟨Hp1, Hpmi, Hd1, Hdata, Hpg⟩
  · iframe; iframe #
  -- `Free(txid, p)`
  unfold wdbW wdbLive wdbCoreG
  icases Hdb with ⟨⟨⟨Hcur, Hgfl, Hgmap, Hgout, Hgwv, Hfli, Hrest⟩, Hflo, Hrd, Hrcpt⟩, %Hwok⟩
  wp_auto
  have hpgne : pg ≠ [] := by intro h; rw [h] at hlen; simp at hlen
  ihave %Hpos := bytesPointsto_pos _ _ _ hpgne $$ Hpg
  icases bytesPointsto_view_read (V := Page) (pageLoc X.v rn.nv.pgid'.toNat) (DFrac.own wq) pg 0
    (pageLoc X.v rn.nv.pgid'.toNat) (by simp [loc_add_0]) (by omega) Hpos $$ Hpg with ⟨Hhdr, Hclose⟩
  rw [show (decode ((pg.drop 0).take 16) : Page) = pageHdr pg from rfl]
  have hhid : (pageHdr pg).id' = rn.nv.pgid' := by
    apply BitVec.eq_of_toNat_eq; exact hid
  have hcan' : w.fl.canFree X.t.mv.txid' (pageHdr pg).id' (1 + (pageHdr pg).overflow'.toNat) := by
    rw [htxid, hhid]; exact hcan
  -- the store's step
  ihave #Hpinv : (inv (pagesN K.N) (pagesInv (GF := GF) K.B K.p) : IProp GF) $$ []
  · unfold BC.core isBoltCoreP
    icases Hcore with ⟨-, -, -, -, -, -, -, -, -, #Hpi, -⟩
    iexact Hpi
  have hCpg : w.C.pages = X.v.pages := by rw [Hwok.2.2]; rfl
  imod (store_free K.B K.N K.p ⊤ CoPset.subseteq_top w.C w.fl w.ms (wLive X.v w.C)
    (w.C.txid + 1) rn.nv.pgid' (1 + pageOverflow pg) (fun _ => []) rfl rfl (by exact hcan))
    $$ [Hpinv Hcur Hgfl Hgmap Hgwv] with ⟨Hcur, Hgfl, Hgmap, Hgwv⟩
  · iframe; iframe #
    ileft
    ipureintro
    exact ⟨pg, by rw [hCpg]; exact hpg, rfl⟩
  wp_apply hFree w.fli w.fl X.t.mv.txid' _ (pageHdr pg) (DFrac.own wq) hcan' $$ [Hflo Hhdr]
    as ⟨Hflo, Hhdr⟩
  · iframe
  -- restore the reads
  ihave Hpg := Hclose $$ Hhdr
  ihave Hcells := Hcells $$ Hpg
  ihave Hpages := Hsp.2 $$ [Hp1 Hp2]
  · iframe
  ihave Hdbf := Hsd.2 $$ [Hd1 Hd2]
  · iframe
  ihave Hpm := Hpmb $$ Hpmi
  ihave Hbtx := Htxb $$ Htx
  ihave Hn : (n ↦ ({ rn.nv with pgid' := W64 0 } : node) : IProp GF)
    $$ [bucket isLeaf unbalanced spilled key pgid parent children inodes]
  · iapply typedPointsto_combine _ _ _ Hnn'
    simp only [TypedPointsto.typedPointstoDef]
    rw [hbl]
    iframe
  ispecialize Hnback $$ %(W64 0)
  ihave Hno := Hnback $$ [Hn]
  · simp only; rw [hbl]; iexact Hn
  ihave Hh := Hback $$ %({ rn with nv := { rn.nv with pgid' := W64 0 } }) [] [Hno] [Hb1 Hbtx Hbo] [Hf1 Hf2 Hmeta Hpages Hf5 Hf6 Hmv Hpm Hbufs]
  · ipureintro; exact Hok.2.2.2.1 bl B n rn hb hr
  · simp only; rw [hbl]; iexact Hno
  · iframe
  · iframe
  iapply HΦ $$ %(X.setNode bl n { rn with nv := { rn.nv with pgid' := W64 0 } })
    %(w.withFl (w.fl.freePages w.wtxid rn.nv.pgid' (1 + pageOverflow pg)))
  have hv : (X.setNode bl n { rn with nv := { rn.nv with pgid' := W64 0 } }).v = X.v := by
    rw [setNode_eq X bl n B _ hb]
  have hh : (X.setNode bl n { rn with nv := { rn.nv with pgid' := W64 0 } }).handles = X.handles := by
    rw [setNode_eq X bl n B _ hb]
  have hnl : (X.setNode bl n { rn with nv := { rn.nv with pgid' := W64 0 } }).nloc = X.nloc := by
    rw [setNode_eq X bl n B _ hb]
  rw [hv, hh, hnl]
  try unfold wdbW wdbLive wdbCoreG
  simp only [WDb.withFl]
  rw [htxid]
  iframe; iframe #
  isplitr
  · ipureintro; exact ⟨⟨trivial, Hr.2.1, Hr.2.2.1, by unfold WX.setNode; split <;> exact Hr.2.2.2.1, Hr.2.2.2.2.1,
    by unfold WX.setNode; split <;> exact Hr.2.2.2.2.2⟩, Hlen, Hl⟩
  isplitl [Hflo]
  · isplitl [Hflo]
    · rw [← hhid]; simp only [pageHdr, pageOverflow]; iexact Hflo
    · ipureintro
      exact ⟨wdbOK_free w rn.nv.pgid' pg Hwok.1 (by rw [hCpg]; exact hpg) hcan, Hwok.2.1, Hwok.2.2⟩
  ipureintro
  exact Or.inr ⟨pg, hp0, hpg, by rw [hbl], rfl⟩

end proof

end Spill

end bbolt
end EtcdGrove
end Perennial
