/-
`node.spill` after its children's loop (U9l, `notes/bbolt-proof-plan.md`): **one piece's
iteration** (`pieceOne_wp`, the WP of `pieceFn`'s body for the piece `l`): its page freed
(`pieceFree_wp`), a page allocated (`Tx.allocate`), the node written there (`node.write`, the
buffer becoming `wPage`), marked spilled, and put in its parent (`node.put`) with its key its
first inode's; or `allocate`'s error returned.
-/
module

public import Proof.go_etcd_io.bbolt.Spill.NodeSpillPiecesFree
public import Spec.go_etcd_io.bbolt.Tx__allocate
public import Spec.go_etcd_io.bbolt.node__write
public import Spec.go_etcd_io.bbolt.node__put
public import Spec.go_etcd_io.bbolt.node__size
public import Spec.go_etcd_io.bbolt.TxStats__IncSpill
public import Spec.go_etcd_io.bbolt.internal.common.Meta__Pgid
public import Spec.go_etcd_io.bbolt.internal.common.Page__Id
public import Spec.go_etcd_io.bbolt.internal.common.Inode__Key
public import Spec.go_etcd_io.bbolt.internal.common.Assert
public import Proof.go_etcd_io.bbolt.Spill.PageBuf
public import Proof.go_etcd_io.bbolt.Spill.NodeSpillPiecesStep
public import Proof.go_etcd_io.bbolt.Spill.NodeSpillPiecesAlloc
public import Proof.go_etcd_io.bbolt.Spill.NodeSpillHeap

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

omit package_sem in
/-- `wtxW`'s persistent parts. -/
theorem wtxW_pers (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) :
    wtxW (GF := GF) K tx r m X ⊢ wtxW K tx r m X ∗
      □ (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ K.core ∗ reg tx K.B r) := by
  iintro Hw
  icases (wtxW_split K tx r m X).1 $$ Hw with ⟨Hc, Hcells, Hmap⟩
  unfold wtxCore
  icases Hc with ⟨#Hpkg', #Hcore, %Hr, #Hreg, Hh, Hfills, Hbk, Hnl, Hdbf, Hview, Hst⟩
  isplitl
  · iapply (wtxW_split K tx r m X).2
    unfold wtxCore
    iframe; iframe #
    ipureintro; exact Hr
  · imodintro; iframe #

omit package_sem in
/-- **A live node's struct and inodes, and the transaction's `db` field, out of `wtxW` and
back** (what `node.size()` and `tx.db.pageSize` read). -/
theorem wtxW_size_acc (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (bl n : Loc)
    (rn : NRec) (hn : X.node bl n = some rn) (hl : n ∈ X.live) :
    wtxW (GF := GF) K tx r m X ⊢ n ↦ rn.nv ∗ rn.nv.inodes' ↦* rn.ins ∗
      tx.[Tx, go!"db"] ↦{DFrac.own (txDbQ 1)} K.db ∗ K.db.[DB, go!"pageSize"] ↦□ W64 4096 ∗
      (n ↦ rn.nv -∗ rn.nv.inodes' ↦* rn.ins -∗ tx.[Tx, go!"db"] ↦{DFrac.own (txDbQ 1)} K.db -∗
        wtxW K tx r m X) := by
  obtain ⟨B, HB, Hrn⟩ := node_bs_of hn
  iintro Hw
  icases (wtxW_split K tx r m X).1 $$ Hw with ⟨Hc, Hcells, Hmap⟩
  unfold wtxCore
  icases Hc with ⟨#Hpkg', #Hcore, %Hr, #Hreg, Hh, Hfills, Hbk, Hnl, Hdbf, Hview, Hst⟩
  ihave %Hok := wtxHeap_heapOK tx (DFrac.own 1) X $$ Hh
  have Ho := objs_node X.t bl B n rn Hok.2.1 HB Hrn
  ihave #Hps := isBoltCoreP_pageSize K.B K.N K.db K.p K.sp K.t0 $$ [Hcore]
  · unfold BC.core; iexact Hcore
  icases wtxHeap_setNode tx (DFrac.own 1) X bl B n rn HB Hrn $$ Hh with ⟨Hno, Hback⟩
  rw [decide_eq_true hl]
  icases (objOwn_live_node _ _ _ _ _).1 $$ Hno with ⟨Hn, Hins, Hcap, Hws, Hch, Hchcap, Hkey⟩
  rw [Hr.1]
  iframe Hn Hins Hdbf Hps
  iintro Hn Hins Hdbf
  ihave Hno : objOwn X.v n (DFrac.own 1) true (.node bl rn) $$ [Hn Hins Hcap Hws Hch Hchcap Hkey]
  · iapply (objOwn_live_node _ _ _ _ _).2; iframe
  ihave Hh := Hback $$ %rn %(Hok.2.2.2.1 bl B n rn HB Hrn) [Hno]
  · iexact Hno
  rw [setNode_self X bl n B rn HB Hrn]
  iapply (wtxW_split K tx r m X).2
  unfold wtxCore
  rw [← Hr.1]
  iframe; iframe #
  ipureintro; exact ⟨rfl, Hr.2⟩

/-- **One piece's iteration** (see the module doc): the piece `l` (record `rl`, live, of bucket
`bl`; its parent, if any, a live node of `bl` owning its inodes' capacity, its entries sorted).
The premises on the states after the free and the allocation (`hG`, `hid`) are the caller's
(the spill's global state, the allocated page below the mark and none of a branch's children). -/
theorem pieceOne_wp (hAlloc : Tx.allocate.spec (GF := GF) (hG := hG))
    (hPage : Tx.page.spec (GF := GF) (hG := hG))
    (hWrite : node.write.spec (GF := GF) (hG := hG))
    (hPut : node.put.spec (GF := GF) (hG := hG))
    (hSize : node.size.spec (GF := GF) (hG := hG))
    (hInc : TxStats.IncSpill.spec (GF := GF) (hG := hG))
    (hTxid : internal.common.Meta.Txid.spec (GF := GF) (hG := hG))
    (hPgid : internal.common.Meta.Pgid.spec (GF := GF) (hG := hG))
    (hId : internal.common.Page.Id.spec (GF := GF) (hG := hG))
    (hKey : internal.common.Inode.Key.spec (GF := GF) (hG := hG))
    (hAssert : internal.common.Assert.spec (GF := GF) (hG := hG))
    (hFree : internal.freelist.Interface.Free.spec (GF := GF) (hG := hG))
    (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (w : WDb) (bl l : Loc) (rl : NRec)
    (txp resp nodep l0 : Loc) (e0 : GoInterface) (k : w64)
    (hn : X.node bl l = some rl) (hlv : l ∈ X.live) (hbl : rl.nv.bucket' = bl)
    (hfree : rl.nv.pgid' ≠ W64 0 → X.t.pm !! rl.nv.pgid' = none ∧ X.t.mv.txid' = w.wtxid ∧
      ∃ pg, X.v.pages !! rl.nv.pgid'.toNat = some pg ∧
        16 ≤ pg.length ∧ pageId pg = rl.nv.pgid'.toNat ∧
        (pageFlags pg = branchPageFlag ∨ pageFlags pg = leafPageFlag) ∧
        w.fl.canFree w.wtxid rl.nv.pgid' (1 + pageOverflow pg))
    (hG : ∀ X1 w1 st, pcFreed X w bl l rl X1 w1 st → spG X1 w.wtxid (mapLen w1.ms))
    (hne : 0 < rl.ws.length) (hil : rl.ins.length = rl.ws.length)
    (hsz : insSize rl.ins + 4096 < 2 ^ 62) (hfit : pageFits (wsMs rl.ws))
    (hid : ∀ X1 w1 st X2 fl2 p id, pcFreed X w bl l rl X1 w1 st →
      allocRes X1 X2 w1.fl fl2 w.wtxid (pcCount (insSize rl.ins)) p id →
      id.toNat < X2.t.mv.pgid'.toNat ∧ (rl.nv.isLeaf' = false → ∀ e ∈ rl.ws, e.pgid ≠ id))
    (hpar : rl.nv.parent' ≠ null → ∃ rp, X.node bl rl.nv.parent' = some rp ∧
      rl.nv.parent' ∈ X.live ∧ rl.nv.parent' ≠ l ∧ rp.capOwn = true ∧ wsSorted rp.ws)
    (Φ : val → IProp GF) :
    wtxW K tx r m X ∗ wdbW K tx X.v w ∗ txp ↦ tx ∗ nodep ↦ l0 ∗ resp ↦ e0 ∗
      (∀ (X3 : WX) (w2 : WDb) (st : List FLStep) (id : w64),
        ⌜pcStep X w bl l rl (pcCount (insSize rl.ins)) X3 w2 st id⌝ -∗
        wtxW K tx r m X3 -∗ wdbW K tx X3.v w2 -∗ txp ↦ tx -∗ nodep ↦ l -∗ resp ↦ e0 -∗
        Φ executeVal) ∗
      (∀ (err : GoInterface) (X' : WX) (w' : WDb) (st : List FLStep),
        ⌜err ≠ interface.nil ∧ w'.C = w.C ∧ w'.fl = w.fl.applySteps w.wtxid st ∧
          X'.v.pages = X.v.pages⌝ -∗ fmtErrorOk err -∗
        ((wtxW K tx r m X' ∗ wdbW K tx X'.v w') ∨ (wtxLost K tx r m X' ∗ wdbLost K tx X'.v w')) -∗
        txp ↦ tx -∗ nodep ↦ l -∗ resp ↦ err -∗ Φ (returnVal #())) ⊢
    WP (App (App (Val (pieceFn txp resp nodep)) (Val #k)) (Val #l)) {{ Φ }} := by
  iintro ⟨Hw, Hdb, Htxp, Hnodep, Hres, HΦ, HΦe⟩
  icases wtxW_pers K tx r m X $$ Hw with ⟨Hw, #⟨Hpkg, Hcore, Hreg⟩⟩
  unfold pieceFn
  wp_pures
  wp_store
  wp_pures
  -- the inline free
  wp_bind (If _ _ _)
  iapply (pieceFree_wp hTxid hPage hFree K tx r m X w bl l rl txp nodep hn hbl hfree)
  iframe
  iintro %X1 %w1 ⟨Hw, Hdb, Htxp, Hnodep, %Hfr⟩
  have Hfr' : ∃ st, pcFreed X w bl l rl X1 w1 st := by
    rcases Hfr with ⟨h1, h2, h3⟩ | ⟨pg, h1, h2, h3, h4⟩
    · exact ⟨[], Or.inl ⟨h1, h2, h3, rfl⟩⟩
    · exact ⟨_, Or.inr ⟨pg, h1, h2, h3, h4, rfl⟩⟩
  obtain ⟨st1, Hfr1⟩ := Hfr'
  -- the piece's record after the free
  obtain ⟨rl1, hn1, hrl1⟩ : ∃ rl1, X1.node bl l = some rl1 ∧
      rl1 = { rl with nv := { rl.nv with pgid' := W64 0 } } := by
    rcases Hfr1 with ⟨h0, rfl, -, -⟩ | ⟨pg, -, -, rfl, -, -⟩
    · refine ⟨rl, hn, ?_⟩
      rw [← h0]
    · exact ⟨_, WX.setNode_node_same hn _, rfl⟩
  have hlv1 : l ∈ X1.live := by
    rcases Hfr1 with ⟨-, rfl, -, -⟩ | ⟨pg, -, -, rfl, -, -⟩
    · exact hlv
    · rw [WX.setNode_live]; exact hlv
  have hv1 : X1.v = X.v := by
    rcases Hfr1 with ⟨-, rfl, -, -⟩ | ⟨pg, -, -, rfl, -, -⟩
    · rfl
    · exact WX.setNode_v _ _ _ _
  rw [← hv1]
  wp_pures
  -- `node.size()` and `tx.db.pageSize`
  icases wtxW_size_acc K tx r m X1 bl l rl1 hn1 hlv1 $$ Hw with ⟨Hn, Hins, Hdbf, #Hps, Hwb⟩
  wp_auto
  wp_apply (hSize l rl1.nv rl1.ins (DFrac.own 1) (DFrac.own 1)) $$ [Hn Hins] as ⟨Hn, Hins⟩
  · iframe
  ihave Hw := Hwb $$ Hn Hins Hdbf
  have hins1 : rl1.ins = rl.ins := by rw [hrl1]
  rw [hins1]
  have hcnt : BitVec.sdiv (W64 (insSize rl.ins : Int) + W64 4096 - W64 1) (W64 4096) =
      W64 (pcCount (insSize rl.ins) : Int) := by
    unfold pcCount
    have : insSize rl.ins + 4096 < 2 ^ 62 := hsz
    word
  rw [hcnt]
  obtain ⟨hG1, hG2, hG3, hG4, hG5, hG6, hG7⟩ := hG X1 w1 st1 Hfr1
  have hwtx : w1.wtxid = w.wtxid := by
    rcases Hfr1 with ⟨-, -, rfl, -⟩ | ⟨pg, -, -, -, rfl, -⟩ <;> rfl
  have hc0 : 0 < pcCount (insSize rl.ins) := by
    unfold pcCount insSize; omega
  wp_apply (hAlloc K tx r m X1 w1 (W64 (pcCount (insSize rl.ins) : Int))
    (by unfold pcCount at hc0 ⊢; word) (by unfold pcCount at hc0 ⊢; word)
    (by rw [hwtx]; exact hG1) hG2 hG3 hG4 hG5) $$ [Hw Hdb]
    as %p %err (⟨%Herr, %X2, %w2, %id, Hw, Hdb, %Hal⟩ | ⟨%Herr, #Herrok, Hres2⟩)
  · iframe
  rotate_left
  · -- `allocate`'s error: returned
    have hfw : w1.C = w.C ∧ w1.fl = w.fl.applySteps w.wtxid st1 := by
      rcases Hfr1 with ⟨-, -, rfl, rfl⟩ | ⟨pg, -, -, -, rfl, rfl⟩
      · exact ⟨rfl, rfl⟩
      · exact ⟨rfl, rfl⟩
    cases err with
    | nil => exact absurd rfl Herr
    | ok ii =>
    simp only
    wp_auto
    icases Hres2 with (⟨Hw, Hdb⟩ | ⟨%X', %w', Hw, Hdb, %Hl⟩)
    · iapply HΦe $$ %err %X1 %w1 %st1 [] Herrok [Hw Hdb] Htxp Hnodep Hres
      · ipureintro; exact ⟨Herr, hfw.1, hfw.2, by rw [hv1]⟩
      · ileft; iframe
    · obtain ⟨⟨Xd, b, hd, rfl⟩, hC, hfl⟩ := Hl
      iapply HΦe $$ %err %(Xd.rebase b) %w' %st1 [] Herrok [Hw Hdb] Htxp Hnodep Hres
      · ipureintro
        refine ⟨Herr, hC.trans hfw.1, hfl.trans hfw.2, ?_⟩
        show Xd.v.pages = X.v.pages
        rw [hd.2.1, hv1]
      · iright; iframe
  trace_state
  sorry

end proof

end Spill

end bbolt
end EtcdGrove
end Perennial
