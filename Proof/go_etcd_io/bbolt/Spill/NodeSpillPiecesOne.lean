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
public import Proof.go_etcd_io.bbolt.Spill.NodeSpillPiecesHeap
public import Proof.go_etcd_io.bbolt.Spill.NodeSpillPiecesWOwn
public import Proof.go_etcd_io.bbolt.Read.Bytes
public import Proof.go_etcd_io.bbolt.Inv.WtxBase
public import Proof.go_etcd_io.bbolt.Spill.AllocDeref
public import Proof.go_etcd_io.bbolt.Spill.NodeSpillAsm
public import Proof.go_etcd_io.bbolt.Spill.DerefCopy
public import Proof.go_etcd_io.bbolt.Spill.SpErr

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
/-- `wtxW`'s heap facts. -/
theorem wtxW_heapOK (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) :
    wtxW (GF := GF) K tx r m X ⊢ wtxW K tx r m X ∗ ⌜heapOK (GF := GF) tx X⌝ := by
  iintro Hw
  icases (wtxW_split K tx r m X).1 $$ Hw with ⟨Hc, Hcells, Hmap⟩
  unfold wtxCore
  icases Hc with ⟨#Hpkg', #Hcore, %Hr, #Hreg, Hh, Hfills, Hbk, Hnl, Hdbf, Hview, Hst⟩
  ihave %Hok := wtxHeap_heapOK tx (DFrac.own 1) X $$ Hh
  isplitl
  · iapply (wtxW_split K tx r m X).2
    unfold wtxCore
    iframe; iframe #
    ipureintro; exact Hr
  · ipureintro; exact Hok

omit [GooseSemantics] [GooseInterp] go_gctx hos in
theorem wsMs_congr {ws ws' : List WEntry} (h : ws'.map wDat = ws.map wDat) : wsMs ws' = wsMs ws := by
  unfold wsMs
  induction ws generalizing ws' with
  | nil => cases ws' with
    | nil => rfl
    | cons _ _ => simp at h
  | cons a ws ih => cases ws' with
    | nil => simp at h
    | cons b ws' =>
      simp only [List.map_cons, List.cons.injEq] at h ⊢
      refine ⟨?_, ih h.2⟩
      have h1 := h.1
      simp only [wDat, Prod.mk.injEq] at h1
      rw [h1.1, h1.2.1, h1.2.2.1, h1.2.2.2]

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

/-- The parent's put on the state after the write is the piece's step's state. -/
theorem setBkt_pcFin {X2 : WX} {bl l pl : Loc} {B2 : BRec} (hB2 : X2.t.bs !! bl = some B2)
    (A0 A P : NRec) (id : w64) (pg : List w8) :
    ((X2.setNode bl l A0).setBuf id pg).setBkt bl { B2 with ns := (B2.ns.insert l A).insert pl P } =
      ((X2.setNode bl l A).setNode bl pl P).setBuf id pg := by
  unfold WX.setNode
  rw [hB2]
  simp only [WX.setBkt, WX.setBuf, GMap.lookup_insert, GMap.insert_insert]

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
    (txp resp nodep l0 : Loc) (e0 : GoInterface) (k : w64) (P : IProp GF)
    (hn : X.node bl l = some rl) (hlv : l ∈ X.live) (hbl : rl.nv.bucket' = bl)
    (hfree : rl.nv.pgid' ≠ W64 0 → X.t.pm !! rl.nv.pgid' = none ∧ X.t.mv.txid' = w.wtxid ∧
      ∃ pg, X.v.pages !! rl.nv.pgid'.toNat = some pg ∧
        16 ≤ pg.length ∧ pageId pg = rl.nv.pgid'.toNat ∧
        (pageFlags pg = branchPageFlag ∨ pageFlags pg = leafPageFlag) ∧
        w.fl.canFree w.wtxid rl.nv.pgid' (1 + pageOverflow pg))
    (hG : ∀ X1 w1 st, pcFreed X w bl l rl X1 w1 st → spG X1 w.wtxid (mapLen w1.ms) w1.fl)
    (hne : rl.nv.parent' ≠ null → 0 < rl.ws.length) (hil : rl.ins.length = rl.ws.length)
    (hsz : insSize rl.ins + 4096 < 2 ^ 62) (hfit : pageFits (wsMs rl.ws))
    (hn16 : rl.ws.length < 0xFFFF)
    (hbody : 16 + (pageBody true (wsMs rl.ws)).length ≤ pcCount (insSize rl.ins) * 4096)
    (hid : ∀ X1 w1 st X2 fl2 p id, pcFreed X w bl l rl X1 w1 st →
      allocRes X1 X2 w1.fl fl2 w.wtxid (pcCount (insSize rl.ins)) p id →
      id.toNat < X2.t.mv.pgid'.toNat ∧ (rl.nv.isLeaf' = false → ∀ e ∈ rl.ws, e.pgid ≠ id))
    (hpar : rl.nv.parent' ≠ null → ∃ rp, X.node bl rl.nv.parent' = some rp ∧
      rl.nv.parent' ∈ X.live ∧ rl.nv.parent' ≠ l ∧ rp.capOwn = true ∧ wsSorted rp.ws)
    (Φ : val → IProp GF) :
    wtxW K tx r m X ∗ wdbW K tx X.v w ∗ poolR K.B.bq K.N P ∗ txp ↦ tx ∗ nodep ↦ l0 ∗ resp ↦ e0 ∗
      (∀ (X3 : WX) (w2 : WDb) (st : List FLStep) (id : w64),
        ⌜pcStep X w bl l rl (pcCount (insSize rl.ins)) X3 w2 st id⌝ -∗ poolR K.B.bq K.N P -∗
        wtxW K tx r m X3 -∗ wdbW K tx X3.v w2 -∗ txp ↦ tx -∗ nodep ↦ l -∗ resp ↦ e0 -∗
        Φ executeVal) ∗
      (∀ (err : GoInterface) (X' : WX) (w' : WDb) (st : List FLStep),
        ⌜err ≠ interface.nil ∧ spErr X X' w w' st⌝ -∗ poolR K.B.bq K.N P -∗ fmtErrorOk err -∗
        ((wtxW K tx r m X' ∗ wdbW K tx X'.v w') ∨ (wtxLost K tx r m X' ∗ wdbLost K tx X'.v w')) -∗
        txp ↦ tx -∗ nodep ↦ l -∗ resp ↦ err -∗ Φ (returnVal #())) ⊢
    WP (App (App (Val (pieceFn txp resp nodep)) (Val #k)) (Val #l)) {{ Φ }} := by
  iintro ⟨Hw, Hdb, HR, Htxp, Hnodep, Hres, HΦ, HΦe⟩
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
  icases wtxW_heapOK K tx r m X1 $$ Hw with ⟨Hw, %Hok1⟩
  obtain ⟨hG1, hG2, hG3, hG4, hG5, hG6, hG7⟩ := hG X1 w1 st1 Hfr1
  have hwtx : w1.wtxid = w.wtxid := by
    rcases Hfr1 with ⟨-, -, rfl, -⟩ | ⟨pg, -, -, -, rfl, -⟩ <;> rfl
  have hc0 : 0 < pcCount (insSize rl.ins) := by
    unfold pcCount insSize; omega
  wp_apply (hAlloc K tx r m X1 w1 (W64 (pcCount (insSize rl.ins) : Int)) P
    (by unfold pcCount at hc0 ⊢; word) (by unfold pcCount at hc0 ⊢; word)
    (by rw [hwtx]; exact hG1) hG2 hG3 hG4 hG5) $$ [Hw Hdb HR]
    as %p %err ⟨HR, (⟨%Herr, %X2, %w2, %id, Hw, Hdb, %Hal⟩ | ⟨%Herr, #Herrok, Hres2⟩)⟩
  · iframe
  rotate_left
  · -- `allocate`'s error: returned
    have hfw : spErr X X1 w w1 st1 := by
      rcases Hfr1 with ⟨h0, rfl, rfl, rfl⟩ | ⟨pg, -, -, rfl, rfl, rfl⟩
      · exact spErr_refl _ _
      · obtain ⟨-, -, c, d, e, f, g⟩ := spErr_setNode X w bl l { rl with nv := { rl.nv with pgid' := W64 0 } }
        exact ⟨rfl, rfl, c, d, e, f, g⟩
    cases err with
    | nil => exact absurd rfl Herr
    | ok ii =>
    simp only
    wp_auto
    icases Hres2 with (⟨Hw, Hdb⟩ | ⟨%X', %w', Hw, Hdb, %Hl⟩)
    · iapply HΦe $$ %(GoInterface.ok ii) %X1 %w1 %st1 [] HR Herrok [Hw Hdb] Htxp Hnodep Hres
      · ipureintro; exact ⟨Herr, spErr_st (spErr_trans hfw (spErr_refl X1 w1)) (List.append_nil _)⟩
      · ileft; iframe
    · obtain ⟨⟨Xd, b, hd, rfl⟩, hC, hfl⟩ := Hl
      iapply HΦe $$ %(GoInterface.ok ii) %(Xd.rebase b) %w' %st1 [] HR Herrok [Hw Hdb] Htxp Hnodep Hres
      · ipureintro
        exact ⟨Herr, spErr_st (spErr_trans hfw (spErr_rebase hd b hC hfl)) (List.append_nil _)⟩
      · iright; iframe
  -- `allocate`'s success
  obtain ⟨Hal, HC2, Hml2, Hw2⟩ := Hal
  subst Herr
  have Hal' : allocRes X1 X2 w1.fl w2.fl w.wtxid (pcCount (insSize rl.ins)) p id := by
    have hsn : sint.nat (W64 (pcCount (insSize rl.ins) : Int)) = pcCount (insSize rl.ins) := by
      unfold pcCount at hc0 ⊢; word
    rw [← hwtx, ← hsn]; exact Hal
  obtain ⟨sta, hsta, hsta'⟩ : ∃ sta, w2.fl = w1.fl.applySteps w.wtxid sta ∧
      (sta = [FLStep.alloc id (pcCount (insSize rl.ins))] ∨ sta = [] ∧ id = X1.t.mv.pgid') := by
    obtain ⟨-, -, Xr, -, hX'⟩ := Hal'
    rcases hX' with ⟨-, hf, -⟩ | ⟨hid, hf, -, -⟩
    · exact ⟨[FLStep.alloc id (pcCount (insSize rl.ins))], by rw [hf]; rfl, Or.inl rfl⟩
    · exact ⟨[], by rw [hf]; rfl, Or.inr ⟨rfl, hid⟩⟩
  obtain ⟨hpm2, hbs2⟩ := allocRes_buf Hal'
  obtain ⟨⟨ra, hna, hsa⟩, hliv⟩ := allocRes_node Hal' hn1
  have hlv2 : l ∈ X2.live := hliv.2 hlv1
  obtain ⟨hidlt, hidch⟩ := hid X1 w1 st1 X2 w2.fl p id Hfr1 Hal'
  wp_auto
  ihave %Hbase := wtxW_base_pos K tx r m X2 $$ Hw
  have hlf2 : liveFresh X2 :=
    (allocRes_derefPre' X1 X2 _ _ _ _ _ _ Hal' Hok1.2.1 hG3 hG4 hG5).2.1
  obtain ⟨B2, hB2, hra⟩ := node_bs_of hna
  have hwl : wsLive ra.ws := (hlf2 bl B2 l ra hB2 hra hlv2).1
  have hms : wsMs ra.ws = wsMs rl.ws := wsMs_congr (by
    have := hsa.2.2.1
    rw [hrl1] at this; exact this)
  have hlenws : ra.ws.length = rl.ws.length := by
    have := congrArg List.length hms; simp only [wsMs_length] at this; exact this
  icases wtxW_open K tx r m X2 $$ Hw with ⟨#-, #-, #-, Hh, Hv, Hst, Hclose⟩
  ihave %Hok2 := wtxHeap_heapOK tx (DFrac.own 1) X2 $$ Hh
  icases wtxHeap_node_buf_acc tx X2 bl l ra id p _ hna hlv2 hpm2 hbs2 $$ Hh
    with ⟨Hno, Hp, Hmeta, Hmv, Hback⟩
  icases Read.bytesPointsto_bounds _ _ _ (by
      rw [ne_eq, List.append_eq_nil_iff]; intro h
      have := congrArg List.length h.1; rw [ByteEncoding.encode_length] at this; simp at this)
    $$ Hp with ⟨Hp, %Hpb⟩
  icases (pageBuf_split p (DFrac.own 1) _ _ Hpb.1).1 $$ Hp with ⟨Hhdr, Hrest⟩
  wp_apply (hId p _ (DFrac.own 1)) $$ [Hhdr] as Hhdr
  · iframe
  wp_apply (hPgid X2.t.t.meta' X2.t.mv (DFrac.own 1)) $$ [Hmv] as Hmv
  · iframe
  rw [decide_eq_false (show ¬ (uint.Z X2.t.mv.pgid' ≤ uint.Z id) by have := hidlt; word)]
  wp_auto
  wp_apply (hId p _ (DFrac.own 1)) $$ [Hhdr] as Hhdr
  · iframe
  icases (objOwn_live_node _ _ _ _ _).1 $$ Hno with ⟨Hn, Hins, Hcap, Hws, Hch, Hchcap, Hkey⟩
  icases typedPointsto_not_null_dup _ _ _ $$ Hn with ⟨Hn, %Hnn⟩
  iStructNamed Hn
  wp_auto
  icases Hws with #Hws
  icases wOwns_write_acc X2.v Hbase ra.ins ra.ws wq hwl $$ [Hv] with ⟨%qk, %qv, Hbytes, Hbb⟩
  · iframe; iframe #
  ihave Hn : (l ↦ ({ ra.nv with pgid' := id } : node) : IProp GF)
    $$ [bucket isLeaf unbalanced spilled key pgid parent children inodes]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  wp_apply (hWrite l { ra.nv with pgid' := id } ra.ins (wsMs ra.ws) (DFrac.own 1) (DFrac.own 1) qk qv p
    (⟨id, W16 0, W16 0, W32 ((pcCount (insSize rl.ins) - 1 : Nat) : Int)⟩ : Page)
    (pcCount (insSize rl.ins) * 4096 - 16) rfl rfl (by rw [wsMs_length, hlenws]; exact hn16)
    (by rw [hms]; exact hfit) (by rw [hms]; omega)
    (fun hlf m hm => by
      rw [hms] at hm
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 hm
      show e.pgid ≠ id
      exact hidch (by
        have := nodeSim_isLeaf hsa; rw [hrl1] at this; simp only at hlf this
        rw [← this]; exact hlf) e he)
    Hpb.1 (by have := Hpb.2; simp [ByteEncoding.encode_length] at this; omega))
    $$ [Hn Hins Hbytes Hhdr Hrest] as ⟨Hn, Hins, Hbytes, Hhdr, Hrest⟩
  · iframe
    iunfold insBytes at Hbytes
    iexact Hbytes
  -- the written page and node, back
  ihave Hv := Hbb $$ [Hbytes]
  · iunfold insBytes; iexact Hbytes
  ihave Hp : bytesPointsto p (DFrac.own 1)
      (pcPage id ra.nv.isLeaf' ra.ws (pcCount (insSize rl.ins))) $$ [Hhdr Hrest]
  · unfold pcPage
    rw [← allocBuf_written]
    iapply (pageBuf_split p (DFrac.own 1) _ _ Hpb.1).2
    iframe
  ihave Hno : objOwn X2.v l (DFrac.own 1) true (.node bl (pcRec ra id false))
    $$ [Hn Hins Hcap Hch Hchcap Hkey]
  · iapply (objOwn_live_node _ _ _ _ _).2
    simp only [pcRec, Bool.false_eq_true, ↓reduceIte]
    iframe; iframe #
  have hpar2 : (pcRec ra id false).nv.parent' ≠ l := by
    simp only [pcRec, Bool.false_eq_true, ↓reduceIte]
    exact Hok2.2.2.2.1 bl B2 l ra hB2 hra
  ihave Hh := Hback $$ %(pcRec ra id false) %(pcPage id ra.nv.isLeaf' ra.ws (pcCount (insSize rl.ins)))
    %hpar2 Hno Hp Hmeta Hmv
  ihave Hw := Hclose $$ %((X2.setNode bl l (pcRec ra id false)).setBuf id
    (pcPage id ra.nv.isLeaf' ra.ws (pcCount (insSize rl.ins)))) [] Hh Hv Hst
  · ipureintro
    rw [setNode_eq X2 bl l B2 _ hB2]
    exact ⟨rfl, rfl, rfl⟩
  have hparl : ra.nv.parent' = rl.nv.parent' := by
    have := nodeSim_parent hsa; rw [hrl1] at this; exact this
  by_cases hp : ra.nv.parent' = null
  · -- no parent: the stats, done
    rw [decide_eq_true hp]
    wp_auto
    icases wtxW_open K tx r m _ $$ Hw with ⟨#-, #-, #-, Hh, Hv, Hst, Hclose⟩
    wp_apply (hInc K tx r m 1 (W64 1)) $$ [Hst] as %_ Hst
    · iframe; iframe #
    ihave Hw := Hclose $$ %_ [] Hh Hv Hst
    · ipureintro; exact ⟨rfl, rfl, rfl⟩
    have hpl : rl.nv.parent' = null := hparl ▸ hp
    have hv3 : ((X2.setNode bl l (pcRec ra id false)).setBuf id
        (pcPage id ra.nv.isLeaf' ra.ws (pcCount (insSize rl.ins)))).v = X2.v :=
      WX.setNode_v _ _ _ _
    iapply HΦ $$ %((X2.setNode bl l (pcRec ra id false)).setBuf id
        (pcPage id ra.nv.isLeaf' ra.ws (pcCount (insSize rl.ins)))) %w2 %(st1 ++ sta) %id
      [] HR [Hw] [Hdb] Htxp Hnodep Hres
    · ipureintro
      refine ⟨X1, w1, X2, p, ra, ra, slice.nil, [], st1, sta, Hfr1, rfl, Hal', hsta, hsta', HC2, Hml2,
        Hw2, hna,
        fun h => absurd hpl h, ?_⟩
      simp only [pcFin, hpl, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
        ↓reduceIte]
    · iexact Hw
    · rw [hv3]; iexact Hdb
  · -- a parent: the put (`pcPar`), the piece's key its first inode's (`pcRec … true`), the stats
    rw [decide_eq_false hp]
    -- the parent's records
    have hpn : rl.nv.parent' ≠ null := hparl ▸ hp
    have hne := hne hpn
    obtain ⟨rp, hrp, hplv, hpll, hcapp, hsrt⟩ := hpar hpn
    have hrp1 : X1.node bl rl.nv.parent' = some rp := by
      rcases Hfr1 with ⟨-, rfl, -, -⟩ | ⟨pg, -, -, rfl, -, -⟩
      · exact hrp
      · rw [WX.setNode_node_ne _ _ hpll]; exact hrp
    have hplv1 : rl.nv.parent' ∈ X1.live := by
      rcases Hfr1 with ⟨-, rfl, -, -⟩ | ⟨pg, -, -, rfl, -, -⟩
      · exact hplv
      · rw [WX.setNode_live]; exact hplv
    obtain ⟨⟨rpa, hrpa, hspa⟩, hlivp⟩ := allocRes_node Hal' hrp1
    have hplv2 : rl.nv.parent' ∈ X2.live := hlivp.2 hplv1
    obtain ⟨B2', hB2', hrpa'⟩ := node_bs_of hrpa
    rw [hB2] at hB2'; cases hB2'
    have hdp2 : derefPre X2 :=
      (allocRes_derefPre' X1 X2 _ _ _ _ _ _ Hal' Hok1.2.1 hG3 hG4 hG5).1
    have hcapa : rpa.capOwn = true := by rw [hspa.2.2.2.2.2.2]; exact hcapp
    have hsrta : wsSorted rpa.ws := wsSorted_of_dat hspa.2.2.1 hsrt
    have hwlp : wsLive rpa.ws := (hlf2 bl B2 _ rpa hB2 hrpa' hplv2).1
    have hbkp : rpa.nv.bucket' = bl := (hdp2.1 bl B2 _ rpa hB2 hrpa' hplv2).1
    obtain ⟨-, hkl, hkey0, -⟩ := hdp2.1 bl B2 l ra hB2 hra hlv2
    have hksrc := (hlf2 bl B2 l ra hB2 hra hlv2).2
    have hpparp : rpa.nv.parent' ≠ rl.nv.parent' := Hok2.2.2.2.1 bl B2 _ rpa hB2 hrpa'
    -- the bucket's record after the write
    have hbw : ((X2.setNode bl l (pcRec ra id false)).setBuf id (pcPage id ra.nv.isLeaf' ra.ws (pcCount (insSize rl.ins)))).t.bs !! bl = some ({ B2 with ns := B2.ns.insert l (pcRec ra id false) } : BRec) := by
      show (X2.setNode bl l (pcRec ra id false)).t.bs !! bl = some ({ B2 with ns := B2.ns.insert l (pcRec ra id false) } : BRec)
      rw [setNode_eq X2 bl l B2 _ hB2]
      exact GMap.lookup_insert _ _ _
    have hnd : [l, rl.nv.parent'].Nodup := by
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, _root_.or_false, List.nodup_nil,
        and_true]
      exact ⟨fun h => hpll (Eq.symm h), fun h => h⟩
    have hlivw : ∀ x, x ∈ ((X2.setNode bl l (pcRec ra id false)).setBuf id (pcPage id ra.nv.isLeaf' ra.ws (pcCount (insSize rl.ins)))).live ↔ x ∈ X2.live := by
      intro x; show x ∈ (X2.setNode bl l (pcRec ra id false)).live ↔ _; rw [WX.setNode_live]
    icases wtxW_open K tx r m _ $$ Hw with ⟨#-, #-, #-, Hh, Hv, Hst, Hclose⟩
    icases wtxHeap_setBkt_acc tx (DFrac.own 1) _ bl ({ B2 with ns := B2.ns.insert l (pcRec ra id false) } : BRec) [l, rl.nv.parent']
      (fun x => if x = l then (pcRec ra id false) else rpa) hbw hnd (by
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at hx
        rcases hx with rfl | rfl
        · simp only [↓reduceIte]; exact GMap.lookup_insert _ _ _
        · simp only [if_neg hpll]
          rw [GMap.lookup_insert_ne _ _ (Ne.symm hpll)]; exact hrpa') $$ Hh
      with ⟨HL, Hbo, Htf, Hrf, Hback⟩
    icases BigSepL.bigSepL_cons.1 $$ HL with ⟨Hlo, HL⟩
    icases BigSepL.bigSepL_cons.1 $$ HL with ⟨Hpo, -⟩
    simp only [↓reduceIte, if_neg hpll, hlivw, decide_eq_true hlv2, decide_eq_true hplv2]
    have hvw : ((X2.setNode bl l (pcRec ra id false)).setBuf id
        (pcPage id ra.nv.isLeaf' ra.ws (pcCount (insSize rl.ins)))).v = X2.v := by
      unfold WX.setBuf WX.setNode; split <;> rfl
    have hmv : ((X2.setNode bl l (pcRec ra id false)).setBuf id
        (pcPage id ra.nv.isLeaf' ra.ws (pcCount (insSize rl.ins)))).t.mv = X2.t.mv := by
      unfold WX.setBuf WX.setNode; split <;> rfl
    have htt : ((X2.setNode bl l (pcRec ra id false)).setBuf id
        (pcPage id ra.nv.isLeaf' ra.ws (pcCount (insSize rl.ins)))).t.t = X2.t.t := by
      unfold WX.setBuf WX.setNode; split <;> rfl
    rw [hvw]
    have hbtx : B2.bv.tx' = tx := Hok2.2.2.1 bl B2 hB2
    icases objOwn_bkt_tx_acc _ bl _ _ $$ Hbo with ⟨%dqb, Hbtx, Hbo⟩
    unfold txFields
    rw [hmv, htt]
    icases Htf with ⟨Hf1, Hf2, Hf3, Hf4, Hf5, Hf6, Hf7, Hf8, Hbufs⟩
    icases (objOwn_live_node _ _ _ _ _).1 $$ Hlo with ⟨Hn, Hins, Hcap, -, Hch, Hchcap, Hkey⟩
    simp only [pcRec, Bool.false_eq_true, ↓reduceIte]
    icases typedPointsto_not_null_dup _ _ _ $$ Hn with ⟨Hn, %Hnn'⟩
    iStructNamed Hn
    wp_auto
    -- the first inode and entry
    ihave %Hlenra := BigSepL2.bigSepL2_length $$ Hws
    obtain ⟨i0, is, hins0⟩ : ∃ i0 is, ra.ins = i0 :: is := by
      cases h : ra.ins with
      | nil => rw [h] at Hlenra; simp at Hlenra; omega
      | cons a b => exact ⟨a, b, rfl⟩
    obtain ⟨w0, wt, hws0⟩ : ∃ w0 wt, ra.ws = w0 :: wt := by
      cases h : ra.ws with
      | nil => rw [h] at hlenws; simp at hlenws; omega
      | cons a b => exact ⟨a, b, rfl⟩
    have hw0 : ra.w0 = w0 := by simp only [NRec.w0, hws0, List.headD_cons]
    have hk0 : ra.k0 = i0.key' := by simp only [NRec.k0, hins0, List.head?_cons, Option.map_some, Option.getD_some]
    ihave #Hw0 : wOwn X2.v true i0 w0 $$ [Hws]
    · rw [hins0, hws0]
      icases BigSepL2.bigSepL2_cons.1 $$ Hws with ⟨H, -⟩
      iexact H
    icases (wOwn_true' _ _ _).1 $$ Hw0 with ⟨%-, #Hk0, -⟩
    have hw0l : w0.ks ≠ Src.stale ∧ w0.vs ≠ Src.stale := hwl w0 (by rw [hws0]; simp)
    have hw0k : 0 < w0.key.length := hkl w0 (by rw [hws0]; simp)
    ihave Hins : ra.nv.inodes' ↦* (i0 :: is) $$ [Hins]
    · rw [← hins0]; iexact Hins
    ihave %Hsl0 := ownSlice_len _ _ _ $$ Hins
    have hset0 : (i0 :: is).set (sint.Z (W64 0)).toNat i0 = i0 :: is := by
      rw [show (sint.Z (W64 0)).toNat = 0 from rfl]; rfl
    have hlen0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z ra.nv.inodes'.len := by
      simp at Hsl0; exact ⟨by decide, by word⟩
    -- `if key == nil { key = node.inodes[0].Key() }`
    wp_join iprop(key_ptr ↦ (if ra.nv.key' = slice.nil then i0.key' else ra.nv.key') ∗ nodep ↦ l ∗
        l.[node, go!"inodes"] ↦ ra.nv.inodes' ∗ ra.nv.inodes' ↦* (i0 :: is))
      with [key Hnodep inodes Hins] as ⟨key, Hnodep, inodes, Hins⟩
    · rw [if_pos Hif]
      rw [ite_eq_left_of_eq_true _ _ (eq_true hlen0)]
      icases ownSlice_elem_acc (sint.Z (W64 0)) i0 _ _ (i0 :: is) (by decide) rfl $$ Hins
        with ⟨Hit, Hsback⟩
      wp_apply hKey $$ [$Hit] as Hit
      ihave Hins := Hsback $$ Hit
      try rw [hset0]
      wp_join_done
    · rw [if_neg Hif]
      iframe
    rw [ite_eq_left_of_eq_true _ _ (eq_true hlen0)]
    icases ownSlice_elem_acc (sint.Z (W64 0)) i0 _ _ (i0 :: is) (by decide) rfl $$ Hins
      with ⟨Hit, Hsback⟩
    wp_apply hKey $$ [$Hit] as Hit
    ihave Hins := Hsback $$ Hit
    try rw [hset0]
    try wp_auto
    -- `node.parent.put(key, node.inodes[0].Key(), nil, node.pgid, 0)`
    have hokl : 0 < (pcOldKey ra).length := by
      unfold pcOldKey; split
      · rw [hw0]; exact hw0k
      · rcases hkey0 with h | h
        · contradiction
        · exact h
    have hoks : (if ra.nv.key' = slice.nil then w0.ks else ra.ksrc) ≠ Src.stale := by
      split
      · exact hw0l.1
      · exact hksrc (by assumption)
    ihave #Hok : srcOwn X2.v (if ra.nv.key' = slice.nil then i0.key' else ra.nv.key')
        (if ra.nv.key' = slice.nil then w0.ks else ra.ksrc) (pcOldKey ra) $$ [Hkey]
    · unfold pcOldKey
      by_cases hkn : ra.nv.key' = slice.nil
      · rw [if_pos hkn, if_pos hkn, if_pos hkn, hw0]; iexact Hk0
      · rw [if_neg hkn, if_neg hkn, if_neg hkn,
          if_pos (show True ∧ ra.nv.key' ≠ slice.nil from ⟨trivial, hkn⟩)]
        iexact Hkey
    ihave #Hnil : srcOwn X2.v slice.nil (Src.own DFrac.discard) ([] : List w8) $$ []
    · unfold srcOwn; iapply ownSlice_nil
    rw [hbtx]
    ihave Hpo : objOwn X2.v ra.nv.parent' (DFrac.own 1) true (.node bl rpa) $$ [Hpo]
    · rw [hparl]; iexact Hpo
    wp_apply (hPut X2.v ra.nv.parent' bl rpa tx X2.t.t.meta' X2.t.mv dqb (DFrac.own 1) wq _ i0.key' slice.nil
      (pcOldKey ra) w0.key [] (if ra.nv.key' = slice.nil then w0.ks else ra.ksrc) w0.ks
      (Src.own DFrac.discard) id (W32 0) hbkp hcapa hsrta hwlp hidlt hokl hw0k
      hoks hw0l.1 (by simp) Hbase) $$ [Hpo Hv Hbtx Hf3 Hf7]
      as ⟨%s, %ins2, Hpo, Hv, Hbtx, Hf3, Hf7⟩
    · iframe; iframe #
    try wp_auto
    have hpe : pcEnt ra id = (⟨W32 0, id, w0.key, [], w0.ks, Src.own DFrac.discard⟩ : WEntry) := by
      simp only [pcEnt, hw0]
    -- the parent's inodes' count its entries'
    icases (objOwn_live_node _ _ _ _ _).1 $$ Hpo with ⟨Hpn, Hpins, Hpcap, Hpws, Hpch, Hpchcap, Hpkey⟩
    icases Hpws with #Hpws
    ihave %Hinsl := BigSepL2.bigSepL2_length $$ Hpws
    ihave Hpo : objOwn X2.v ra.nv.parent' (DFrac.own 1) true (.node bl (pcPar rpa ra id s ins2))
      $$ [Hpn Hpins Hpcap Hpch Hpchcap Hpkey]
    · iapply (objOwn_live_node _ _ _ _ _).2; iframe
      simp only [pcPar, hpe]; iexact Hpws
    -- `node.key = node.inodes[0].Key()`
    rw [ite_eq_left_of_eq_true _ _ (eq_true hlen0)]
    icases ownSlice_elem_acc (sint.Z (W64 0)) i0 _ _ (i0 :: is) (by decide) rfl $$ Hins
      with ⟨Hit, Hsback⟩
    wp_apply hKey $$ [$Hit] as Hit
    ihave Hins := Hsback $$ Hit
    try rw [hset0]
    try wp_auto
    -- `common.Assert(len(node.key) > 0, ...)`
    ihave %Hkl := srcOwn_len X2.v i0.key' w0.ks w0.key hw0l.1 $$ Hk0
    rw [decide_eq_true (show sint.Z (W64 0) < sint.Z i0.key'.len by
      have h3 : (sint.Z i0.key'.len).toNat = w0.key.length := Hkl.1.symm
      have h4 : sint.Z (W64 0) = 0 := rfl
      omega)]
    have hk0ne : ra.k0 ≠ slice.nil := by
      rw [hk0]; intro he
      have h1 := Hkl.1
      rw [he] at h1
      simp [slice.nil] at h1
      have h0 : sint.nat (0#64 : w64) = 0 := by decide
      omega
    wp_apply hAssert
    try wp_auto
    -- the heap back: `l` written with its new key, the parent with the entry
    ihave Hn : (l ↦ (pcRec ra id true).nv : IProp GF)
      $$ [bucket isLeaf unbalanced spilled key pgid parent children inodes]
    · iapply typedPointsto_combine _ _ _ Hnn'
      simp only [TypedPointsto.typedPointstoDef, pcRec, ↓reduceIte, hk0]
      iframe
    ihave Hlo : objOwn X2.v l (DFrac.own 1) true (.node bl (pcRec ra id true))
      $$ [Hn Hins Hcap Hch Hchcap]
    · iapply (objOwn_live_node _ _ _ _ _).2
      simp only [pcRec, ↓reduceIte, hk0, hw0]
      rw [hins0]
      iframe
      isplitr
      · rw [← hins0]; iexact Hws
      · by_cases hk : True ∧ i0.key' ≠ slice.nil
        · rw [if_pos hk]; iexact Hk0
        · rw [if_neg hk]; iempintro
    ihave Hbo := Hbo $$ Hbtx
    ihave Hh := Hback $$ %({ B2 with ns := (B2.ns.insert l (pcRec ra id true)).insert rl.nv.parent' (pcPar rpa ra id s ins2) } : BRec)
      %(fun x => if x = l then pcRec ra id true else pcPar rpa ra id s ins2) [] [Hlo Hpo] [Hbo]
      [Hf1 Hf2 Hf3 Hf4 Hf5 Hf6 Hf7 Hf8 Hbufs] [Hrf]
    · ipureintro
      refine ⟨?_, ?_, hbtx, ?_⟩
      · intro x hx
        simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at hx
        rcases hx with rfl | rfl
        · simp only [↓reduceIte]
          rw [GMap.lookup_insert_ne _ _ hpll, GMap.lookup_insert]
        · simp only [if_neg hpll]; exact GMap.lookup_insert _ _ _
      · intro x hx
        simp only [List.mem_cons, List.not_mem_nil, _root_.or_false, not_or] at hx
        rw [GMap.lookup_insert_ne _ _ (Ne.symm hx.2), GMap.lookup_insert_ne _ _ (Ne.symm hx.1),
          GMap.lookup_insert_ne _ _ (Ne.symm hx.1)]
      · intro x hx
        simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at hx
        rcases hx with rfl | rfl
        · simp only [↓reduceIte, pcRec]; rw [hparl]; exact hpll
        · simp only [if_neg hpll, pcPar, NRec.withEnts]; exact hpparp
    · iapply BigSepL.bigSepL_cons.2
      isplitl [Hlo]
      · simp only [↓reduceIte, decide_eq_true hlv2]; iexact Hlo
      iapply BigSepL.bigSepL_cons.2
      isplitl [Hpo]
      · simp only [if_neg hpll, decide_eq_true hplv2, pcPar, hpe]; rw [← hparl]; iexact Hpo
      iapply BigSepL.bigSepL_nil.2; iempintro
    · iapply (objOwn_bkt_ns _ _ _ _ B2 _).2
      iapply (objOwn_bkt_ns _ _ _ _ B2 _).1
      iexact Hbo
    · iframe
    · iexact Hrf
    ihave Hw := Hclose $$ %_ [] Hh Hv Hst
    · ipureintro
      refine ⟨by unfold WX.setBkt; exact hvw, rfl, by unfold WX.setBkt; exact Prod.ext rfl htt⟩
    -- the stats, done
    icases wtxW_open K tx r m _ $$ Hw with ⟨#-, #-, #-, Hh, Hv, Hst, Hclose⟩
    wp_apply (hInc K tx r m 1 (W64 1)) $$ [Hst] as %_ Hst
    · iframe; iframe #
    ihave Hw := Hclose $$ %_ [] Hh Hv Hst
    · ipureintro; exact ⟨rfl, rfl, rfl⟩
    rw [setBkt_pcFin hB2]
    have hv3 : (((X2.setNode bl l (pcRec ra id true)).setNode bl rl.nv.parent' (pcPar rpa ra id s ins2)).setBuf id (pcPage id ra.nv.isLeaf' ra.ws (pcCount (insSize rl.ins)))).v = X2.v := by
      show ((X2.setNode bl l (pcRec ra id true)).setNode bl rl.nv.parent' (pcPar rpa ra id s ins2)).v = X2.v
      rw [WX.setNode_v, WX.setNode_v]
    iapply HΦ $$ %(((X2.setNode bl l (pcRec ra id true)).setNode bl rl.nv.parent'
        (pcPar rpa ra id s ins2)).setBuf id (pcPage id ra.nv.isLeaf' ra.ws (pcCount (insSize rl.ins))))
      %w2 %(st1 ++ sta) %id [] HR [Hw] [Hdb] Htxp Hnodep Hres
    · ipureintro
      refine ⟨X1, w1, X2, p, ra, rpa, s, ins2, st1, sta, Hfr1, rfl, Hal', hsta, hsta', HC2, Hml2, Hw2,
        hna, fun _ => ⟨hrpa, by simpa only [pcPar, NRec.withEnts, hpe] using Hinsl, hk0ne⟩, ?_⟩
      simp only [pcFin, ne_eq, hpn, not_false_eq_true, _root_.decide_true, ↓reduceIte]
    · iexact Hw
    · rw [hv3]; iexact Hdb

end proof

end Spill

end bbolt
end EtcdGrove
end Perennial
