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
    (hn16 : rl.ws.length < 0xFFFF)
    (hbody : 16 + (pageBody true (wsMs rl.ws)).length ≤ pcCount (insSize rl.ins) * 4096)
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
  icases wtxW_heapOK K tx r m X1 $$ Hw with ⟨Hw, %Hok1⟩
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
    · iapply HΦe $$ %(GoInterface.ok ii) %X1 %w1 %st1 [] Herrok [Hw Hdb] Htxp Hnodep Hres
      · ipureintro; exact ⟨Herr, hfw.1, hfw.2, by rw [hv1]⟩
      · ileft; iframe
    · obtain ⟨⟨Xd, b, hd, rfl⟩, hC, hfl⟩ := Hl
      iapply HΦe $$ %(GoInterface.ok ii) %(Xd.rebase b) %w' %st1 [] Herrok [Hw Hdb] Htxp Hnodep Hres
      · ipureintro
        refine ⟨Herr, hC.trans hfw.1, hfl.trans hfw.2, ?_⟩
        show Xd.v.pages = X1.v.pages
        rw [hd.2.1]
      · iright; iframe
  -- `allocate`'s success
  obtain ⟨Hal, HC2, Hml2, Hw2⟩ := Hal
  subst Herr
  have Hal' : allocRes X1 X2 w1.fl w2.fl w.wtxid (pcCount (insSize rl.ins)) p id := by
    have hsn : sint.nat (W64 (pcCount (insSize rl.ins) : Int)) = pcCount (insSize rl.ins) := by
      unfold pcCount at hc0 ⊢; word
    rw [← hwtx, ← hsn]; exact Hal
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
        (pcPage id ra.nv.isLeaf' ra.ws (pcCount (insSize rl.ins)))) %w2 %st1 %id
      [] [Hw] [Hdb] Htxp Hnodep Hres
    · ipureintro
      refine ⟨X1, w1, X2, p, ra, ra, slice.nil, [], Hfr1, Hal', HC2, Hml2, Hw2, hna,
        fun h => absurd hpl h, ?_⟩
      simp only [pcFin, hpl, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
        ↓reduceIte]
    · iexact Hw
    · rw [hv3]; iexact Hdb
  · -- a parent: the put. Not yet (U9l hand-off). Steps, from `Hw : wtxW` of
    -- `X2w = (X2.setNode bl l (pcRec ra id false)).setBuf id (pcPage …)`, `pl = ra.nv.parent'`:
    -- 1. `pl`'s record in `X2w`: `hpar` gives `rp` at `X`; `X1` is `X` or a `setNode` of `l`
    --    (`WX.setNode_node_ne`, `pl ≠ l`); `allocRes_node Hal'` gives `rpa` at `X2`, `nodeSim`;
    --    `X2w` keeps it (`setNode_node_ne`; `setBuf` keeps `bs`). Sortedness through `nodeSim`
    --    (`wsSorted` reads `wKey` only: `ws.map wDat` equal); `wsLive rpa.ws` and the keys'
    --    lengths from `liveFresh X2`/`derefPre X2` (`allocRes_derefPre'`, as `hlf2`).
    -- 2. `wtxW_open`, then `wtxHeap_setBkt_acc tx 1 X2w bl B [l, pl] f` (both live): `l`'s and
    --    `pl`'s objects, the bucket's (its `tx` field: the `Htxf` dance of `node__free`), the
    --    transaction's fields (`tx.meta`, `meta' ↦ mv`, at full fraction: `node.put` takes `dqb`).
    -- 3. `l`'s object unfolded (`objOwn_live_node`, `iStructNamed`); `key := node.key`; the nil
    --    test (`decide (ra.nv.key' = slice.nil)`); `inodes[0].Key()` by `ownSlice_elem_acc` and
    --    `hKey` (as `Spill/SplitIndex`); the old key's source is the key's `srcOwn` (`Hkey`) or the
    --    first inode's (the persistent `wOwn` list's head: `wOwn_true'`).
    -- 4. `hPut X2.v pl bl rpa tx mp mv dqb wq oldKey k0 slice.nil okb (w0.key) [] oks w0.ks
    --    (Src.own DFrac.discard) id (W32 0)` (the nil value's `srcOwn`: `ownSlice_nil` made
    --    persistent); its post's `s`, `ins` are `pcPar`'s.
    -- 5. `node.key = node.inodes[0].Key()` (`hKey` again, the field's store); `Assert` with
    --    `0 < len`: a `srcOwn` gives the slice's length (`ownSlice_len` for `↦*□`, `inViewAt`'s
    --    for the view).
    -- 6. back: `l`'s object for `pcRec ra id true` (its key's `srcOwn` the first entry's),
    --    `pl`'s for `pcPar rpa ra id s ins`, the wand with `B' = {B with ns := (B.ns.insert l _)
    --    .insert pl _}`; `IncSpill` (reopen `wtxW` for `statsTok`, as the parentless case); the
    --    post's `X3 = pcFin X2 bl l ra pl rpa s ins id count true` needs `setBuf`/`setNode`
    --    commuting and a `setNode` of `l` overwriting one (`setNode_eq` unfolds both).
    rw [decide_eq_false hp]
    sorry

end proof

end Spill

end bbolt
end EtcdGrove
end Perennial
