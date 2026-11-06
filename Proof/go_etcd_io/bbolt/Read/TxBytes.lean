/-
`txBytesDef_acc` (U6w, the review's F2): a slice the transaction returned, read with the whole
transaction at any fraction. Its view's fragment is at the fixed key `null` for both kinds
(`viewOf`), so it is the transaction's current view (a writer's `X.v`, a reader's `v`), whose cells
`boltTx` holds. Moved here from `Inv/Tx` (where it was a `sorry`), which cannot see the view's
cells' accessors; `Inv/FileHolds` imports it for `Api.txBytes_acc`.
-/
module

public import Proof.go_etcd_io.bbolt.Read.WQ

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section txbytes
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

private instance reg_persistent_tb (tx : Loc) (B : BNs) (r : TxReg) :
    Persistent (reg (GF := GF) tx B r) := by
  unfold reg; infer_instance

/-- `wtxWQ`'s registration. -/
theorem wtxWQ_reg (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (q : Qp) (X : WX) :
    wtxWQ (GF := GF) K tx r m q X ⊢ wtxWQ K tx r m q X ∗ reg tx K.B r := by
  unfold wtxWQ wtxCoreQ
  iintro ⟨⟨Hpkg, Hcore, Hr, #Hreg, Hrest⟩, Hcells, Hmap⟩
  iframe; iframe #

/-- Two fragments of a transaction's view agree. -/
theorem viewOf_agree (r : TxReg) (v v' : View) :
    viewOf (GF := GF) r v ∗ viewOf r v' ⊢ ⌜v = v'⌝ := by
  unfold viewOf
  iintro ⟨H1, H2⟩
  icombine H1 H2 gives %h
  ipureintro; exact h.2

/-- A slice of the view, read through the cells (at any fraction), and back. -/
theorem viewCells_slice_acc1 (qc : Qp) (v : View) (hb : 0 < v.base.addr) (s : GoSlice)
    (bs : List w8) (h : inViewAt v s bs) :
    viewCells (GF := GF) qc v ⊢ ∃ dq : DFrac, s ↦*{dq} bs ∗ (s ↦*{dq} bs -∗ viewCells qc v) := by
  iintro Hc
  icases viewCells_slices_acc qc v [(s, bs)] hb (by simpa using h) $$ Hc with ⟨%dq, Hl, Hcb⟩
  iexists dq
  icases BigSepL.bigSepL_cons.1 $$ Hl with ⟨Hl, -⟩
  iframe Hl
  iintro Hs
  iapply Hcb
  iapply BigSepL.bigSepL_cons.2
  iframe Hs
  iapply BigSepL.bigSepL_nil.2; iempintro

/-- A reader's view's cells, its base positive, its registration and view, out of `rdTxK`. -/
theorem rdTxK_view_acc (K : BC) (tx : Loc) (src : PairSrc) (q : Qp) (T : TxView) (v : View) :
    rdTxK (GF := GF) K tx src q T v ⊢ ∃ (r : TxReg) (qc : Qp), reg tx K.B r ∗ viewOf r v ∗
      ⌜0 < v.base.addr⌝ ∗ viewCells qc v ∗ (viewCells qc v -∗ rdTxK K tx src q T v) := by
  unfold rdTxK rtxFrac
  iintro ⟨%r, %c, %mv, %k, %Hc, #Hreg, #Hpk, #Hcore, Hv, Hex,
    ⟨%t, Hw, Hm, Hmeta, Hroot, Hfill, Hpages, Hch, Hwf, Hdb, Hmv, Hcells,
      ⟨%l, Hg, Hmf, %Hl⟩, #Hvo, %Hf⟩, Hpool⟩
  ihave %Hnn : ⌜0 < v.base.addr⌝ $$ [Hmf]
  · iunfold mapFields at Hmf; icases Hmf with ⟨-, -, -, -, %H⟩; ipureintro; exact H.2.1
  iexists r, _
  iframe Hreg Hvo Hcells
  isplitr
  · ipureintro; exact Hnn
  iintro Hcells
  iexists r, c, mv, k
  iframe; iframe #
  isplitr
  · ipureintro; exact Hc
  ipureintro; exact ⟨Hl, Hf⟩

theorem txBytesDef_acc (B : BNs) (N : Namespace) (tx : Loc) (q : Qp) (T : TxView)
    (s : GoSlice) (b : GoString) :
    txBytesDef (GF := GF) B tx s b ∗ boltTxDef B N tx q T ⊢
      ∃ dq : DFrac, s ↦*{dq} b ∗ (s ↦*{dq} b -∗ boltTxDef B N tx q T) := by
  unfold txBytesDef
  iintro ⟨Hs, Ht⟩
  icases Hs with (#Hs | ⟨%r, %v, #Hreg, #Hvo, %Hin⟩)
  · iexists DFrac.discard
    iframe Hs
    iintro -
    iexact Ht
  by_cases hrw : T.rw = true
  · icases (boltTxDef_wtxWQ B N tx q T hrw).1 $$ Ht
      with ⟨%K, %r', %c, %X, %HK, #Hfull, #Hvf, Hv, Hw, Hst, %Hf⟩
    obtain ⟨KB, KN, Kdb, Kp, Ksp, Kt0⟩ := K
    obtain ⟨hB, hN, hT⟩ := HK
    simp only at hB hN
    subst hB hN
    icases wtxWQ_reg _ tx r' true q X $$ Hw with ⟨Hw, #Hreg'⟩
    iunfold reg at Hreg Hreg'
    icombine Hreg Hreg' gives %hr
    obtain ⟨-, rfl⟩ := hr
    ihave %Hvv := viewOf_agree r v X.v $$ [Hvo Hvf]
    · iframe #
    subst Hvv
    icases wtxWQ_cells_acc _ tx r true q X $$ Hw with ⟨%Hbase, Hc, Hwb⟩
    icases viewCells_slice_acc1 (QpMul q wq) X.v Hbase s b Hin $$ Hc with ⟨%dq, Hsb, Hcb⟩
    iexists dq
    iframe Hsb
    iintro Hsb
    ihave Hc := Hcb $$ Hsb
    ihave Hw := Hwb $$ Hc
    iapply (boltTxDef_wtxWQ _ _ tx q T hrw).2
    iexists _, r, c, X
    iframe; iframe #
    ipureintro; exact ⟨⟨rfl, rfl, hT⟩, Hf⟩
  · have hro : T.rw = false := by simpa using hrw
    ihave Ht := (boltTx_rdTx B N tx q T hro).1 $$ Ht
    icases Ht with ⟨%db, Hr, #Hdb⟩
    ihave Hr := (rdTx_rdTxK B N tx .loan q T).1 $$ Hr
    icases Hr with ⟨%K, %v', %HK, Hk⟩
    obtain ⟨KB, KN, Kdb, Kp, Ksp, Kt0⟩ := K
    obtain ⟨hKB, hKN⟩ := HK
    simp only at hKB hKN
    subst hKB hKN
    icases rdTxK_view_acc _ tx .loan q T v' $$ Hk with ⟨%r', %qc, #Hreg', #Hvo', %Hbase, Hc, Hkb⟩
    iunfold reg at Hreg Hreg'
    icombine Hreg Hreg' gives %hr
    obtain ⟨-, rfl⟩ := hr
    ihave %Hvv := viewOf_agree r v v' $$ [Hvo Hvo']
    · iframe #
    subst Hvv
    icases viewCells_slice_acc1 qc v Hbase s b Hin $$ Hc with ⟨%dq, Hsb, Hcb⟩
    iexists dq
    iframe Hsb
    iintro Hsb
    ihave Hc := Hcb $$ Hsb
    ihave Hk := Hkb $$ Hc
    iapply (boltTx_rdTx _ _ tx q T hro).2
    iexists db
    iframe #
    iapply (rdTx_rdTxK _ _ tx .loan q T).2
    iexists _, v
    iframe
    ipureintro; exact ⟨rfl, rfl⟩

end txbytes

end bbolt
end EtcdGrove
end Perennial
