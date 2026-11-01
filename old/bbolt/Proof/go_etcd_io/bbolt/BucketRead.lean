/-
A bucket on the read path (a read transaction: no nodes, `tx.pages` nil), as the bucket API
owns it.

`bktR bl V q`: the bucket at `bl` with the view `V` (`CursorModel.lean`), at the fraction `q`:
what a cursor on it needs (`bktCtx`, `bktPages`), and, for an inline bucket, the transaction's
pages too (a nested bucket of it has its tree there); its tree well-formed (`treeOK`: the
cursor's `wfAt` and the nested buckets' trees). It is fractional (`bktR_split`), so a bucket
can be read while a cursor on it is open, or a nested bucket open.

`txStats txl`: the transaction's statistics, which creating a cursor writes (an atomic add):
kept apart from the bucket's view, which holds the transaction's other fields.
-/
module

public import Proof.go_etcd_io.bbolt.CursorModel
public import Proof.go_etcd_io.bbolt.StructSplit
public import Proof.go_etcd_io.bbolt.internal.common.Bytes

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section view
variable [ext : FfiSyntax]

/-- The bucket's tree is well-formed, nested buckets included (for an inline bucket: its leaf
page, and the trees of the buckets in it). -/
def BktView.treeOK (V : BktView) : Prop :=
  if V.root = W64 0 then pageFlags V.ipg = leafPageFlag ∧ pageTreeWF V.pages V.hwm V.ipg V.ipg.length
  else treeWF V.pages V.hwm (uint.nat V.root)

theorem treeOK_wfAt (V : BktView) (h : V.treeOK) : V.wfAt V.root := by
  unfold BktView.treeOK at h
  unfold BktView.wfAt
  by_cases hr : V.root = W64 0
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hr)] at h ⊢
    obtain ⟨hfl, hpt⟩ := h
    cases hpt with
    | leaf _ _ _ hw _ =>
      refine ⟨hr, hfl, hw, ?_⟩
      have := hw.2.1; have := hw.1; unfold elemOff at *; omega
    | branch _ _ hb _ _ => rw [hfl] at hb; exact absurd hb (by decide)
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hr)] at h ⊢
    exact h

end view

section preds
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- The transaction's statistics (any value). -/
def txStats (txl : Loc) : IProp GF :=
  iprop(∃ (s : TxStats), structFieldRef Tx go!"stats" txl ↦ s)

/-- The bucket at `bl` on the read path, at the fraction `q` (see the module doc). -/
def bktR (bl : Loc) (V : BktView) (q : Qp) : IProp GF :=
  iprop(bktCtx bl V q ∗ bktPages V q ∗
    (if V.root = W64 0 then pagesView V.data (uint.nat V.ps) q V.pages else True) ∗
    ⌜V.ok ∧ V.treeOK⌝)

theorem pt_split {V : Type} [TypedPointsto (GF := GF) V] (l : Loc) (v : V) (a b : Qp) :
    (l ↦{DFrac.own (a + b)} v : IProp GF) ⊣⊢ l ↦{DFrac.own a} v ∗ l ↦{DFrac.own b} v :=
  (typedPointsto_dfractional (GF := GF) l v).dfractional (DFrac.own a) (DFrac.own b)

theorem bytes_split (l : Loc) (bs : List w8) (a b : Qp) :
    bytesPointsto (GF := GF) l (DFrac.own (a + b)) bs ⊣⊢
      bytesPointsto l (DFrac.own a) bs ∗ bytesPointsto l (DFrac.own b) bs :=
  (bytesPointsto_dfractional (GF := GF) l bs).dfractional (DFrac.own a) (DFrac.own b)

theorem pagesView_split (data : Loc) (ps : Nat) (pages : GMap Nat (List w8)) (a b : Qp) :
    pagesView (GF := GF) data ps (a + b) pages ⊣⊢
      pagesView data ps a pages ∗ pagesView data ps b pages := by
  unfold pagesView
  rw [← BigSepM.bigSepM_sep_eq]
  exact ⟨BigSepM.bigSepM_mono_of_forall (bytes_split _ _ a b).1,
    BigSepM.bigSepM_mono_of_forall (bytes_split _ _ a b).2⟩

theorem bktPages_split (V : BktView) (a b : Qp) :
    bktPages (GF := GF) V (a + b) ⊣⊢ bktPages V a ∗ bktPages V b := by
  unfold bktPages
  split
  · exact bytes_split _ _ a b
  · exact pagesView_split _ _ _ a b

theorem Tx_rest_stats_split (l : Loc) (t : Tx) (a b : Qp) :
    Tx_rest_stats (GF := GF) l (DFrac.own (a + b)) t ⊣⊢
      Tx_rest_stats l (DFrac.own a) t ∗ Tx_rest_stats l (DFrac.own b) t := by
  unfold Tx_rest_stats
  constructor
  · iintro ⟨H1, H2, H3, H4, H5, H6, H7, H8, %Hn⟩
    icases (pt_split _ _ a b).1 $$ H1 with ⟨H1a, H1b⟩
    icases (pt_split _ _ a b).1 $$ H2 with ⟨H2a, H2b⟩
    icases (pt_split _ _ a b).1 $$ H3 with ⟨H3a, H3b⟩
    icases (pt_split _ _ a b).1 $$ H4 with ⟨H4a, H4b⟩
    icases (pt_split _ _ a b).1 $$ H5 with ⟨H5a, H5b⟩
    icases (pt_split _ _ a b).1 $$ H6 with ⟨H6a, H6b⟩
    icases (pt_split _ _ a b).1 $$ H7 with ⟨H7a, H7b⟩
    icases (pt_split _ _ a b).1 $$ H8 with ⟨H8a, H8b⟩
    isplitl [H1a H2a H3a H4a H5a H6a H7a H8a]
    · iframe; ipureintro; exact Hn
    · iframe; ipureintro; exact Hn
  · iintro ⟨⟨H1a, H2a, H3a, H4a, H5a, H6a, H7a, H8a, %Hn⟩, ⟨H1b, H2b, H3b, H4b, H5b, H6b, H7b, H8b, -⟩⟩
    ihave H1 := (pt_split _ _ a b).2 $$ [H1a H1b]
    · iframe
    ihave H2 := (pt_split _ _ a b).2 $$ [H2a H2b]
    · iframe
    ihave H3 := (pt_split _ _ a b).2 $$ [H3a H3b]
    · iframe
    ihave H4 := (pt_split _ _ a b).2 $$ [H4a H4b]
    · iframe
    ihave H5 := (pt_split _ _ a b).2 $$ [H5a H5b]
    · iframe
    ihave H6 := (pt_split _ _ a b).2 $$ [H6a H6b]
    · iframe
    ihave H7 := (pt_split _ _ a b).2 $$ [H7a H7b]
    · iframe
    ihave H8 := (pt_split _ _ a b).2 $$ [H8a H8b]
    · iframe
    iframe; ipureintro; exact Hn

theorem Tx_rest_stats_stats (l : Loc) (dq : DFrac) (t : Tx) (s : TxStats) :
    Tx_rest_stats (GF := GF) l dq { t with stats' := s } = Tx_rest_stats l dq t := by
  unfold Tx_rest_stats; rfl

theorem Tx_rest_stats_with (l : Loc) (dq : DFrac) (t : Tx) (s : TxStats) :
    Tx_rest_stats (GF := GF) l dq t ⊢ Tx_rest_stats l dq { t with stats' := s } := by
  unfold Tx_rest_stats; exact .rfl

/-- A transaction's fields but `stats` and `root`. -/
def Tx_rest_root (l : Loc) (dq : DFrac) (v : Tx) : IProp GF :=
  iprop(structFieldRef Tx go!"writable" l ↦{dq} v.writable' ∗
    structFieldRef Tx go!"managed" l ↦{dq} v.managed' ∗
    structFieldRef Tx go!"db" l ↦{dq} v.db' ∗
    structFieldRef Tx go!"meta" l ↦{dq} v.meta' ∗
    structFieldRef Tx go!"pages" l ↦{dq} v.pages' ∗
    structFieldRef Tx go!"commitHandlers" l ↦{dq} v.commitHandlers' ∗
    structFieldRef Tx go!"WriteFlag" l ↦{dq} v.WriteFlag' ∗ ⌜l ≠ null⌝)

theorem Tx_rest_stats_root (l : Loc) (dq : DFrac) (t : Tx) :
    Tx_rest_stats (GF := GF) l dq t ⊣⊢
      structFieldRef Tx go!"root" l ↦{dq} t.root' ∗ Tx_rest_root l dq t := by
  unfold Tx_rest_stats Tx_rest_root
  constructor
  · iintro ⟨H1, H2, H3, H4, H5, H6, H7, H8, %Hn⟩
    iframe; ipureintro; exact Hn
  · iintro ⟨H5, H1, H2, H3, H4, H6, H7, H8, %Hn⟩
    iframe; ipureintro; exact Hn

theorem bktCtx_split (bl : Loc) (V : BktView) (a b : Qp) :
    bktCtx (GF := GF) bl V (a + b) ⊣⊢ bktCtx bl V a ∗ bktCtx bl V b := by
  unfold bktCtx
  constructor
  · iintro ⟨%bv, %ib, %t, %dbl, Hb, Hib, Ht, Hd, Hps, %Hcx⟩
    icases (pt_split _ _ a b).1 $$ Hb with ⟨Hba, Hbb⟩
    icases (pt_split _ _ a b).1 $$ Hib with ⟨Hiba, Hibb⟩
    icases (Tx_rest_stats_split _ _ a b).1 $$ Ht with ⟨Hta, Htb⟩
    icases (pt_split _ _ a b).1 $$ Hd with ⟨Hda, Hdb⟩
    icases (pt_split _ _ a b).1 $$ Hps with ⟨Hpsa, Hpsb⟩
    isplitl [Hba Hiba Hta Hda Hpsa]
    · iexists bv, ib, t, dbl; iframe; ipureintro; exact Hcx
    · iexists bv, ib, t, dbl; iframe; ipureintro; exact Hcx
  · iintro ⟨⟨%bv, %ib, %t, %dbl, Hba, Hiba, Hta, Hda, Hpsa, %Hcx⟩,
      ⟨%bv', %ib', %t', %dbl', Hbb, Hibb, Htb, Hdb, Hpsb, %Hcx'⟩⟩
    have Hcx0 := Hcx
    obtain ⟨Hr, -, -, Hdb1, -, -, -, -, Hbv, Ht1, Hsq⟩ := Hcx0
    obtain ⟨Hr', -, -, Hdb1', -, -, -, -, Hbv', Ht1', Hsq'⟩ := Hcx'
    have Hib : ib = ib' := by
      cases ib; cases ib'; simp only at Hr Hr' Hsq Hsq'; rw [Hr, Hr', Hsq, Hsq']
    subst Hbv Hbv' Ht1 Ht1' Hib Hdb1 Hdb1'
    ihave Hb := (pt_split _ _ a b).2 $$ [Hba Hbb]
    · iframe
    ihave Hib := (pt_split _ _ a b).2 $$ [Hiba Hibb]
    · iframe
    ihave Ht := (Tx_rest_stats_split _ _ a b).2 $$ [Hta Htb]
    · iframe
    ihave Hd := (pt_split _ _ a b).2 $$ [Hda Hdb]
    · iframe
    ihave Hps := (pt_split _ _ a b).2 $$ [Hpsa Hpsb]
    · iframe
    iexists V.bkt, ib, V.txv, V.txv.db'
    iframe
    ipureintro; exact Hcx

theorem bktR_split (bl : Loc) (V : BktView) (a b : Qp) :
    bktR (GF := GF) bl V (a + b) ⊣⊢ bktR bl V a ∗ bktR bl V b := by
  unfold bktR
  by_cases hr : V.root = W64 0 <;> simp only [hr, ↓reduceIte]
  · constructor
    · iintro ⟨Hc, Hp, He, %Hok⟩
      icases (bktCtx_split _ _ a b).1 $$ Hc with ⟨Hca, Hcb⟩
      icases (bktPages_split _ a b).1 $$ Hp with ⟨Hpa, Hpb⟩
      icases (pagesView_split _ _ _ a b).1 $$ He with ⟨Hea, Heb⟩
      isplitl [Hca Hpa Hea]
      · iframe; ipureintro; exact Hok
      · iframe; ipureintro; exact Hok
    · iintro ⟨⟨Hca, Hpa, Hea, %Hok⟩, ⟨Hcb, Hpb, Heb, -⟩⟩
      ihave Hc := (bktCtx_split _ _ a b).2 $$ [Hca Hcb]
      · iframe
      ihave Hp := (bktPages_split _ a b).2 $$ [Hpa Hpb]
      · iframe
      ihave He := (pagesView_split _ _ _ a b).2 $$ [Hea Heb]
      · iframe
      iframe; ipureintro; exact Hok
  · constructor
    · iintro ⟨Hc, Hp, -, %Hok⟩
      icases (bktCtx_split _ _ a b).1 $$ Hc with ⟨Hca, Hcb⟩
      icases (bktPages_split _ a b).1 $$ Hp with ⟨Hpa, Hpb⟩
      isplitl [Hca Hpa]
      · iframe; ipureintro; exact ⟨trivial, Hok⟩
      · iframe; ipureintro; exact ⟨trivial, Hok⟩
    · iintro ⟨⟨Hca, Hpa, -, %Hok⟩, ⟨Hcb, Hpb, -, -⟩⟩
      ihave Hc := (bktCtx_split _ _ a b).2 $$ [Hca Hcb]
      · iframe
      ihave Hp := (bktPages_split _ a b).2 $$ [Hpa Hpb]
      · iframe
      iframe; ipureintro; exact ⟨trivial, Hok⟩

theorem pt_split' {V : Type} [TypedPointsto (GF := GF) V] (l : Loc) (v : V) (a b c : Qp)
    (h : c = a + b) :
    (l ↦{DFrac.own c} v : IProp GF) ⊣⊢ l ↦{DFrac.own a} v ∗ l ↦{DFrac.own b} v := by
  rw [h]; exact pt_split l v a b

theorem pagesView_split' (data : Loc) (ps : Nat) (pages : GMap Nat (List w8)) (a b c : Qp)
    (h : c = a + b) :
    pagesView (GF := GF) data ps c pages ⊣⊢
      pagesView data ps a pages ∗ pagesView data ps b pages := by
  rw [h]; exact pagesView_split data ps pages a b

theorem Tx_rest_stats_split' (l : Loc) (t : Tx) (a b c : Qp) (h : c = a + b) :
    Tx_rest_stats (GF := GF) l (DFrac.own c) t ⊣⊢
      Tx_rest_stats l (DFrac.own a) t ∗ Tx_rest_stats l (DFrac.own b) t := by
  rw [h]; exact Tx_rest_stats_split l t a b

theorem bktR_split' (bl : Loc) (V : BktView) (a b c : Qp) (h : c = a + b) :
    bktR (GF := GF) bl V c ⊣⊢ bktR bl V a ∗ bktR bl V b := by
  rw [h]; exact bktR_split bl V a b

/-- A bucket is its cursor's context and pages (and back). -/
theorem bktR_acc (bl : Loc) (V : BktView) (q : Qp) :
    bktR (GF := GF) bl V q ⊢ ⌜V.ok ∧ V.treeOK⌝ ∗ bktCtx bl V q ∗ bktPages V q ∗
      (bktCtx bl V q -∗ bktPages V q -∗ bktR bl V q) := by
  unfold bktR
  iintro ⟨Hc, Hp, He, %Hok⟩
  iframe Hc Hp
  isplitr
  · ipureintro; exact Hok
  iintro Hc Hp
  iframe
  ipureintro; exact Hok

/-- A bucket's location is not null. -/
theorem bktR_ne_null (bl : Loc) (V : BktView) (q : Qp) :
    bktR (GF := GF) bl V q ⊢ ⌜bl ≠ null⌝ ∗ bktR bl V q := by
  refine (and_intro ?_ .rfl).trans persistent_and_sep_mp
  unfold bktR bktCtx
  iintro ⟨⟨%bv, %ib, %t, %dbl, Hb, -⟩, -⟩
  iapply typedPointsto_not_null $$ Hb

/-- A cursor, dropped: its bucket's context and pages. -/
theorem curI_drop (cl bl : Loc) (V : BktView) (q : Qp) (es : List elemRef) :
    curI (GF := GF) cl bl V q es ⊢ bktCtx bl V q ∗ bktPages V q := by
  unfold curI
  iintro ⟨%cv, -, -, -, -, Hc, Hp⟩
  iframe

theorem kv_inside (p : Loc) (pg : List w8) (i : Int) (h0 : 0 ≤ i) (hi : i < pageCount pg) :
    kvResult p pg i =
      (sliceAt p (elemOff i.toNat + leafPos pg i.toNat) (leafKsize pg i.toNat),
       sliceAt p (elemOff i.toNat + leafPos pg i.toNat + leafKsize pg i.toNat) (leafVsize pg i.toNat),
       W32 (leafFlags pg i.toNat)) := by
  unfold kvResult
  rw [if_neg (by omega)]
  rfl

theorem kv_past (p : Loc) (pg : List w8) (i : Int) (hi : (pageCount pg : Int) ≤ i) :
    kvResult p pg i = (slice.nil, slice.nil, W32 0) := by
  unfold kvResult
  rw [if_pos (Or.inr hi)]

/-- Key `i` of a leaf page, taken out of the page's bytes as a slice (and given back). -/
theorem leaf_key_acc (p : Loc) (q : DFrac) (pg : List w8) (i : Nat) (hw : leafWF pg pg.length)
    (hi : i < pageCount pg) (hc : p.locCar ≠ 0) :
    bytesPointsto (GF := GF) p q pg ⊢
      sliceAt p (elemOff i + leafPos pg i) (leafKsize pg i) ↦*{q} leafKey pg i ∗
      (sliceAt p (elemOff i + leafPos pg i) (leafKsize pg i) ↦*{q} leafKey pg i -∗
        bytesPointsto p q pg) := by
  have h1 := (hw.2.2.1 i hi).1
  have h2 := hw.1
  have h3 := leAt_lt pg (elemOff i + 8) 4
  exact bytes_slice_acc p q pg _ _ (by omega) (by unfold leafKsize; omega) hc

/-- Value `i` of a leaf page, taken out of the page's bytes as a slice (and given back). -/
theorem leaf_value_acc (p : Loc) (q : DFrac) (pg : List w8) (i : Nat) (hw : leafWF pg pg.length)
    (hi : i < pageCount pg) (hc : p.locCar ≠ 0) :
    bytesPointsto (GF := GF) p q pg ⊢
      sliceAt p (elemOff i + leafPos pg i + leafKsize pg i) (leafVsize pg i) ↦*{q} leafValue pg i ∗
      (sliceAt p (elemOff i + leafPos pg i + leafKsize pg i) (leafVsize pg i) ↦*{q} leafValue pg i -∗
        bytesPointsto p q pg) := by
  have h1 := (hw.2.2.1 i hi).1
  have h2 := hw.1
  have h3 := leAt_lt pg (elemOff i + 12) 4
  exact bytes_slice_acc p q pg _ _ (by omega) (by unfold leafVsize; omega) hc

end preds

end bbolt
end EtcdGrove
end Perennial
