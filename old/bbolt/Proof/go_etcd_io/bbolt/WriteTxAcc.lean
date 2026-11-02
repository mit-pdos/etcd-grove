/-
A write transaction's bucket, out of `ownWriteTx` for an operation on it (`Put`, `Delete`) and
back with the bucket changed (still clean) and the transaction's stats moved (`wtxUpd`).
-/
module
public import Proof.go_etcd_io.bbolt.WriteLeaf

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section pure
variable [ext : FfiSyntax]

/-- The transaction with the stats `st` and the bucket `bl`'s record `B'`. -/
def wtxUpd (T : WTx) (st : TxStats) (bl : Loc) (B' : BRec) : WTx :=
  { T with t := { T.t with stats' := st }, bs := <[bl := B']> T.bs }

/-- The transaction `T'` is `T` but its stats and its buckets' records (the same buckets). -/
def wtxSame (T T' : WTx) : Prop :=
  T'.mv = T.mv ∧ T'.pm = T.pm ∧ T'.bufs = T.bufs ∧
  (∀ b, (T'.bs !! b).isSome = (T.bs !! b).isSome) ∧ ∃ st, T'.t = { T.t with stats' := st }

theorem wtxSame_upd (T : WTx) (st : TxStats) (bl : Loc) (B B' : BRec) (hB : T.bs !! bl = some B) :
    wtxSame T (wtxUpd T st bl B') := by
  refine ⟨rfl, rfl, rfl, ?_, st, rfl⟩
  intro b
  show ((<[bl := B']> T.bs) !! b).isSome = _
  by_cases h : b = bl
  · subst h; rw [GMap.lookup_insert, hB]; rfl
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm h)]

theorem wtxSame_trans (T1 T2 T3 : WTx) (h1 : wtxSame T1 T2) (h2 : wtxSame T2 T3) : wtxSame T1 T3 := by
  obtain ⟨a1, b1, c1, d1, s1, e1⟩ := h1
  obtain ⟨a2, b2, c2, d2, s2, e2⟩ := h2
  refine ⟨a2.trans a1, b2.trans b1, c2.trans c1, fun b => (d2 b).trans (d1 b), s2, ?_⟩
  rw [e2, e1]

theorem txClean_upd (W : WView) (txl rl : Loc) (T : WTx) (bl : Loc) (B B' : BRec) (st : TxStats)
    (h : txClean W txl rl T) (hB : T.bs !! bl = some B)
    (hc : bktClean W (uint.nat T.mv.pgid') bl B') (htx : B'.bv.tx' = txl) (hbm : B'.bm = B.bm) :
    txClean W txl rl (wtxUpd T st bl B') := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  have hs : ∀ b, ((<[bl := B']> T.bs) !! b).isSome = (T.bs !! b).isSome := by
    intro b
    by_cases hb : b = bl
    · subst hb; rw [GMap.lookup_insert, hB]; rfl
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hb)]
  refine ⟨h1, h2, h3, h4, h5, h6, by show ((<[bl := B']> T.bs) !! rl).isSome; rw [hs]; exact h7, ?_⟩
  intro b0 B0 hb0
  change (<[bl := B']> T.bs) !! b0 = some B0 at hb0
  by_cases hb : b0 = bl
  · subst hb
    rw [GMap.lookup_insert] at hb0; cases hb0
    refine ⟨htx, hc, fun name c hn => ?_⟩
    show ((<[b0 := _]> T.bs) !! c).isSome
    rw [hs]; rw [hbm] at hn; exact (h8 b0 B hB).2.2 name c hn
  · rw [GMap.lookup_insert_ne _ _ (Ne.symm hb)] at hb0
    obtain ⟨k1, k2, k3⟩ := h8 b0 B0 hb0
    refine ⟨k1, k2, fun name c hn => ?_⟩
    show ((<[bl := B']> T.bs) !! c).isSome
    rw [hs]; exact k3 name c hn

end pure

section own
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- The bucket `bl` of a write transaction, with the transaction's fields and the view, and back
(the bucket changed, still clean; the stats moved). -/
theorem ownWriteTx_bkt_acc (W : WView) (txl : Loc) (T : WTx) (bl : Loc) (B : BRec)
    (hB : T.bs !! bl = some B) :
    ownWriteTx (GF := GF) W txl T ⊢
      ⌜viewOK W ∧ txClean W txl (structFieldRef Tx go!"root" txl) T⌝ ∗
      TxW_rest_root txl (DFrac.own 1) T.t ∗ T.t.meta' ↦ T.mv ∗ T.t.pages' ↦$ T.pm ∗ bktOwn W bl B ∗
      wView W ∗
      (∀ (st : TxStats) (B' : BRec),
        ⌜bktClean W (uint.nat T.mv.pgid') bl B' ∧ B'.bv.tx' = txl ∧ B'.bm = B.bm⌝ -∗
        TxW_rest_root txl (DFrac.own 1) { T.t with stats' := st } -∗ T.t.meta' ↦ T.mv -∗
        T.t.pages' ↦$ T.pm -∗
        bktOwn W bl B' -∗ wView W -∗ ownWriteTx W txl (wtxUpd T st bl B')) := by
  unfold ownWriteTx ownWriteTxG
  iintro ⟨⟨Hrest, Hm, Hpm, Hbufs, Hbs⟩, Hv, %Hok⟩
  icases (BigSepM.bigSepM_insert_acc (M := GMap Loc) (Φ := fun bl B => bktOwn (GF := GF) W bl B)
    (show Std.get? T.bs bl = some B from hB)) $$ Hbs with ⟨Hb, Hback⟩
  isplitr
  · ipureintro; exact Hok
  iframe Hrest Hm Hpm Hb Hv
  iintro %st %B' %Hc3 Hrest Hm Hpm Hb Hv
  obtain ⟨Hc, Htx, Hbm⟩ := Hc3
  ihave Hbs := Hback $$ %B' Hb
  iframe
  ipureintro
  exact ⟨Hok.1, txClean_upd W txl _ T bl B B' st Hok.2 hB Hc Htx Hbm⟩

theorem wpt_split {V : Type} [TypedPointsto (GF := GF) V] (l : Loc) (v : V) (a b : Qp) :
    (l ↦{DFrac.own (a + b)} v : IProp GF) ⊣⊢ l ↦{DFrac.own a} v ∗ l ↦{DFrac.own b} v :=
  (typedPointsto_dfractional (GF := GF) l v).dfractional (DFrac.own a) (DFrac.own b)

theorem wpt_split' {V : Type} [TypedPointsto (GF := GF) V] (l : Loc) (v : V) (a b c : Qp)
    (h : c = a + b) :
    (l ↦{DFrac.own c} v : IProp GF) ⊣⊢ l ↦{DFrac.own a} v ∗ l ↦{DFrac.own b} v := by
  rw [h]; exact wpt_split l v a b

theorem TxW_rest_root_split (l : Loc) (t : Tx) (a b : Qp) :
    TxW_rest_root (GF := GF) l (DFrac.own (a + b)) t ⊣⊢
      TxW_rest_root l (DFrac.own a) t ∗ TxW_rest_root l (DFrac.own b) t := by
  unfold TxW_rest_root
  constructor
  · iintro ⟨H1, H2, H3, H4, H5, H6, H7, H8, %Hn⟩
    icases (wpt_split _ _ a b).1 $$ H1 with ⟨H1a, H1b⟩
    icases (wpt_split _ _ a b).1 $$ H2 with ⟨H2a, H2b⟩
    icases (wpt_split _ _ a b).1 $$ H3 with ⟨H3a, H3b⟩
    icases (wpt_split _ _ a b).1 $$ H4 with ⟨H4a, H4b⟩
    icases (wpt_split _ _ a b).1 $$ H5 with ⟨H5a, H5b⟩
    icases (wpt_split _ _ a b).1 $$ H6 with ⟨H6a, H6b⟩
    icases (wpt_split _ _ a b).1 $$ H7 with ⟨H7a, H7b⟩
    icases (wpt_split _ _ a b).1 $$ H8 with ⟨H8a, H8b⟩
    isplitl [H1a H2a H3a H4a H5a H6a H7a H8a]
    · iframe; ipureintro; exact Hn
    · iframe; ipureintro; exact Hn
  · iintro ⟨⟨H1a, H2a, H3a, H4a, H5a, H6a, H7a, H8a, %Hn⟩, ⟨H1b, H2b, H3b, H4b, H5b, H6b, H7b, H8b, -⟩⟩
    ihave H1 := (wpt_split _ _ a b).2 $$ [H1a H1b]
    · iframe
    ihave H2 := (wpt_split _ _ a b).2 $$ [H2a H2b]
    · iframe
    ihave H3 := (wpt_split _ _ a b).2 $$ [H3a H3b]
    · iframe
    ihave H4 := (wpt_split _ _ a b).2 $$ [H4a H4b]
    · iframe
    ihave H5 := (wpt_split _ _ a b).2 $$ [H5a H5b]
    · iframe
    ihave H6 := (wpt_split _ _ a b).2 $$ [H6a H6b]
    · iframe
    ihave H7 := (wpt_split _ _ a b).2 $$ [H7a H7b]
    · iframe
    ihave H8 := (wpt_split _ _ a b).2 $$ [H8a H8b]
    · iframe
    iframe; ipureintro; exact Hn

theorem one_halves : (1 : Qp) = halfQ + halfQ := by simp [halfQ, Qp.half_add_half]

/-- The root bucket's struct, at half, when `bl` is not the root bucket. -/
def rootHalf (txl bl : Loc) : IProp GF :=
  iprop(⌜bl = structFieldRef Tx go!"root" txl⌝ ∨
    ∃ (rv : Bucket), ⌜bl ≠ structFieldRef Tx go!"root" txl⌝ ∗
      structFieldRef Tx go!"root" txl ↦{DFrac.own halfQ} rv)

/-- `ownWriteTx_bkt_acc`, with the root bucket's struct at half when it is not `bl` (what
assembling the transaction's struct needs, for `node.put`). -/
theorem ownWriteTx_put_acc (W : WView) (txl : Loc) (T : WTx) (bl : Loc) (B : BRec)
    (hB : T.bs !! bl = some B) :
    ownWriteTx (GF := GF) W txl T ⊢
      ⌜viewOK W ∧ txClean W txl (structFieldRef Tx go!"root" txl) T⌝ ∗
      TxW_rest_root txl (DFrac.own 1) T.t ∗ T.t.meta' ↦ T.mv ∗ T.t.pages' ↦$ T.pm ∗ bktOwn W bl B ∗
      wView W ∗ rootHalf txl bl ∗
      (∀ (st : TxStats) (B' : BRec),
        ⌜bktClean W (uint.nat T.mv.pgid') bl B' ∧ B'.bv.tx' = txl ∧ B'.bm = B.bm⌝ -∗
        TxW_rest_root txl (DFrac.own 1) { T.t with stats' := st } -∗ T.t.meta' ↦ T.mv -∗
        T.t.pages' ↦$ T.pm -∗ bktOwn W bl B' -∗ wView W -∗ rootHalf txl bl -∗
        ownWriteTx W txl (wtxUpd T st bl B')) := by
  unfold ownWriteTx ownWriteTxG
  iintro ⟨⟨Hrest, Hm, Hpm, Hbufs, Hbs⟩, Hv, %Hok⟩
  icases (BigSepM.bigSepM_delete (M := GMap Loc) (Φ := fun bl B => bktOwn (GF := GF) W bl B)
    (show Std.get? T.bs bl = some B from hB)).1 $$ Hbs with ⟨Hb, Hbs⟩
  isplitr
  · ipureintro; exact Hok
  iframe Hrest Hm Hpm Hb Hv
  by_cases hrl : bl = structFieldRef Tx go!"root" txl
  · isplitl []
    · unfold rootHalf; ileft; ipureintro; exact hrl
    iintro %st %B' %Hc3 Hrest Hm Hpm Hb Hv -
    obtain ⟨Hc, Htx, Hbm⟩ := Hc3
    unfold wtxUpd
    isplitl [Hrest Hm Hpm Hbufs Hb Hbs]
    · iframe
      iapply (BigSepM.bigSepM_insert_delete (M := GMap Loc) (Φ := fun bl B => bktOwn (GF := GF) W bl B)).2
      iframe
    iframe
    ipureintro
    exact ⟨Hok.1, txClean_upd W txl _ T bl B B' st Hok.2 hB Hc Htx Hbm⟩
  · obtain ⟨Br, hBr⟩ := Option.isSome_iff_exists.1 Hok.2.2.2.2.2.2.2.1
    have hBr' : Std.get? (Std.delete T.bs bl) (structFieldRef Tx go!"root" txl) = some Br := by
      show (GMap.delete bl T.bs) !! (structFieldRef Tx go!"root" txl) = some Br
      rw [GMap.lookup_delete_ne _ hrl]; exact hBr
    icases (BigSepM.bigSepM_lookup_acc (M := GMap Loc) (Φ := fun bl B => bktOwn (GF := GF) W bl B)
      hBr').1 $$ Hbs with ⟨Hr, Hrback⟩
    isimp only [bktOwn] at Hr
    icases Hr with ⟨Hrbv, Hr2, Hr3, Hr4, Hr5, Hr6⟩
    icases (wpt_split' _ _ halfQ halfQ 1 one_halves).1 $$ Hrbv with ⟨Hrb1, Hrb2⟩
    isplitl [Hrb1]
    · unfold rootHalf; iright; iexists Br.bv; iframe; ipureintro; exact hrl
    iintro %st %B' %Hc3 Hrest Hm Hpm Hb Hv Hrh
    obtain ⟨Hc, Htx, Hbm⟩ := Hc3
    unfold rootHalf
    icases Hrh with (%h | ⟨%rv, -, Hrb1⟩)
    · exact absurd h hrl
    icombine Hrb1 Hrb2 gives %Heq
    subst Heq
    ihave Hrbv := (wpt_split' _ _ halfQ halfQ 1 one_halves).2 $$ [Hrb1 Hrb2]
    · iframe
    ihave Hbs := Hrback $$ [Hrbv Hr2 Hr3 Hr4 Hr5 Hr6]
    · unfold bktOwn; iframe
    unfold wtxUpd
    isplitl [Hrest Hm Hpm Hbufs Hb Hbs]
    · iframe
      iapply (BigSepM.bigSepM_insert_delete (M := GMap Loc) (Φ := fun bl B => bktOwn (GF := GF) W bl B)).2
      iframe
    iframe
    ipureintro
    exact ⟨Hok.1, txClean_upd W txl _ T bl B B' st Hok.2 hB Hc Htx Hbm⟩

theorem TxW_rest_root_halves (l : Loc) (t : Tx) :
    TxW_rest_root (GF := GF) l (DFrac.own 1) t ⊣⊢
      TxW_rest_root l (DFrac.own halfQ) t ∗ TxW_rest_root l (DFrac.own halfQ) t := by
  rw [one_halves]; exact TxW_rest_root_split l t halfQ halfQ

theorem pt_halves {V : Type} [TypedPointsto (GF := GF) V] (l : Loc) (v : V) :
    (l ↦ v : IProp GF) ⊣⊢ l ↦{DFrac.own halfQ} v ∗ l ↦{DFrac.own halfQ} v :=
  wpt_split' l v halfQ halfQ 1 one_halves

theorem slice_halves {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (s : GoSlice) (vs : List V) :
    (s ↦* vs : IProp GF) ⊣⊢ s ↦*{DFrac.own halfQ} vs ∗ s ↦*{DFrac.own halfQ} vs := by
  have := (ownSlice_dfractional (GF := GF) s vs).dfractional (DFrac.own halfQ) (DFrac.own halfQ)
  have e : (DFrac.own halfQ • DFrac.own halfQ : DFrac) = DFrac.own 1 := by rw [one_halves]; rfl
  rw [e] at this
  exact this

theorem TxW_rest_root_root (l : Loc) (dq : DFrac) (t : Tx) (rv : Bucket) :
    TxW_rest_root (GF := GF) l dq { t with root' := rv } = TxW_rest_root l dq t := rfl

end own

end bbolt
end EtcdGrove
end Perennial
