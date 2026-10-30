/-
A new, empty bucket (`CreateBucket`): its value (`emptyBV`, what `write` makes of an empty leaf
root) is a good inline bucket.
-/
module

public import Proof.go_etcd_io.bbolt.WriteBucket
public import Spec.go_etcd_io.bbolt.Bucket__write

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

/-- The value of a new, empty bucket: a zero header, and a leaf page with no element. -/
def emptyBV : List w8 :=
  List.replicate 16 (0 : w8) ++ [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0]

section pure
variable [ext : FfiSyntax]

theorem writtenBucket_empty : writtenBucket ⟨W64 0, W64 0⟩ true [] [] [] = emptyBV := by
  unfold writtenBucket emptyBV writtenHdr
  simp [writtenElems, kvBytes, inBucketBytes, pageBytes, leBytes]

theorem emptyBV_facts : emptyBV.length = 32 ∧ inBucketRoot emptyBV = 0 ∧
    pageFlags (inlinePage emptyBV) = leafPageFlag ∧ pageCount (inlinePage emptyBV) = 0 ∧
    pageId (inlinePage emptyBV) = 0 ∧ (inlinePage emptyBV).length = 16 := by
  decide

theorem bvalOK_empty (pages : GMap Nat (List w8)) (hwm : Nat) : bvalOK pages hwm emptyBV := by
  obtain ⟨hl, hr, hf, hc, hi, hil⟩ := emptyBV_facts
  have hwf : leafWF (inlinePage emptyBV) (inlinePage emptyBV).length := by
    refine ⟨Nat.le_refl _, ?_, ?_, ?_⟩
    · rw [hc, hil]; decide
    · intro i hi'; rw [hc] at hi'; omega
    · intro i j _ hj; rw [hc] at hj; omega
  refine ⟨bucketWF.inline _ (by omega) hr hf (pageTreeWF.leaf _ _ hf hwf ?_), fun _ => ?_⟩
  · intro i hi'; rw [hc] at hi'; omega
  · exact ⟨hi, hf, hwf, by omega, fun i hi' => by rw [hc] at hi'; omega⟩

theorem wtxSub_trans (T1 T2 T3 : WTx) (h1 : wtxSub T1 T2) (h2 : wtxSub T2 T3) : wtxSub T1 T3 := by
  obtain ⟨a1, b1, c1, d1, s1, e1⟩ := h1
  obtain ⟨a2, b2, c2, d2, s2, e2⟩ := h2
  refine ⟨a2.trans a1, b2.trans b1, c2.trans c1, fun b hb => d2 b (d1 b hb), s2, ?_⟩
  rw [e2, e1]

/-- A bucket with a root node, its inline page dropped: still clean. -/
theorem bktClean_pageNil (W : WView) (hwm : Nat) (bl : Loc) (B : BRec) (hc : bktClean W hwm bl B)
    (hrn : B.bv.rootNode' ≠ null) :
    bktClean W hwm bl { B with bv := { B.bv with page' := null } } := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩ := hc
  exact ⟨fun _ h => absurd h hrn, c2, fun h => absurd h hrn, c4, c5, fun _ => rfl, c7, c8, c9, c10⟩

end pure

section own
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `ownWriteTx_put_acc`, closing as it is or with a bucket added. -/
theorem ownWriteTx_put_add (W : WView) (txl : Loc) (T : WTx) (bl : Loc) (B : BRec)
    (hB : T.bs !! bl = some B) :
    ownWriteTx (GF := GF) W txl T ⊢
      ⌜viewOK W ∧ txClean W txl (structFieldRef Tx go!"root" txl) T⌝ ∗
      TxW_rest_root txl (DFrac.own 1) T.t ∗ T.t.meta' ↦ T.mv ∗ T.t.pages' ↦$ T.pm ∗ bktOwn W bl B ∗
      wView W ∗ rootHalf txl bl ∗
      ((∀ (st : TxStats) (B' : BRec),
          ⌜bktClean W (uint.nat T.mv.pgid') bl B' ∧ B'.bv.tx' = txl ∧ B'.bm = B.bm⌝ -∗
          TxW_rest_root txl (DFrac.own 1) { T.t with stats' := st } -∗ T.t.meta' ↦ T.mv -∗
          T.t.pages' ↦$ T.pm -∗ bktOwn W bl B' -∗ wView W -∗ rootHalf txl bl -∗
          ownWriteTx W txl (wtxUpd T st bl B')) ∧
        (∀ (st : TxStats) (B' : BRec) (cl : Loc) (Bc : BRec),
          ⌜bktClean W (uint.nat T.mv.pgid') bl B' ∧ B'.bv.tx' = txl ∧
            (∀ n c, B'.bm !! n = some c → c = cl ∨ (T.bs !! c).isSome) ∧
            bktClean W (uint.nat T.mv.pgid') cl Bc ∧ Bc.bv.tx' = txl ∧ Bc.bm = ∅⌝ -∗
          TxW_rest_root txl (DFrac.own 1) { T.t with stats' := st } -∗ T.t.meta' ↦ T.mv -∗
          T.t.pages' ↦$ T.pm -∗ bktOwn W bl B' -∗ bktOwn W cl Bc -∗ wView W -∗ rootHalf txl bl -∗
          ownWriteTx W txl (wtxAdd T st bl B' cl Bc))) := by
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
    isplit
    · iintro %st %B' %Hc3 Hrest Hm Hpm Hb Hv -
      obtain ⟨Hc, Htx, Hbm⟩ := Hc3
      unfold wtxUpd
      isplitl [Hrest Hm Hpm Hbufs Hb Hbs]
      · iframe
        iapply (BigSepM.bigSepM_insert_delete (M := GMap Loc) (Φ := fun bl B => bktOwn (GF := GF) W bl B)).2
        iframe
      iframe
      ipureintro
      exact ⟨Hok.1, txClean_upd W txl _ T bl B B' st Hok.2 hB Hc Htx Hbm⟩
    · iintro %st %B' %cl %Bc %Hc6 Hrest Hm Hpm Hb Hc Hv -
      obtain ⟨Hcl, Htx, Hbm, Hcc, Hctx, Hcbm⟩ := Hc6
      ihave Hbs := (BigSepM.bigSepM_insert_delete (M := GMap Loc)
        (Φ := fun bl B => bktOwn (GF := GF) W bl B) (m := T.bs) (i := bl) (x := B')).2 $$ [Hb Hbs]
      · iframe
      isimp only [bktOwn] at Hc
      icases Hc with ⟨Hcbv, Hcrest⟩
      icases bs_fresh W (<[bl := B']> T.bs) cl Bc.bv $$ [Hbs Hcbv] with ⟨%Hfr, Hbs, Hcbv⟩
      · iframe
      have Hfr' : T.bs !! cl = none := by
        have hne : cl ≠ bl := by
          intro e; subst e; rw [GMap.lookup_insert] at Hfr; cases Hfr
        rw [GMap.lookup_insert_ne _ _ (Ne.symm hne)] at Hfr; exact Hfr
      unfold wtxAdd
      isplitl [Hrest Hm Hpm Hbufs Hbs Hcbv Hcrest]
      · iframe
        iapply (BigSepM.bigSepM_insert (M := GMap Loc) (Φ := fun bl B => bktOwn (GF := GF) W bl B)
          (show Std.get? (<[bl := B']> T.bs) cl = none from Hfr)).2
        iframe
        unfold bktOwn; iframe
      iframe
      ipureintro
      exact ⟨Hok.1, txClean_add W txl _ T bl B B' st cl Bc Hok.2 hB Hcl Htx Hbm Hcc Hctx Hcbm Hfr'⟩

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
    isplit
    · iintro %st %B' %Hc3 Hrest Hm Hpm Hb Hv Hrh
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
    · iintro %st %B' %cl %Bc %Hc6 Hrest Hm Hpm Hb Hc Hv Hrh
      obtain ⟨Hcl, Htx, Hbm, Hcc, Hctx, Hcbm⟩ := Hc6
      unfold rootHalf
      icases Hrh with (%h | ⟨%rv, -, Hrb1⟩)
      · exact absurd h hrl
      icombine Hrb1 Hrb2 gives %Heq
      subst Heq
      ihave Hrbv := (wpt_split' _ _ halfQ halfQ 1 one_halves).2 $$ [Hrb1 Hrb2]
      · iframe
      ihave Hbs := Hrback $$ [Hrbv Hr2 Hr3 Hr4 Hr5 Hr6]
      · unfold bktOwn; iframe
      ihave Hbs := (BigSepM.bigSepM_insert_delete (M := GMap Loc)
        (Φ := fun bl B => bktOwn (GF := GF) W bl B) (m := T.bs) (i := bl) (x := B')).2 $$ [Hb Hbs]
      · iframe
      isimp only [bktOwn] at Hc
      icases Hc with ⟨Hcbv, Hcrest⟩
      icases bs_fresh W (<[bl := B']> T.bs) cl Bc.bv $$ [Hbs Hcbv] with ⟨%Hfr, Hbs, Hcbv⟩
      · iframe
      have Hfr' : T.bs !! cl = none := by
        have hne : cl ≠ bl := by
          intro e; subst e; rw [GMap.lookup_insert] at Hfr; cases Hfr
        rw [GMap.lookup_insert_ne _ _ (Ne.symm hne)] at Hfr; exact Hfr
      unfold wtxAdd
      isplitl [Hrest Hm Hpm Hbufs Hbs Hcbv Hcrest]
      · iframe
        iapply (BigSepM.bigSepM_insert (M := GMap Loc) (Φ := fun bl B => bktOwn (GF := GF) W bl B)
          (show Std.get? (<[bl := B']> T.bs) cl = none from Hfr)).2
        iframe
        unfold bktOwn; iframe
      iframe
      ipureintro
      exact ⟨Hok.1, txClean_add W txl _ T bl B B' st cl Bc Hok.2 hB Hcl Htx Hbm Hcc Hctx Hcbm Hfr'⟩

end own

end bbolt
end EtcdGrove
end Perennial
