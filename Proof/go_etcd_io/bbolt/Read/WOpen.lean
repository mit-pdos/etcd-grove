/-
The writer's opened buckets (U6e, `notes/bbolt-proof-plan.md`): the record `openBucket` makes on
a nested bucket's value (`openedRec`, `bktOpened`'s facts of the child), and the writer's fields
`openBucket` reads (`tx.writable`) and the root's `FillPercent` (a fresh bucket is not the root).
-/
module

public import Proof.go_etcd_io.bbolt.Read.Open
public import Proof.go_etcd_io.bbolt.Read.WCtx
public import Proof.go_etcd_io.bbolt.internal.common.Lemmas.Layout

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section orec
variable [GooseExts]

/-- **The record `openBucket` makes** on the value `cv` (source `vsr`) of a nested bucket, in the
transaction `tx`: its header the value's (`ibOf`), no root node, empty caches and nodes; an inline
bucket's page right after the header, view bytes (`vsr` the view's, aligned) or persistent heap
bytes (a clone, or a persistent value); a stored bucket's page nil. -/
def openedRec (tx : Loc) (cv : List w8) (vsr : Src) (C : BRec) : Prop :=
  C.ib = ibOf cv ∧ C.bv.tx' = tx ∧ C.bv.rootNode' = null ∧ C.nm = ∅ ∧ C.bm = ∅ ∧ C.ns = ∅ ∧
  (inBucketRoot cv = 0 →
    C.bv.page' ≠ null ∧ C.ipg = inlinePage cv ∧
    ((vsr = Src.view ∧ C.isrc = Src.view ∧ C.pst = PageSt.view) ∨
      (C.isrc = Src.own DFrac.discard ∧ C.pst = PageSt.none))) ∧
  (inBucketRoot cv ≠ 0 → C.bv.page' = null ∧ C.pst = PageSt.none)

end orec

section acc
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The writer's `writable` field**, out of `wtxW` and back. -/
theorem wtxW_writable_acc (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) :
    wtxW (GF := GF) K tx r m X ⊢ tx.[Tx, go!"writable"] ↦ X.t.t.writable' ∗
      (tx.[Tx, go!"writable"] ↦ X.t.t.writable' -∗ wtxW K tx r m X) := by
  unfold wtxW wtxCore wtxHeap txFields
  iintro ⟨⟨Hpkg, Hcore, %Hr, Hreg, ⟨%Hok, ⟨Hw, Hf⟩, Hroot, Hobjs, Hbobjs⟩, Hfills, Hbk, Hnl, Hdb,
    Hview, Hst⟩, Hcells, Hmap⟩
  iframe Hw
  iintro Hw
  iframe
  ipureintro; exact ⟨Hr, Hok⟩

/-- The writer's heap facts, read out of `wtxW`. -/
theorem wtxW_heapOK' (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) :
    wtxW (GF := GF) K tx r m X ⊢ wtxW K tx r m X ∗ ⌜heapOK (GF := GF) tx X⌝ := by
  unfold wtxW wtxCore wtxHeap
  iintro ⟨⟨Hpkg, Hcore, %Hr, Hreg, ⟨%Hok, Hh⟩, Hrest⟩, Hcells, Hmap⟩
  iframe
  ipureintro; exact ⟨⟨Hr, Hok⟩, Hok⟩

/-- **A bucket's `tx` field**, out of `wtxW` and back (owned or persistent). -/
theorem wtxW_bkt_tx_acc (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (bl : Loc) (B : BRec)
    (hb : X.t.bs !! bl = some B) :
    wtxW (GF := GF) K tx r m X ⊢ ∃ dq : DFrac, bl.[Bucket, go!"tx"] ↦{dq} tx ∗
      (bl.[Bucket, go!"tx"] ↦{dq} tx -∗ wtxW K tx r m X) := by
  iintro Hw
  icases wtxW_heapOK' K tx r m X $$ Hw with ⟨Hw, %Hok⟩
  have htx : B.bv.tx' = tx := Hok.2.2.1 bl B hb
  icases wtxW_bkt_acc K tx r m X bl B hb $$ Hw with ⟨Ho, Hback⟩
  isimp only [objOwn] at Ho
  icases Ho with ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, H10⟩
  by_cases hr : bl = B.bv.tx'.[Tx, go!"root"]
  · rw [if_pos hr]
    iexists (DFrac.own 1)
    rw [htx]
    iframe H2
    iintro H2
    iapply Hback
    isimp only [objOwn]
    rw [if_pos hr, htx]
    iframe
  · rw [if_neg hr]
    iexists DFrac.discard
    rw [htx]
    iframe H2
    iintro H2
    iapply Hback
    isimp only [objOwn]
    rw [if_neg hr, htx]
    iframe

omit hos in
/-- Two points-tos of one `w64` field: their fractions are valid together. -/
theorem w64Pt_valid2 (l : Loc) (a b : w64) (dq1 dq2 : DFrac) :
    l ↦{dq1} a ∗ l ↦{dq2} b ⊢ (⌜✓ (dq1 • dq2)⌝ : IProp GF) := by
  iintro ⟨H1, H2⟩
  icases (persistent_entails_left (typedPointsto_pos _ _ _)) $$ H1 with ⟨H1, %Hp⟩
  have ha : (encode a).length = 8 := ByteEncoding.encode_length a
  have hb : (encode b).length = 8 := ByteEncoding.encode_length b
  obtain ⟨xa, ra, hea⟩ : ∃ x r, encode a = x :: r := by
    cases h : encode a with
    | nil => rw [h] at ha; simp at ha
    | cons x r => exact ⟨x, r, rfl⟩
  obtain ⟨xb, rb, heb⟩ : ∃ x r, encode b = x :: r := by
    cases h : encode b with
    | nil => rw [h] at hb; simp at hb
    | cons x r => exact ⟨x, r, rfl⟩
  have h1 := (typedPointsto_bytes (GF := GF) l a dq1 Hp).1
  have h2 := (typedPointsto_bytes (GF := GF) l b dq2 Hp).1
  rw [hea] at h1; rw [heb] at h2
  simp only [bytesPointsto] at h1 h2
  icases h1 $$ H1 with H1
  icases h2 $$ H2 with H2
  icases H1 with ⟨H1, -⟩
  icases H2 with ⟨H2, -⟩
  icombine H1 H2 gives %h
  ipureintro; exact h.1

omit hos in
/-- Two points-tos of one pointer field: their fractions are valid together. -/
theorem locPt_valid2' (l : Loc) (v1 v2 : Loc) (dq1 dq2 : DFrac) :
    l ↦{dq1} v1 ∗ l ↦{dq2} v2 ⊢ (⌜✓ (dq1 • dq2)⌝ : IProp GF) := by
  iintro ⟨H1, H2⟩
  ihave H1 := typedPointsto_split l v1 dq1 $$ H1
  ihave H2 := typedPointsto_split l v2 dq2 $$ H2
  rw [typedPointstoDef_heap]
  rw [typedPointstoDef_heap]
  icombine H1 H2 gives %h
  ipureintro; exact h.1

/-- **A bucket whose `FillPercent` one owns is no handle and not the root bucket** (the writer's
heap holds theirs whole). -/
theorem wtxW_fill_fresh (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (c : Loc) (f : w64) :
    wtxW (GF := GF) K tx r m X ∗ c.[Bucket, go!"FillPercent"] ↦ f ⊢
      wtxW K tx r m X ∗ c.[Bucket, go!"FillPercent"] ↦ f ∗
        ⌜X.handles !! c = none ∧ c ≠ txRoot (GF := GF) tx⌝ := by
  unfold wtxW wtxCore wtxHeap fills
  iintro ⟨⟨⟨Hpkg, Hcore, %Hr, Hreg, ⟨%Hok, Hf, Hroot, Hobjs, Hbobjs⟩, Hfills, Hbk,
    Hnl, Hdb, Hview, Hst⟩, Hcells, Hmap⟩, Hc⟩
  have hroot : c ≠ txRoot (GF := GF) tx ∨ c = txRoot (GF := GF) tx := by
    by_cases h : c = txRoot (GF := GF) tx
    · exact Or.inr h
    · exact Or.inl h
  rcases hroot with hroot | hroot
  · cases hh : X.handles !! c with
    | none =>
      iframe
      ipureintro; exact ⟨⟨Hr, Hok⟩, rfl, hroot⟩
    | some x =>
      icases (BigSepM.bigSepM_lookup_acc hh).1 $$ Hfills with ⟨⟨%f1, -, Hf1⟩, -⟩
      ihave %Hv := w64Pt_valid2 _ _ _ _ _ $$ [Hf1 Hc]
      · iframe
      exfalso
      exact absurd Hv (dfrac_own_one_op_invalid _)
  · unfold txRoot at hroot
    rw [hroot]
    iunfold rootFill at Hroot
    icases Hroot with ⟨%f0, -, Hroot⟩
    ihave %Hv := w64Pt_valid2 _ _ _ _ _ $$ [Hroot Hc]
    · iframe
    exfalso
    exact absurd Hv (dfrac_own_one_op_invalid _)

/-- **A bucket whose `InBucket` field one owns is no bucket of the writer's heap.** -/
theorem wtxW_bkt_fresh (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (c p : Loc) :
    wtxW (GF := GF) K tx r m X ∗ c.[Bucket, go!"InBucket"] ↦ p ⊢
      wtxW K tx r m X ∗ c.[Bucket, go!"InBucket"] ↦ p ∗ ⌜X.t.bobjs !! c = none⌝ := by
  unfold wtxW wtxCore wtxHeap
  iintro ⟨⟨⟨Hpkg, Hcore, %Hr, Hreg, ⟨%Hok, Hf, Hroot, Hobjs, Hbobjs⟩, Hfills, Hbk,
    Hnl, Hdb, Hview, Hst⟩, Hcells, Hmap⟩, Hc⟩
  cases hh : X.t.bobjs !! c with
  | none =>
    iframe
    ipureintro; exact ⟨⟨Hr, Hok⟩, rfl⟩
  | some B =>
    icases (BigSepM.bigSepM_lookup_acc hh).1 $$ Hbobjs with ⟨Ho, -⟩
    isimp only [objOwn] at Ho
    icases Ho with ⟨H1, -⟩
    ihave %Hv := locPt_valid2' _ _ _ _ _ $$ [H1 Hc]
    · iframe
    exfalso
    exact absurd Hv (dfrac_own_one_op_invalid _)

end acc

section hdr
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **The header of a nested bucket's value**, typed, from a live source (persistent bytes, or the
view's through the writer's cells), and back. -/
theorem wtxW_src_hdr (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (value : GoSlice)
    (vsr : Src) (cv : List w8) (hvs : vsr ≠ Src.stale) (h16 : 16 ≤ cv.length) :
    wtxW (GF := GF) K tx r m X ∗ srcOwn X.v value vsr cv ⊢ ∃ dq : DFrac,
      value.ptr ↦{dq} inBucketOf cv ∗ (value.ptr ↦{dq} inBucketOf cv -∗ wtxW K tx r m X) := by
  have hdec : (decode (List.take 16 (List.drop 0 cv)) : InBucket) = inBucketOf cv := by
    unfold inBucketOf bytesAt; simp only [List.drop_zero]
  cases vsr with
  | stale => exact absurd rfl hvs
  | own d =>
    unfold srcOwn
    iintro ⟨Hw, #Hs⟩
    have hne : cv ≠ [] := by intro h; simp [h] at h16
    ihave %Hp := ownSlice_ptr_pos value cv DFrac.discard hne $$ Hs
    icases ownSlice_bytes_acc go.uint8 (.scalar _ _ .isPlainScalar_uint8) value cv DFrac.discard Hp
      $$ Hs with ⟨Hb, -⟩
    rw [flatMap_encode_w8]
    icases bytesPointsto_view_read (V := InBucket) value.ptr DFrac.discard cv 0 value.ptr (by simp)
      (by omega) Hp $$ Hb with ⟨Hib, -⟩
    rw [hdec]
    iexists DFrac.discard
    iframe Hib
    iintro -
    iexact Hw
  | view =>
    unfold srcOwn
    iintro ⟨Hw, %Hin⟩
    obtain ⟨hl, -, -, -⟩ := Hin
    have hh := inViewLoc_sub X.v value.ptr cv hl 0 16 (by omega)
    rw [show ((0 : Nat) : Int) = 0 from rfl, show value.ptr +ₗ (0 : Int) = value.ptr by simp] at hh
    icases wtxW_cells_acc K tx r m X $$ Hw with ⟨%Hbase, Hc, Hwb⟩
    icases viewCells_loc_acc wq X.v value.ptr _ hh $$ Hc with ⟨%dqh, Hb, Hcb⟩
    have hlen : (bytesAt cv 0 16).length = 16 := by unfold bytesAt; simp; omega
    icases Read.bytesPointsto_bounds value.ptr dqh (bytesAt cv 0 16)
      (by intro h; simp [h] at hlen) $$ Hb with ⟨Hb, %Hbd⟩
    icases bytesPointsto_view_read (V := InBucket) value.ptr dqh (bytesAt cv 0 16) 0 value.ptr
      (by simp) (by omega) Hbd.1 $$ Hb with ⟨Hib, Hback⟩
    rw [show (decode (List.take 16 (List.drop 0 (bytesAt cv 0 16))) : InBucket) = inBucketOf cv by
      unfold inBucketOf bytesAt; simp only [List.drop_zero, List.take_take, Nat.min_self]]
    iexists dqh
    iframe Hib
    iintro Hib
    ihave Hb := Hback $$ Hib
    ihave Hc := Hcb $$ Hb
    iapply Hwb $$ Hc

/-- An inline bucket value's page, from the view. -/
theorem src_inl_view (v : View) (value : GoSlice) (cv : List w8) (h16 : 16 ≤ cv.length) :
    srcOwn (GF := GF) v value Src.view cv ⊢ ⌜inViewLoc v (value.ptr +ₗ (16 : Int)) (inlinePage cv)⌝ := by
  unfold srcOwn
  iintro %Hin
  ipureintro
  obtain ⟨hl, -, -, -⟩ := Hin
  have hi := inViewLoc_sub v value.ptr cv hl 16 (cv.length - 16) (by omega)
  rw [bytesAt_drop cv 16 h16] at hi
  exact hi

/-- An inline bucket value's page, from persistent bytes. -/
theorem src_inl_own (v : View) (value : GoSlice) (d : DFrac) (cv : List w8) (h16 : 16 ≤ cv.length) :
    srcOwn (GF := GF) v value (Src.own d) cv ⊢
      bytesPointsto (value.ptr +ₗ (16 : Int)) DFrac.discard (inlinePage cv) := by
  have hl : (inlinePage cv).length = cv.length - 16 := by unfold inlinePage bucketHeaderSize; simp
  have hne : cv ≠ [] := by intro h; simp [h] at h16
  unfold srcOwn
  iintro #Hs
  ihave %Hp := ownSlice_ptr_pos value cv DFrac.discard hne $$ Hs
  icases ownSlice_bytes_acc go.uint8 (.scalar _ _ .isPlainScalar_uint8) value cv DFrac.discard Hp
    $$ Hs with ⟨Hb, -⟩
  rw [flatMap_encode_w8]
  icases Read.bytesPointsto_sub_acc value.ptr DFrac.discard cv (inlinePage cv) 16 (by rw [hl]; omega)
    (by rw [hl, bytesAt_drop cv 16 h16]; rfl) $$ Hb with ⟨Hi, -⟩
  iexact Hi

end hdr

end bbolt
end EtcdGrove
end Perennial
