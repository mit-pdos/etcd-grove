/-
The read path's (U6, `notes/bbolt-proof-plan.md`) opened buckets: a nested bucket's value, from a
live source, gives the parts of a reader bucket (`rBkt`) `openBucket` points into it: its header
at the value's start (persistent bytes or the view's), its inline page after the header.
-/
module

public import Proof.go_etcd_io.bbolt.Read.Src

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section open_
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

omit [GooseExts] in
theorem bytesAt_drop (bs : List w8) (off : Nat) (h : off ≤ bs.length) :
    bytesAt bs off (bs.length - off) = bs.drop off := by
  unfold bytesAt; rw [List.take_of_length_le (by simp)]

/-- The header and inline-page parts of a reader bucket opened on the value `cv` at `p`. -/
def openParts (v : View) (p : Loc) (cv : List w8) : IProp GF :=
  iprop(((∃ ib : InBucket, p ↦□ ib ∗ ⌜ib.root' = (inBucketOf cv).root'⌝) ∨
      ⌜inViewLoc v p (bytesAt cv 0 16)⌝) ∗ locOwn v (p +ₗ (16 : Int)) (inlinePage cv))

instance openParts_persistent (v : View) (p : Loc) (cv : List w8) :
    Persistent (openParts (GF := GF) v p cv) := by
  unfold openParts locOwn; infer_instance

/-- **Persistent bytes of a value give an opened bucket's parts.** -/
theorem bytes_openParts (v : View) (p : Loc) (cv : List w8) (h16 : 16 ≤ cv.length)
    (hp : 0 < p.addr) :
    bytesPointsto (GF := GF) p DFrac.discard cv ⊢ openParts v p cv := by
  iintro #Hb
  unfold openParts locOwn
  isplitl
  · ileft
    icases bytesPointsto_view_read (V := InBucket) p DFrac.discard cv 0 p (by simp) (by omega) hp
      $$ Hb with ⟨Hib, -⟩
    iexists (decode ((cv.drop 0).take 16) : InBucket)
    iframe Hib
    ipureintro; rfl
  · iright
    have hl : (inlinePage cv).length = cv.length - 16 := by unfold inlinePage bucketHeaderSize; simp
    icases Read.bytesPointsto_sub_acc p DFrac.discard cv (inlinePage cv) 16 (by rw [hl]; omega)
      (by rw [hl, bytesAt_drop cv 16 h16]; rfl) $$ Hb with ⟨Hi, -⟩
    iexact Hi

/-- **A value from a live source gives an opened bucket's parts** (the view's base mapped). -/
theorem src_openParts (v : View) (hb : 0 < v.base.addr) (value : GoSlice) (sr : Src)
    (cv : List w8) (hs : sr ≠ Src.stale) (h16 : 16 ≤ cv.length) :
    srcOwn (GF := GF) v value sr cv ⊢ openParts v value.ptr cv ∗ ⌜0 < value.ptr.addr⌝ := by
  cases sr with
  | stale => exact absurd rfl hs
  | own d =>
    unfold srcOwn
    iintro #Hs
    have hne : cv ≠ [] := by intro h; simp [h] at h16
    ihave %Hp := ownSlice_ptr_pos value cv DFrac.discard hne $$ Hs
    icases ownSlice_bytes_acc go.uint8 (.scalar _ _ .isPlainScalar_uint8) value cv DFrac.discard Hp
      $$ Hs with ⟨Hb, -⟩
    rw [flatMap_encode_w8]
    ihave #Hb := persistently_intro $$ Hb
    isplitl
    · iapply bytes_openParts v value.ptr cv h16 Hp
      iexact Hb
    · ipureintro; exact Hp
  | view =>
    unfold srcOwn
    iintro %Hin
    obtain ⟨hl, hlen, -, -⟩ := Hin
    have hp : 0 < value.ptr.addr := by
      obtain ⟨id, pg, off, -, -, -, hq⟩ := hl
      rw [hq]; simp [Loc.add]; omega
    have hh := inViewLoc_sub v value.ptr cv hl 0 16 (by omega)
    have hi := inViewLoc_sub v value.ptr cv hl 16 (cv.length - 16) (by omega)
    rw [bytesAt_drop cv 16 h16] at hi
    rw [show ((0 : Nat) : Int) = 0 from rfl, show value.ptr +ₗ (0 : Int) = value.ptr by simp] at hh
    rw [show ((16 : Nat) : Int) = 16 from rfl] at hi
    unfold openParts locOwn
    isplitl
    · isplitl
      · iright; ipureintro; exact hh
      · ileft; ipureintro; exact hi
    · ipureintro; exact hp

/-- **The reader's `writable` field** (`false`), out of `rdTxK` and back. -/
theorem rdTxK_writable_acc (K : BC) (tx : Loc) (src : PairSrc) (q : Qp) (T : TxView) (v : View) :
    rdTxK (GF := GF) K tx src q T v ⊢ ∃ dw, tx.[Tx, go!"writable"] ↦{dw} false ∗
      (tx.[Tx, go!"writable"] ↦{dw} false -∗ rdTxK K tx src q T v) := by
  unfold rdTxK rtxFrac
  iintro ⟨%r, %c, %mv, %k, %Hc, #Hreg, #Hpk, #Hcore, Hv, Hex,
    ⟨%t, Hw, Hm, Hmeta, Hroot, Hfill, Hpages, Hch, Hwf, Hdb, Hmv, Hcells, Hmap, #Hvo, %Hf⟩, Hpool⟩
  iexists _
  iframe Hw
  iintro Hw
  iexists r, c, mv, k
  iframe; iframe #
  isplitr
  · ipureintro; exact Hc
  ipureintro; exact Hf

/-- **The reader's statistics token** (its `ex` share), with its core and registration, out of
`rdTxK` and back (`Bucket.Cursor_i`'s pre). -/
theorem rdTxK_stats_acc (K : BC) (tx : Loc) (src : PairSrc) (q : Qp) (T : TxView) (v : View) :
    rdTxK (GF := GF) K tx src q T v ⊢ ∃ r : TxReg, K.core ∗ reg tx K.B r ∗ statsTok r true q ∗
      (statsTok r true q -∗ rdTxK K tx src q T v) := by
  unfold rdTxK
  iintro ⟨%r, %c, %mv, %k, %Hc, #Hreg, #Hpk, #Hcore, Hv, Hex, Hrt, Hpool⟩
  iexists r
  iframe Hcore Hreg
  unfold statsTok
  simp only [if_true]
  iframe Hex
  iintro Hex
  iexists r, c, mv, k
  iframe; iframe #
  ipureintro; exact Hc

/-- The reader's package initialization. -/
theorem rdTxK_pkgInit (K : BC) (tx : Loc) (src : PairSrc) (q : Qp) (T : TxView) (v : View) :
    rdTxK (GF := GF) K tx src q T v ⊢ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt := by
  unfold rdTxK
  iintro ⟨%r, %c, %mv, %k, -, -, #Hpk, -⟩
  iexact Hpk

end open_

end bbolt
end EtcdGrove
end Perennial
