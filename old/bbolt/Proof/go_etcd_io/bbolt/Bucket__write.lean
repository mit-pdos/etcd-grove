module
public import Spec.go_etcd_io.bbolt.Bucket__write
public import Spec.go_etcd_io.bbolt.node__size
public import Spec.go_etcd_io.bbolt.node__write
public import Proof.go_etcd_io.bbolt.BucketOpen

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem leInt_zeros (n : Nat) : leInt (List.replicate n (0 : w8)) = 0 := by
  induction n with
  | zero => simp [leInt]
  | succ n ih => rw [List.replicate_succ, leInt_cons, ih]; simp

theorem leAt_zeros (n off k : Nat) : leAt (List.replicate n (0 : w8)) off k = 0 := by
  unfold leAt; rw [List.drop_replicate, List.take_replicate, leInt_zeros]; rfl

theorem inBucketBytes_length (b : InBucket) : (inBucketBytes b).length = 16 := by
  unfold inBucketBytes; simp [leBytes_length']

theorem pageBytes_length (p : Page) : (pageBytes p).length = 16 := by
  unfold pageBytes; simp [leBytes_length']

end lemmas

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem Bucket.write.wp_proof (hSize : node.size.spec (GF := GF) (hG := hG))
    (hWrite : node.write.spec (GF := GF) (hG := hG)) :
    Bucket.write.spec (GF := GF) (hG := hG) := by
  intro bl bv dqb ib dqi nv dqn ins dqs ks vs q Hn Hks Hvs Hkpos Hbig Hsz Hpg
  wp_start as ⟨Hb, Hib, Hn, Hins, Hdata⟩
  wp_auto
  wp_apply hSize $$ [Hn Hins] as ⟨Hn, Hins⟩
  · iframe
  try wp_auto
  rw [Hsz]
  have HL : (16 + 16 * ins.length + kvLen ks vs ins.length) + 16 < 2 ^ 63 := by omega
  have HN : W64 16 + W64 ((16 + 16 * ins.length + kvLen ks vs ins.length : Nat) : Int) =
      W64 ((32 + 16 * ins.length + kvLen ks vs ins.length : Nat) : Int) := by
    apply BitVec.eq_of_toNat_eq; simp; omega
  rw [HN]
  have HsN : sint.nat (W64 ((32 + 16 * ins.length + kvLen ks vs ins.length : Nat) : Int)) =
      32 + 16 * ins.length + kvLen ks vs ins.length := by
    unfold sint.nat; word
  wp_apply wp_slice_make2 (V := w8) (W64 ((32 + 16 * ins.length + kvLen ks vs ins.length : Nat) : Int))
    $$ [] as %val ⟨Hval, Hcap⟩
  · ipureintro; word
  rw [HsN]
  try wp_auto
  have Hne : List.replicate (32 + 16 * ins.length + kvLen ks vs ins.length) (zero_val w8) ≠ [] := by
    simp
  icases slice_car_keep val _ (DFrac.own 1) Hne $$ Hval with ⟨%Hcar, Hval⟩
  icases (ownSlice_bytes val _ (DFrac.own 1) Hne).1 $$ Hval with ⟨Hbs, %Hsl⟩
  have HlenZ : sint.Z val.len = ((32 + 16 * ins.length + kvLen ks vs ins.length : Nat) : Int) := by
    have := Hsl.1; simp only [List.length_replicate] at this; omega
  have Hlen0 : 0 < sint.Z val.len := by omega
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, Hlen0⟩)]
  unfold sliceIndexRef
  rw [show sint.Z (W64 0) = 0 by rfl, arrayIndexRef_zero]
  icases (value_inbucket (hG := hG) val.ptr (DFrac.own 1) _ (by simp; omega) Hcar).1 $$ Hbs
    with ⟨Hzib, Hrest⟩
  try wp_auto
  have H16l : 16 < sint.Z val.len := by omega
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, H16l⟩)]
  unfold sliceIndexRef
  rw [arrayIndexRef_w8 (hG := hG) val.ptr _ Hcar, show sint.Z (W64 16) = (16 : Int) from rfl]
  have Hc16 : (val.ptr +ₗ (16 : Int)).locCar ≠ 0 := by simpa [Loc.add] using Hcar
  icases (page_header_bytes (hG := hG) (val.ptr +ₗ (16 : Int)) (DFrac.own 1) _ (by simp; omega) Hc16).1 $$ Hrest
    with ⟨Hhd, Hrest⟩
  try wp_auto
  rw [List.drop_replicate, List.drop_replicate] at *
  have Hz : ∀ off k, leAt (List.replicate (32 + 16 * ins.length + kvLen ks vs ins.length - 16) (zero_val w8)) off k = 0 :=
    fun off k => leAt_zeros _ off k
  have Hhdr : pageOf (List.replicate (32 + 16 * ins.length + kvLen ks vs ins.length - 16) (zero_val w8)) =
      Page.mk (W64 0) (W16 0) (W16 0) (W32 0) := by
    unfold pageOf pageId pageFlags pageCount pageOverflow; rw [Hz, Hz, Hz, Hz]; rfl
  rw [Hhdr]
  wp_apply hWrite bv.rootNode' nv dqn ins dqs ks vs q (val.ptr +ₗ (16 : Int)) (Page.mk (W64 0) (W16 0) (W16 0) (W32 0))
    (List.replicate (32 + 16 * ins.length + kvLen ks vs ins.length - 16 - 16) (zero_val w8)) Hc16 rfl rfl Hn Hks Hvs
    Hkpos Hbig (by simp; omega) Hpg $$ [Hn Hins Hdata Hhd Hrest] as ⟨Hn, Hins, Hdata, Hhd, Hrest⟩
  · iframe
  try wp_auto
  rw [List.drop_replicate, show 32 + 16 * ins.length + kvLen ks vs ins.length - 16 - 16 -
    (16 * ins.length + kvLen ks vs ins.length) = 0 by omega, List.replicate_zero, List.append_nil]
  icases (InBucket_bytes (hG := hG) val.ptr ib (DFrac.own 1) Hcar).1 $$ Hzib with Hb1
  ihave Hb2 := (Page_bytes (hG := hG) (val.ptr +ₗ (16 : Int)) _ (DFrac.own 1) Hc16).1 $$ Hhd
  isimp only at Hb2
  ihave Hall : bytesPointsto (GF := GF) val.ptr (DFrac.own 1) (writtenBucket ib nv.isLeaf' ks vs ins)
    $$ [Hb1 Hb2 Hrest]
  · unfold writtenBucket
    simp only [List.append_assoc]
    iapply (bytesPointsto_app val.ptr (DFrac.own 1) (inBucketBytes ib) _).2
    rw [inBucketBytes_length, show ((16 : Nat) : Int) = 16 from rfl]
    iframe Hb1
    iapply (bytesPointsto_app (val.ptr +ₗ 16) (DFrac.own 1) (pageBytes (writtenHdr nv.isLeaf' ins.length)) _).2
    rw [pageBytes_length, show ((16 : Nat) : Int) = 16 from rfl]
    unfold writtenHdr
    iframe
  have Hwl : (writtenBucket ib nv.isLeaf' ks vs ins).length = 32 + 16 * ins.length + kvLen ks vs ins.length := by
    unfold writtenBucket
    simp only [List.length_append, inBucketBytes_length, pageBytes_length]
    rw [writtenElems_eq, writtenUpTo_length, kvBytes_eq ks vs ins.length Hks Hvs,
      kvUpTo_length _ _ _ (by omega) (by omega)]
    try omega
  have Hwne : writtenBucket ib nv.isLeaf' ks vs ins ≠ [] := by
    intro h; have := congrArg List.length h; rw [Hwl] at this; simp at this
  ihave Hval := (ownSlice_bytes val _ (DFrac.own 1) Hwne).2 $$ [Hall]
  · iframe; ipureintro; exact ⟨by rw [Hwl, HlenZ], Hsl.2⟩
  iapply HΦ
  iframe

end proof

end bbolt
end EtcdGrove
end Perennial
