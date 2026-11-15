/-
The proof of `Spec/go_etcd_io/bbolt/Bucket__write.lean` (U9b, `notes/bbolt-proof-plan.md`): the
bucket header over the first 16 bytes of a new zeroed slice, then the root node written as a page
after it (`node.write`), as Perennial's `unsafememory/writeInlineBucket`.
-/
module

public import Spec.go_etcd_io.bbolt.Bucket__write
public import Spec.go_etcd_io.bbolt.node__size
public import Spec.go_etcd_io.bbolt.node__write
public import Proof.go_etcd_io.bbolt.internal.common.Lemmas.Layout
public import Proof.go_etcd_io.bbolt.internal.common.Lemmas.Bytes

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

theorem decode_zero_page [GooseExts] :
    (decode (List.replicate 16 (0 : w8)) : Page) = ⟨W64 0, W16 0, W16 0, W32 0⟩ :=
  rfl

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

omit hos in
theorem Bucket.write.wp_proof (hSize : node.size.spec (GF := GF) (hG := hG))
    (hWrite : node.write.spec (GF := GF) (hG := hG)) :
    Bucket.write.spec (GF := GF) (hG := hG) := by
  intro b ibp ib n nv ins ms dqb dq dqi qk qv Hleaf Hlen Hfit Hsz Hsz31
  wp_start as ⟨Hib, Hibp, Hrn, Hn, Hins, Hd⟩
  wp_auto
  wp_apply hSize n nv ins dq dqi $$ [Hn Hins] as ⟨Hn, Hins⟩
  · iframe
  try wp_auto
  generalize hL : (pageBody true ms).length = L at *
  rw [Hsz]
  try simp only [internal.common.BucketHeaderSize]
  rw [show W64 16 + W64 ((16 + L : Nat) : Int) = W64 ((32 + L : Nat) : Int) by push_cast; word]
  have hNZ : sint.Z (W64 ((32 + L : Nat) : Int)) = ((32 + L : Nat) : Int) :=
    sint_Z_W64_nat _ (by omega)
  wp_apply wp_slice_make2 (V := w8) $$ [] as %val ⟨Hv, Hcap⟩
  · ipureintro; rw [hNZ]; omega
  rw [show sint.nat (W64 ((32 + L : Nat) : Int)) = 32 + L by simp only [sint.nat, hNZ]; omega]
  ihave %Hvl := ownSlice_len _ _ _ $$ Hv
  ihave %Hvp := ownSlice_ptr_pos _ _ _ (by simp) $$ Hv
  icases ownSlice_bytes_acc go.uint8 (.scalar _ _ .isPlainScalar_uint8) _ _ _ Hvp $$ Hv
    with ⟨Hbytes, Hback⟩
  rw [flatMap_encode_w8, show (zero_val w8 : w8) = 0 from rfl]
  have hvlen : sint.Z val.len = ((32 + L : Nat) : Int) :=
    internal.common.sint_Z_eq_of_sint_nat _ _ (by simpa using Hvl.1) Hvl.2
  ihave %Hbnd := internal.common.bytesPointsto_in_bounds _ _ _ (by simp) $$ Hbytes
  simp only [hvlen, show sint.Z (W64 0) = 0 from rfl,
    show (0 : Int) ≤ 0 ∧ (0 : Int) < ((32 + L : Nat) : Int) from ⟨Int.le_refl _, by omega⟩]
  rw [show sliceIndexRef w8 0 val = val.ptr by rw [sliceIndexRef_byte _ _ Hvp (Int.le_refl _)]; simp]
  rw [show List.replicate (32 + L) (0 : w8) = List.replicate 16 0 ++ (List.replicate 16 0 ++
    List.replicate L 0) by
      rw [List.replicate_append_replicate, List.replicate_append_replicate]; congr 1; omega]
  icases (bytesPointsto_app _ _ _ _).1 $$ Hbytes with ⟨Hh0, Hbytes⟩
  icases (bytesPointsto_app _ _ _ _).1 $$ Hbytes with ⟨Hh1, Hbytes⟩
  icases (bytesPointsto_typed (V := InBucket) _ _ _ (by simp) Hvp).1 $$ Hh0 with Hh0
  rw [List.length_replicate] at *
  have hp16 : 0 < (val.ptr +ₗ ((16 : Nat) : Int)).addr := by simp [Loc.add]; omega
  icases (bytesPointsto_typed (V := Page) _ _ _ (by simp) hp16).1 $$ Hh1 with Hh1
  wp_auto
  simp only [hvlen, show sint.Z (W64 16) = 16 from rfl,
    show (0 : Int) ≤ 16 ∧ (16 : Int) < ((32 + L : Nat) : Int) from ⟨by decide, by omega⟩]
  rw [show sliceIndexRef w8 16 val = val.ptr +ₗ ((16 : Nat) : Int) by
    rw [sliceIndexRef_byte _ _ Hvp (by decide)]; rfl]
  wp_auto
  rw [decode_zero_page]
  rw [show ((16 : Nat) : Int) = 16 from rfl]
  wp_apply hWrite n nv ins ms dq dqi qk qv (val.ptr +ₗ 16) ⟨W64 0, W16 0, W16 0, W32 0⟩ L rfl rfl
      Hlen Hfit (by omega) (by rw [Hleaf]; intro h; cases h) (by simpa [Loc.add] using hp16)
      (by simp [Loc.add] at Hbnd ⊢; omega)
      $$ [Hn Hins Hd Hh1 Hbytes] as ⟨Hn, Hins, Hd, Hh1, Hbytes⟩
  · iframe
  try wp_auto
  rw [Hleaf, hL, Nat.sub_self, List.replicate_zero, List.append_nil]
  icases (typedPointsto_bytes (V := InBucket) _ _ _ Hvp).1 $$ Hh0 with Hh0
  icases (typedPointsto_bytes (V := Page) _ _ _ (by simpa using hp16)).1 $$ Hh1 with Hh1
  iapply HΦ
  iframe
  iapply Hback
  · ipureintro; simp [ByteEncoding.encode_length, hL]; omega
  rw [flatMap_encode_w8, List.append_assoc]
  iapply (bytesPointsto_app _ _ _ _).2
  iframe Hh0
  iapply (bytesPointsto_app _ _ _ _).2
  rw [ByteEncoding.encode_length, ByteEncoding.encode_length,
    show ((16 : Nat) : Int) = 16 from rfl]
  iframe

end proof

end bbolt
end EtcdGrove
end Perennial
