/-
Proof of `Spec/go_etcd_io/etcd/pkg/v3/adt/NewBytesAffinePoint.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.adt.NewBytesAffinePoint
public import Spec.go_etcd_io.etcd.pkg.v3.adt.NewBytesAffineInterval

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.pkg.v3.adt

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.adt.Assumptions]

theorem adt.NewBytesAffinePoint.wp_proof (h_NewBytesAffineInterval :
      adt.NewBytesAffineInterval.spec (GF := GF) (hG := hG)) :
    adt.NewBytesAffinePoint.spec (GF := GF) (hG := hG) := by
  intro b bs dq
  wp_start as ⟨Hb, %Hlen⟩
  ihave %Hbl := ownSlice_len _ _ _ $$ Hb
  wp_auto
  wp_apply wp_slice_make2 (V := w8) (b.len + W64 1) $$ [] as %be ⟨Hbe, -⟩
  · ipureintro; word
  have h1 : sint.nat (b.len + W64 1) = bs.length + 1 := by
    rw [Hbl.1]; unfold sint.nat; word
  have hz : (zero_val w8) = W8 0 := rfl
  rw [hz, h1]
  wp_apply wp_slice_copy be (List.replicate (bs.length + 1) (W8 0)) b bs dq $$ [$Hbe $Hb]
    as %n ⟨%Hn, Hbe, Hb⟩
  have hrep : List.take (List.replicate (bs.length + 1) (W8 0)).length bs ++
      List.drop bs.length (List.replicate (bs.length + 1) (W8 0)) = bs ++ [W8 0] := by
    rw [List.length_replicate, List.take_of_length_le (by omega), List.drop_replicate]
    simp
  rw [hrep]
  ihave %Hbel := ownSlice_len _ _ _ $$ Hbe
  have Hbnd : 0 ≤ sint.Z b.len ∧ sint.Z b.len < sint.Z be.len := by
    simp only [List.length_append, List.length_singleton] at Hbel
    constructor
    · exact Hbl.2
    · have : (bs.length : Int) = sint.Z b.len := by rw [Hbl.1]; word
      word
  simp only [Hbnd, and_self, ite_true]
  wp_apply wp_store_slice_index (V := w8) (t := go.byte) be _ (bs ++ [W8 0]) (W8 0) $$ [$Hbe] as Hbe
  · ipureintro
    simp only [List.length_append, List.length_singleton]
    have : (bs.length : Int) = sint.Z b.len := by rw [Hbl.1]; word
    omega
  wp_apply h_NewBytesAffineInterval
  iapply HΦ
  iframe Hb
  have hset : (bs ++ [W8 0]).set (sint.Z b.len).toNat (W8 0) = bs ++ [W8 0] := by
    have : (sint.Z b.len).toNat = bs.length := by rw [Hbl.1]
    rw [this]; simp
  rw [hset]; iexact Hbe

end proof

end EtcdGrove
end Perennial
