/- Lean-first (no Rocq counterpart).

`b.set(pos)`: one load and one store of word `pos / 64`.
-/
module

public import Spec.github_com.anishathalye.porcupine.bitset__set
public import Spec.github_com.anishathalye.porcupine.bitsetIndex

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace porcupine

open Iris Iris.BI Iris.ProofMode github_com.anishathalye.porcupine

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]

theorem bitset.set.wp_proof (wp_bitsetIndex : bitsetIndex.spec (GF := GF) (hG := hG)) :
    bitset.set.spec (GF := GF) (hG := hG) := fun b ws pos hpos => by
  wp_start as Hb
  wp_auto
  wp_apply wp_bitsetIndex
  ihave %Hlen := ownSlice_len $$ Hb
  have hidx : sint.Z (pos / W64 64) = (uint.nat pos / 64 : Nat) := by word
  have Hb' : 0 ≤ sint.Z (pos / W64 64) ∧ sint.Z (pos / W64 64) < sint.Z b.len := by word
  simp only [Hb', and_self, ↓reduceIte]
  wp_auto
  simp only [Hb', and_self, ↓reduceIte]
  list_elem ws (uint.nat pos / 64) as w
  wp_apply wp_load_slice_index b (sint.Z (pos / W64 64)) ws _ w (by word) $$ [Hb] with Hb
  · iframe; ipureintro; rw [hidx]; simpa only [Int.toNat_natCast] using Hw_lookup
  wp_load
  wp_pures
  wp_apply wp_store_slice_index $$ [Hb] as Hb
  · iframe; ipureintro; word
  wp_auto
  rw [hidx, Int.toNat_natCast]
  have hw : ws.getD (uint.nat pos / 64) 0 = w := by
    simp [List.getD_eq_getElem?_getD, Hw_lookup]
  iapply HΦ
  unfold bsSet
  rw [hw]
  iexact Hb

end proof

end porcupine
end EtcdGrove
end Perennial
