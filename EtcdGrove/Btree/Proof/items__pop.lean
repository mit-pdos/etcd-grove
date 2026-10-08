import EtcdGrove.Btree.Spec.items__pop
import EtcdGrove.Btree.ListLemmas

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Btree

open Iris Iris.BI Iris.ProofMode github_com.google.btree

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.google.btree.Assumptions]

theorem items.pop.wp_proof : items.pop.spec (GF := GF) (hG := hG) := by
  intro V _ _ T _ s sl vs v Hlast
  wp_start as ⟨Hs, Hsl, Hcap⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  ihave %Hwf := ownSlice_wf _ _ _ $$ Hsl
  have hn : 0 < vs.length := by
    cases vs with
    | nil => simp at Hlast
    | cons _ _ => simp
  have hv : vs[vs.length - 1]? = some v := by
    rw [List.getLast?_eq_getElem?] at Hlast; exact Hlast
  have hi : sint.nat (sl.len - W64 1) = vs.length - 1 := by word
  wp_auto
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
  wp_apply wp_load_slice_index sl (sint.Z (sl.len - W64 1)) vs _ v (by word) $$ [Hsl] as Hsl
  · iframe; ipureintro
    rw [show (sint.Z (sl.len - W64 1)).toNat = sint.nat (sl.len - W64 1) from rfl, hi]; exact hv
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
  wp_apply wp_store_slice_index sl (sint.Z (sl.len - W64 1)) _ (zero_val V) $$ [Hsl] as Hsl
  · iframe; ipureintro; word
  wp_auto
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word, by word⟩)]
  wp_auto
  icases (ownSlice_split_all (sl.len - W64 1) sl _ _ ⟨by word, by word⟩).1 $$ Hsl with ⟨Hsl1, Hsl2⟩
  ihave Hcap := ownSlice_slice_absorb_capacity sl _ (W64 0) (sl.len - W64 1)
    ⟨by decide, by word, by word⟩ $$ [Hsl2 Hcap]
  · iframe
  have htake : (vs.set (sint.Z (sl.len - W64 1)).toNat (zero_val V)).take
      (sint.nat (sl.len - W64 1)) = vs.dropLast := by
    rw [show (sint.Z (sl.len - W64 1)).toNat = sint.nat (sl.len - W64 1) from rfl, hi,
      List.take_set_of_le (Nat.le_refl _), List.dropLast_eq_take]
  rw [htake]
  iapply HΦ
  iframe

end proof

end Btree
end EtcdGrove
end Perennial
