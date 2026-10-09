/-
Proof of `Spec/getPrefix.lean`. Lean-first (no Rocq counterpart).
-/
import EtcdGrove.Cache.Spec.getPrefix

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

theorem getPrefix.wp_proof : getPrefix.spec (GF := GF) (hG := hG) := by
  intro sl key dq
  wp_start as Hsl
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  ihave Hci : (clientv3Init : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hci with ⟨%npe, #Hnpe, #Hnpe_sl⟩
  wp_auto
  wp_apply wp_slice_make2 (V := w8) as %e ⟨He, Hecap⟩
  · ipureintro; exact Hlen.2
  wp_apply wp_slice_copy (V := w8) $$ [$He $Hsl] as %n ⟨%Hn, He, Hsl⟩
  have Hcopy : key.take (List.replicate (sint.nat sl.len) (zero_val w8)).length ++
      (List.replicate (sint.nat sl.len) (zero_val w8)).drop key.length = key := by
    simp [List.length_replicate, ← Hlen.1]
  rw [Hcopy]
  clear Hcopy Hn
  ihave %Helen := ownSlice_len _ _ _ $$ He
  ihave HI : (∃ i : w64, "i" ∷ i_ptr ↦ i ∗
      "%Hi" ∷ ⌜-1 ≤ sint.Z i ∧ sint.Z i < sint.Z e.len ∧
        ∀ j : Nat, sint.Z i < j → ∀ x, key[j]? = some x → x = W8 255⌝ : IProp GF) $$ [i]
  · iexists (e.len - W64 1)
    iframe
    ipureintro
    have h1 : sint.Z (e.len - W64 1) = sint.Z e.len - 1 := by word
    refine ⟨by omega, by omega, ?_⟩
    intro j hj x hx
    have : j < key.length := (List.getElem?_eq_some_iff.1 hx).1
    have : (key.length : Int) = sint.Z e.len := by rw [Helen.1]; word
    omega
  irename «end» => Hend
  wp_for HI
  wp_if_destruct
  · have hi0 : 0 ≤ sint.Z i := by simpa using Hif
    have hilt : sint.nat i < key.length := by rw [Helen.1]; word
    obtain ⟨b, hb⟩ : ∃ b, key[sint.nat i]? = some b :=
      ⟨_, List.getElem?_eq_getElem hilt⟩
    have Hbnd : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z e.len := ⟨hi0, Hi.2.1⟩
    simp only [Hbnd, and_self, ite_true]
    wp_apply wp_load_slice_index e (sint.Z i) key _ b hi0 $$ [He] as He
    · iframe He; ipureintro; exact hb
    wp_if_destruct
    · simp only [Hbnd, and_self, ite_true]
      wp_apply wp_load_slice_index e (sint.Z i) key _ b hi0 $$ [He] as He
      · iframe He; ipureintro; exact hb
      simp only [Hbnd, and_self, ite_true]
      wp_apply wp_store_slice_index (V := w8) (t := go.byte) e _ key (b + W8 1) $$ [$He] as He
      · ipureintro
        have : (key.length : Int) = sint.Z e.len := by rw [Helen.1]; word
        omega
      ihave %Hcapwf := ownSliceCap_wf _ _ $$ Hecap
      have Hi1 : sint.Z (i + W64 1) = sint.Z i + 1 := by word
      have Hsb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (i + W64 1) ∧
          sint.Z (i + W64 1) ≤ sint.Z e.cap := by
        refine ⟨by decide, by word, ?_⟩; omega
      simp only [Hsb, and_self, ite_true]
      icases (ownSlice_slice (W64 0) (i + W64 1) e (DFrac.own 1) _ ⟨by decide, by word, by omega⟩).1
        $$ He with ⟨-, Hout, -⟩
      ipersist Hout
      wp_auto
      wp_for_post
      iapply HΦ
      iframe Hsl
      have Hres : subslice (sint.nat (W64 0)) (sint.nat (i + W64 1))
          (key.set (sint.Z i).toNat (b + W8 1)) = prefixRangeEnd key := by
        have hb255 : b ≠ W8 255 := by intro h; subst h; simp at Hif
        rw [prefixRangeEnd_of_lt key (sint.nat i) b hb hb255 (fun j hj x hx =>
          Hi.2.2 j (by word) x hx)]
        have h0 : sint.nat (W64 0) = 0 := by decide
        have h1 : sint.nat (i + W64 1) = sint.nat i + 1 := by word
        have h2 : (sint.Z i).toNat = sint.nat i := rfl
        rw [h0, h1, h2, subslice, List.drop_zero]
        apply List.ext_getElem?
        intro k
        rw [List.getElem?_take, List.getElem?_append, List.length_take,
          Nat.min_eq_left (Nat.le_of_lt hilt), List.getElem?_set]
        rcases Nat.lt_trichotomy k (sint.nat i) with hk | hk | hk
        · simp [hk, Nat.ne_of_gt hk, show k < sint.nat i + 1 by omega]
        · subst hk; simp [hilt]
        · simp [show ¬ k < sint.nat i + 1 by omega, show ¬ k < sint.nat i by omega]
          omega
      rw [Hres]
      iexact Hout
    · wp_for_post
      iframe
      iexists (i - W64 1)
      iframe
      ipureintro
      have Hi1 : sint.Z (i - W64 1) = sint.Z i - 1 := by word
      have hb255 : b = W8 255 := by word
      refine ⟨by omega, by omega, ?_⟩
      intro j hj x hx
      rcases Nat.lt_or_ge (sint.nat i) j with hj' | hj'
      · exact Hi.2.2 j (by word) x hx
      · have : j = sint.nat i := by have := hi0; word
        subst this
        rw [hb] at hx
        cases hx
        exact hb255
  · have Hall : ∀ x ∈ key, x = W8 255 := by
      intro x hx
      obtain ⟨j, hj, hjx⟩ := List.getElem_of_mem hx
      have hneg : sint.Z i < 0 := by simpa using Hif
      exact Hi.2.2 j (by omega) x
        (by rw [List.getElem?_eq_getElem hj, hjx])
    iapply HΦ
    iframe
    rw [prefixRangeEnd_of_all key Hall]
    iexact Hnpe_sl

end proof

end EtcdGrove
end Perennial
