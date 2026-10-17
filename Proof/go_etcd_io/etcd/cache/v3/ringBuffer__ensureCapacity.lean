/-
Proof of `Spec/ringBuffer__ensureCapacity.lean` (etcd-io/etcd#21676). Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.ringBuffer__ensureCapacity
public import Spec.go_etcd_io.etcd.cache.v3.ringBuffer__at

@[expose] public section

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

theorem ringBuffer.ensureCapacity.wp_proof
    (wp_at : ringBuffer.«at».spec (GF := GF) (hG := hG)) :
    ringBuffer.ensureCapacity.spec (GF := GF) (hG := hG) := by
  intro T' _ _ T _ V r cap isItem _ revOf items minCapacity
  wp_start as ⟨H, %Hmin⟩
  iNamed H
  wp_auto
  have Hc := Hok.cap_pos
  have Hc2 := Hok.cap_le
  have Hl := Hok.len
  have Hsl := Hok.size_le
  have Hs := Hok.size
  wp_if_destruct
  · -- big enough already: `k = 0`
    ispecialize HΦ $$ %0
    rw [Nat.pow_zero, Nat.mul_one]
    iapply HΦ
    isplitl
    · iapply ownRingBuffer_intro r cap isItem revOf items rb ents Hok Hrev Hsorted $$ Hr Hbuf Hitems HrevOf
    · ipureintro; exact ⟨by omega, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  have Hgrow : (cap : Int) < sint.Z minCapacity := by omega
  wp_if_destruct
  · exfalso; have := congrArg sint.Z Hif; rw [Hl] at this; simp at this; omega
  -- the doubling: `newCap = cap * 2^k`, `k` the number of doublings so far
  ihave HI : iprop(∃ (c : w64) (k : Nat),
      "newCap" ∷ newCap_ptr ↦ c ∗
      "%Hk" ∷ ⌜sint.Z c = ((cap * 2 ^ k : Nat) : Int) ∧ cap * 2 ^ k ≤ 2 ^ 61 ∧
        ∀ j < k, ((cap * 2 ^ j : Nat) : Int) < sint.Z minCapacity⌝) $$ [newCap]
  · iexists rb.buffer'.len, 0
    simp only [named]
    iframe
    ipureintro
    refine ⟨by rw [Hl]; simp, by simp; omega, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  wp_for HI
  cleanup_bool_decide
  wp_if_destruct
  · -- below `minCapacity`: double
    wp_for_post
    iframe
    iexists c * W64 2, k + 1
    simp only [named]
    iframe
    ipureintro
    have Hpow : cap * 2 ^ (k + 1) = cap * 2 ^ k * 2 := by rw [Nat.pow_succ, Nat.mul_assoc]
    have Hlt : ((cap * 2 ^ k : Nat) : Int) < sint.Z minCapacity := by rw [← Hk.1]; exact Hif
    refine ⟨?_, ?_, fun j hj => ?_⟩
    · rw [Hpow]
      have h1 := Hk.1
      generalize cap * 2 ^ k = M at h1 Hlt ⊢
      push_cast; word
    · rw [Hpow]; push_cast at Hlt; omega
    · rcases Nat.lt_or_ge j k with h | h
      · exact Hk.2.2 j h
      · have : j = k := by omega
        subst this; exact Hlt
  have Hge : sint.Z minCapacity ≤ ((cap * 2 ^ k : Nat) : Int) := by rw [← Hk.1]; omega
  have Hkc : cap * 2 ^ k ≤ 2 ^ 61 := Hk.2.1
  have Hcn : sint.nat c = cap * 2 ^ k := by simp only [sint.nat, Hk.1, Int.toNat_natCast]
  wp_apply wp_slice_make2 (V := entry T') c $$ [] as %nb ⟨Hnb, -⟩
  · ipureintro; rw [Hk.1]; omega
  rw [Hcn]
  ihave H := ownRingBuffer_intro r cap isItem revOf items rb ents Hok Hrev Hsorted $$ Hr Hbuf Hitems HrevOf
  iclear Hitems HrevOf
  clear Hrev
  -- the copy: the first `i` items are in `newBuffer[0..i)`
  ihave HI : iprop(∃ (i : w64) (nents : List (entry T')),
      "i" ∷ i_ptr ↦ i ∗
      "H" ∷ ownRingBuffer r cap isItem revOf items ∗
      "Hnb" ∷ nb ↦* nents ∗
      "#Hnit" ∷ □ (∀ (j : Nat) (v : V) (e : entry T'), ⌜j < sint.nat i⌝ -∗ ⌜items[j]? = some v⌝ -∗
        ⌜nents[j]? = some e⌝ -∗ isItem e.item' v) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ items.length ∧ nents.length = cap * 2 ^ k ∧
        ∀ (j : Nat) (v : V), j < sint.nat i → items[j]? = some v →
          ∃ e, nents[j]? = some e ∧ e.revision' = revOf v⌝) $$ [i H Hnb]
  · have h0 : sint.nat (W64 0) = 0 := by word
    iexists W64 0, _
    simp only [named]
    iframe
    isplit
    · imodintro; iintro %j %v %e %Hj; exfalso; omega
    · ipureintro
      refine ⟨by word, by word, List.length_replicate, fun j v hj _ => ?_⟩
      exfalso; omega
  wp_for HI
  icases ownRingBuffer_struct_acc r cap isItem revOf items $$ H with ⟨%rb, Hr, %Hsz, Hclose⟩
  wp_auto
  ihave H := Hclose $$ Hr
  cleanup_bool_decide
  wp_if_destruct
  · -- copy item `i`
    have Hin : sint.Z i < items.length := by rw [← Hsz]; exact Hif
    wp_apply wp_at $$ [$H] as %e %v ⟨H, % ⟨Hv, Herev⟩, Hit⟩
    · ipureintro; exact ⟨Hi.1, Hin⟩
    icases Hit with #Hit
    have Hcap : items.length < cap * 2 ^ k := by
      have : cap ≤ cap * 2 ^ k := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos k)
      omega
    ihave %Hnbl := ownSlice_len _ _ _ $$ Hnb
    have Hnbz : sint.Z nb.len = ((cap * 2 ^ k : Nat) : Int) := by
      have := Hi.2.2.1; have := Hnbl.1; word
    rw [ite_eq_left (by omega)]
    wp_apply wp_store_slice_index nb (sint.Z i) nents e $$ [Hnb] as Hnb
    · iframe Hnb; ipureintro; omega
    wp_for_post
    iframe
    have Hi1 : sint.nat (i + W64 1) = sint.nat i + 1 := by word
    have Hil : sint.nat i < nents.length := by word
    iexists i + W64 1, _
    simp only [named]
    iframe
    isplit
    · imodintro
      iintro %j %w %e' %Hj %Hw %He'
      rw [Hi1] at Hj
      rcases Nat.lt_or_ge j (sint.nat i) with h | h
      · rw [List.getElem?_set_ne (by show sint.nat i ≠ j; omega)] at He'
        iapply Hnit $$ %j %w %e' %h %Hw %He'
      · have hj : j = sint.nat i := by omega
        subst hj
        rw [show (sint.Z i).toNat = sint.nat i from rfl, List.getElem?_set_self Hil] at He'
        rw [Hv] at Hw
        cases He'; cases Hw
        iexact Hit
    · ipureintro
      refine ⟨by word, by word, by simp [Hi.2.2.1], fun j w hj hw => ?_⟩
      rw [Hi1] at hj
      rcases Nat.lt_or_ge j (sint.nat i) with h | h
      · obtain ⟨e', He', Hr'⟩ := Hi.2.2.2 j w h hw
        refine ⟨e', ?_, Hr'⟩
        rw [List.getElem?_set_ne (by show sint.nat i ≠ j; omega)]; exact He'
      · have hj : j = sint.nat i := by omega
        subst hj
        rw [Hv] at hw; cases hw
        exact ⟨e, by rw [show (sint.Z i).toNat = sint.nat i from rfl, List.getElem?_set_self Hil],
          Herev⟩
  · -- every item copied: install the new buffer
    have Hall : sint.Z i = items.length := by rw [← Hsz]; omega
    iNamed H
    wp_auto
    try dsimp only at *
    ispecialize HΦ $$ %k
    iapply HΦ
    isplitl
    · have Hcap : items.length < cap * 2 ^ k := by
        have : cap ≤ cap * 2 ^ k := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos k)
        have := Hok.size_le
        omega
      ihave %Hnbl := ownSlice_len _ _ _ $$ Hnb
      have Hok' : RingOk (T' := T')
          { buffer' := nb, head' := rb.size', tail' := W64 0, size' := rb.size',
            revisionOf' := rb.revisionOf' } (cap * 2 ^ k) items.length := by
        have Hs := Hok.size
        refine ⟨by have := Nat.two_pow_pos k; exact Nat.mul_pos Hc this, Hkc, ?_, Hs, by omega,
          ⟨by word, by word⟩, ?_⟩ <;> dsimp only
        · have := Hi.2.2.1; have := Hnbl.1; word
        · rw [Hs, show sint.Z (W64 0) = 0 from rfl, Int.zero_add, Int.emod_eq_of_lt (by omega) (by omega)]
      have Hslot0 : ∀ j, j < items.length → ringSlot (W64 0) (cap * 2 ^ k) j = j := by
        intro j hj
        simp only [ringSlot, show sint.nat (W64 0) = 0 from rfl, Nat.zero_add]
        exact Nat.mod_eq_of_lt (by omega)
      have Hin : ∀ j, j < items.length → j < sint.nat i := by
        intro j hj; simp only [sint.nat, Hall, Int.toNat_natCast]; exact hj
      have Hrev' : ∀ (j : Nat) (w : V), items[j]? = some w →
          ∃ e, nents[ringSlot (W64 0) (cap * 2 ^ k) j]? = some e ∧ e.revision' = revOf w := by
        intro j w hw
        have hj := (List.getElem?_eq_some_iff.1 hw).1
        rw [Hslot0 j hj]
        exact Hi.2.2.2 j w (Hin j hj) hw
      iapply ownRingBuffer_intro r (cap * 2 ^ k) isItem revOf items _ nents Hok' Hrev' Hsorted
        $$ Hr Hnb [] HrevOf
      imodintro
      iintro %j %w %e %Hw %He
      have hj := (List.getElem?_eq_some_iff.1 Hw).1
      rw [Hslot0 j hj] at He
      iapply Hnit $$ %j %w %e %(Hin j hj) %Hw %He
    · ipureintro; exact ⟨Hge, Hk.2.2⟩

end proof

end EtcdGrove
end Perennial
