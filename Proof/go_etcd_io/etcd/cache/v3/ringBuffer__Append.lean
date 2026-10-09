/-
Proof of `Spec/ringBuffer__Append.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.ringBuffer__Append
public import Spec.go_etcd_io.etcd.cache.v3.ringBuffer__full

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

/-- The end of both branches: with the new item stored in slot `idx = tail + n` (the
old `head`) and the struct's fields updated (`Hok'`, the new tail `Ht'`), the ring holds
`ringAppend cap items v`. -/
private theorem append_close {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T'] {V : Type}
    (r : Loc) (cap : Nat) (isItem : T' → V → IProp GF) (revOf : V → w64) (items : List V)
    (item : T') (v : V) (rb' : ringBuffer T') (ents : List (entry T')) (t : w64) (idx : Nat)
    (Hok' : RingOk rb' cap (ringAppend cap items v).length)
    (Hrev : ∀ (i : Nat) (w : V), items[i]? = some w →
      ∃ e, ents[ringSlot t cap i]? = some e ∧ e.revision' = revOf w)
    (Ht' : sint.nat rb'.tail' =
      if items.length < cap then sint.nat t else (sint.nat t + 1) % cap)
    (Hsorted : RevSorted revOf items) (Habove : RevAbove revOf items v)
    (Hc : 0 < cap) (Hsl : items.length ≤ cap)
    (Hidx : idx = (sint.nat t + items.length) % cap) (Hidxl : idx < ents.length) :
    ⊢ (r ↦ rb' : IProp GF) -∗
      rb'.buffer' ↦* ents.set idx ({ revision' := revOf v, item' := item } : entry T') -∗
      □ (∀ (i : Nat) (w : V) (e : entry T'), ⌜items[i]? = some w⌝ -∗
        ⌜ents[ringSlot t cap i]? = some e⌝ -∗ isItem e.item' w) -∗
      □ isItem item v -∗
      revisionOfSpec rb'.revisionOf' isItem revOf -∗
      ownRingBuffer r cap isItem revOf (ringAppend cap items v) := by
  iintro Hr Hbuf #Hitems #Hitem #HrevOf
  have Hlk := ringAppend_lookup (sint.nat t) (sint.nat rb'.tail') cap items v Hc Hsl Ht'
  have Hrev' : ∀ (i : Nat) (w : V), (ringAppend cap items v)[i]? = some w →
      ∃ e, (ents.set idx ({ revision' := revOf v, item' := item } : entry T'))[
        ringSlot rb'.tail' cap i]? = some e ∧ e.revision' = revOf w := by
    intro i w Hw
    rcases Hlk i w Hw with ⟨Hslot, rfl⟩ | ⟨j, Hj, Hslot, Hne⟩
    · refine ⟨{ revision' := revOf w, item' := item }, ?_, rfl⟩
      simp only [ringSlot]
      rw [Hslot, ← Hidx, List.getElem?_set_self Hidxl]
    · obtain ⟨e, He, Herev⟩ := Hrev j w Hj
      refine ⟨e, ?_, Herev⟩
      simp only [ringSlot] at He ⊢
      rw [Hslot, List.getElem?_set_ne (by omega)]
      exact He
  iapply ownRingBuffer_intro r cap isItem revOf _ rb' _ Hok' Hrev'
    (Hsorted.ringAppend_of Habove cap) $$ Hr Hbuf [] HrevOf
  imodintro
  iintro %i %w %e %Hw %He
  rcases Hlk i w Hw with ⟨Hslot, rfl⟩ | ⟨j, Hj, Hslot, Hne⟩
  · simp only [ringSlot] at He
    rw [Hslot, ← Hidx, List.getElem?_set_self Hidxl] at He
    cases He
    iexact Hitem
  · simp only [ringSlot] at He
    rw [Hslot, List.getElem?_set_ne (by omega)] at He
    iapply Hitems $$ %j %w %e %Hj %He

theorem ringBuffer.Append.wp_proof
    (wp_full : ringBuffer.full.spec (GF := GF) (hG := hG)) :
    ringBuffer.Append.spec (GF := GF) (hG := hG) := by
  intro T' _ _ T _ V r cap isItem _ revOf items item v
  wp_start as ⟨H, #Hitem, %Habove⟩
  iNamed H
  wp_auto
  ihave #Hro := HrevOf
  iunfold revisionOfSpec at Hro
  wp_apply Hro $$ %item %v [$Hitem]
  iclear Hro
  ihave H := ownRingBuffer_intro r cap isItem revOf items rb ents Hok Hrev Hsorted $$ Hr Hbuf Hitems HrevOf
  iclear Hitems HrevOf
  clear Hok Hrev rb ents
  wp_apply wp_full $$ [$H] as H
  iNamed H
  have Hc := Hok.cap_pos
  have Hc2 := Hok.cap_le
  have Hl := Hok.len
  have Ht := Hok.tail_lt
  have Hs := Hok.size
  have Hsl := Hok.size_le
  have Hh := Hok.head
  have Hh0 : 0 ≤ sint.Z rb.head' := by rw [Hh]; exact Int.emod_nonneg _ (by omega)
  have Hh1 : sint.Z rb.head' < cap := by rw [Hh]; exact Int.emod_lt_of_pos _ (by omega)
  have Hhn : (sint.Z rb.head').toNat = (sint.nat rb.tail' + items.length) % cap := by
    rw [Hh, show sint.Z rb.tail' = ((sint.nat rb.tail' : Nat) : Int) by word,
      ← Int.natCast_add, ← Int.natCast_emod, Int.toNat_natCast]
  ihave %Hlen := ownSlice_len _ _ _ $$ Hbuf
  have Hel : ents.length = cap := by have := Hlen.1; word
  wp_if_destruct
  · -- full: the oldest item is overwritten, `tail` moves on
    try dsimp only at *
    rw [ite_eq_left (by omega)]
    wp_apply wp_store_slice_index rb.buffer' (sint.Z rb.head') ents
      ({ revision' := revOf v, item' := item } : entry T') $$ [Hbuf] as Hbuf
    · iframe Hbuf; ipureintro; omega
    try dsimp only at *
    iapply HΦ
    have Hlen' : (ringAppend items.length items v).length = items.length := by
      simp only [ringAppend, Nat.lt_irrefl, ite_false, List.length_append, List.length_tail,
        List.length_singleton]; omega
    have Ht1 := sint_srem_succ rb.tail' rb.buffer'.len items.length Hl Hc2 Ht.1 Ht.2
    have Hh1' := sint_srem_succ rb.head' rb.buffer'.len items.length Hl Hc2 Hh0 Hh1
    have Hm0 : 0 ≤ (sint.Z rb.tail' + 1) % (items.length : Int) := Int.emod_nonneg _ (by omega)
    have Hm1 : (sint.Z rb.tail' + 1) % (items.length : Int) < items.length :=
      Int.emod_lt_of_pos _ (by omega)
    have Hok' : RingOk (T' := T')
        { buffer' := rb.buffer', head' := BitVec.srem (rb.head' + W64 1) rb.buffer'.len,
          tail' := BitVec.srem (rb.tail' + W64 1) rb.buffer'.len, size' := rb.size',
          revisionOf' := rb.revisionOf' }
        items.length (ringAppend items.length items v).length := by
      rw [Hlen']
      refine ⟨Hc, Hc2, Hl, Hs, Nat.le_refl _, ⟨?_, ?_⟩, ?_⟩ <;> dsimp only <;> rw [Ht1]
      · exact Hm0
      · exact Hm1
      · rw [Hh1', Hh, Int.emod_add_emod, Int.add_emod_right, Int.emod_emod,
          show sint.Z rb.tail' + (items.length : Int) + 1 = sint.Z rb.tail' + 1 + items.length
            by omega, Int.add_emod_right]
    have Ht' : sint.nat (BitVec.srem (rb.tail' + W64 1) rb.buffer'.len) =
        if items.length < items.length then sint.nat rb.tail' else
          (sint.nat rb.tail' + 1) % items.length := by
      rw [ite_eq_right (Nat.lt_irrefl _)]
      have : sint.Z rb.tail' = ((sint.nat rb.tail' : Nat) : Int) := by word
      rw [this] at Ht1
      have Ht2 : sint.Z (BitVec.srem (rb.tail' + W64 1) rb.buffer'.len) =
          (((sint.nat rb.tail' + 1) % items.length : Nat) : Int) := by
        rw [Ht1]; push_cast; rfl
      word
    iapply append_close r items.length isItem revOf items item v _ ents rb.tail'
      (sint.Z rb.head').toNat Hok' Hrev Ht' Hsorted Habove Hc (Nat.le_refl _) Hhn (by omega)
      $$ Hr Hbuf Hitems Hitem HrevOf
  · -- not full: `size` grows
    try dsimp only at *
    rw [ite_eq_left (by omega)]
    wp_apply wp_store_slice_index rb.buffer' (sint.Z rb.head') ents
      ({ revision' := revOf v, item' := item } : entry T') $$ [Hbuf] as Hbuf
    · iframe Hbuf; ipureintro; omega
    try dsimp only at *
    iapply HΦ
    have Hlt : items.length < cap := by omega
    have Hlen' : (ringAppend cap items v).length = items.length + 1 := by
      simp only [ringAppend, Hlt, ite_true, List.length_append, List.length_singleton]
    have Hh1' := sint_srem_succ rb.head' rb.buffer'.len cap Hl Hc2 Hh0 Hh1
    have Hok' : RingOk (T' := T')
        { buffer' := rb.buffer', head' := BitVec.srem (rb.head' + W64 1) rb.buffer'.len,
          tail' := rb.tail', size' := rb.size' + W64 1, revisionOf' := rb.revisionOf' }
        cap (ringAppend cap items v).length := by
      rw [Hlen']
      refine ⟨Hc, Hc2, Hl, ?_, by omega, Ht, ?_⟩ <;> dsimp only
      · word
      · rw [Hh1', Hh, Int.emod_add_emod, Int.add_assoc]; push_cast; rfl
    have Ht' : sint.nat rb.tail' =
        if items.length < cap then sint.nat rb.tail' else (sint.nat rb.tail' + 1) % cap := by
      rw [ite_eq_left Hlt]
    iapply append_close r cap isItem revOf items item v _ ents rb.tail'
      (sint.Z rb.head').toNat Hok' Hrev Ht' Hsorted Habove Hc Hsl Hhn (by omega)
      $$ Hr Hbuf Hitems Hitem HrevOf

end proof

end EtcdGrove
end Perennial
