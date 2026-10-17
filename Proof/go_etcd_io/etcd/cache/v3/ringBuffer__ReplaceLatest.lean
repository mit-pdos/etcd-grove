/-
Proof of `Spec/ringBuffer__ReplaceLatest.lean` (etcd-io/etcd#21676). Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.ringBuffer__ReplaceLatest
public import Spec.go_etcd_io.etcd.cache.v3.ringBuffer__moduloIndex

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

/-- `ReplaceLatest`'s index `moduloIndex(head - 1)` is the slot of the newest of `n > 0`
items. -/
private theorem replace_slot (tail head len : w64) (cap n : Nat) (hc : 0 < cap)
    (hc2 : cap ≤ 2 ^ 61) (hn : 0 < n) (ht : 0 ≤ sint.Z tail ∧ sint.Z tail < cap)
    (hh : sint.Z head = (sint.Z tail + n) % cap) (hl : sint.Z len = cap) :
    sint.Z (W64 (sint.Z (head - W64 1) % sint.Z len)) = (ringSlot tail cap (n - 1) : Int) := by
  have h0 : 0 ≤ sint.Z head := by rw [hh]; exact Int.emod_nonneg _ (by omega)
  have h1 : sint.Z head < cap := by rw [hh]; exact Int.emod_lt_of_pos _ (by omega)
  have e : sint.Z (head - W64 1) % sint.Z len = sint.Z (head - W64 1 + len) % sint.Z len := by
    rw [show sint.Z (head - W64 1 + len) = sint.Z (head - W64 1) + sint.Z len by word,
      Int.add_emod_right]
  rw [e]
  exact latest_slot tail head len cap n hc hc2 hn ht hh hl

/-- The items after `ReplaceLatest`: index `n - 1` is the new one, the others are the
old ones. -/
private theorem replace_lookup {V : Type} (items : List V) (v w : V) (i : Nat)
    (hw : (items.dropLast ++ [v])[i]? = some w) :
    (i = items.length - 1 ∧ w = v) ∨ (i < items.length - 1 ∧ items[i]? = some w) := by
  rcases Nat.lt_or_ge i items.dropLast.length with hi | hi
  · right
    rw [List.getElem?_append_left hi] at hw
    rw [List.length_dropLast] at hi
    refine ⟨hi, ?_⟩
    rw [List.getElem?_dropLast] at hw
    simpa [hi] using hw
  · left
    rw [List.getElem?_append_right hi, List.getElem?_singleton] at hw
    rw [List.length_dropLast] at hi
    by_cases h0 : i - items.dropLast.length = 0
    · rw [ite_eq_left h0] at hw
      rw [List.length_dropLast] at h0
      exact ⟨by omega, by simpa using hw.symm⟩
    · rw [ite_eq_right h0] at hw; simp at hw

theorem ringBuffer.ReplaceLatest.wp_proof
    (wp_moduloIndex : ringBuffer.moduloIndex.spec (GF := GF) (hG := hG)) :
    ringBuffer.ReplaceLatest.spec (GF := GF) (hG := hG) := by
  intro T' _ _ T _ V r cap isItem _ revOf items item v
  wp_start as ⟨H, #Hitem, %Hpre⟩
  obtain ⟨Hne, Habove⟩ := Hpre
  iNamed H
  wp_auto
  have Hc := Hok.cap_pos
  have Hc2 := Hok.cap_le
  have Hl := Hok.len
  have Ht := Hok.tail_lt
  have Hs := Hok.size
  have Hsl := Hok.size_le
  have Hpos : 0 < items.length := List.length_pos_iff.2 Hne
  wp_if_destruct
  · exfalso; word
  ihave #Hro := HrevOf
  iunfold revisionOfSpec at Hro
  wp_apply Hro $$ %item %v [$Hitem]
  iclear Hro
  have Hh0 : 0 ≤ sint.Z rb.head' := by rw [Hok.head]; exact Int.emod_nonneg _ (by omega)
  have Hh1 : sint.Z rb.head' < cap := by rw [Hok.head]; exact Int.emod_lt_of_pos _ (by omega)
  have Hm1 : -sint.Z rb.buffer'.len ≤ sint.Z (rb.head' - W64 1) := by word
  have Hm2 : sint.Z (rb.head' - W64 1) + sint.Z rb.buffer'.len < 2 ^ 63 := by word
  wp_apply wp_moduloIndex $$ [Hr] as Hr
  · iframe Hr; ipureintro; exact ⟨by omega, Hm1, Hm2⟩
  have Hidx := replace_slot rb.tail' rb.head' rb.buffer'.len cap items.length Hc Hc2 Hpos Ht
    Hok.head Hl
  have Hslot : ringSlot rb.tail' cap (items.length - 1) < cap := Nat.mod_lt _ Hc
  ihave %Hlen := ownSlice_len _ _ _ $$ Hbuf
  have Hel : ents.length = cap := by have := Hlen.1; word
  rw [Hidx, ite_eq_left (by omega)]
  wp_apply wp_store_slice_index rb.buffer' _ ents
    ({ revision' := revOf v, item' := item } : entry T') $$ [Hbuf] as Hbuf
  · iframe Hbuf; ipureintro; omega
  iapply HΦ
  rw [Int.toNat_natCast]
  have Hn' : (items.dropLast ++ [v]).length = items.length := by
    simp only [List.length_append, List.length_dropLast, List.length_singleton]; omega
  have Hok' : RingOk rb cap (items.dropLast ++ [v]).length := by rw [Hn']; exact Hok
  have Hsorted' : RevSorted revOf (items.dropLast ++ [v]) := by
    have H1 := RevSorted.ringAppend_of (Hsorted.sublist (List.dropLast_sublist items)) Habove items.length
    unfold ringAppend at H1
    rw [ite_eq_left (by rw [List.length_dropLast]; omega)] at H1
    exact H1
  have Hne_slot : ∀ i, i < items.length - 1 →
      ringSlot rb.tail' cap i ≠ ringSlot rb.tail' cap (items.length - 1) := by
    intro i hi h
    have := mod_inj_of_lt _ cap i (items.length - 1) (by omega) (by omega) h
    omega
  have Hrev' : ∀ (i : Nat) (w : V), (items.dropLast ++ [v])[i]? = some w →
      ∃ e, (ents.set (ringSlot rb.tail' cap (items.length - 1))
        ({ revision' := revOf v, item' := item } : entry T'))[ringSlot rb.tail' cap i]? = some e ∧
        e.revision' = revOf w := by
    intro i w Hw
    rcases replace_lookup items v w i Hw with ⟨rfl, rfl⟩ | ⟨hi, Hi⟩
    · exact ⟨_, List.getElem?_set_self (by omega), rfl⟩
    · obtain ⟨e, He, Herev⟩ := Hrev i w Hi
      exact ⟨e, by rw [List.getElem?_set_ne (Hne_slot i hi).symm]; exact He, Herev⟩
  iapply ownRingBuffer_intro r cap isItem revOf _ rb _ Hok' Hrev' Hsorted' $$ Hr Hbuf [] HrevOf
  imodintro
  iintro %i %w %e %Hw %He
  rcases replace_lookup items v w i Hw with ⟨rfl, rfl⟩ | ⟨hi, Hi⟩
  · rw [List.getElem?_set_self (by omega)] at He
    cases He
    iexact Hitem
  · rw [List.getElem?_set_ne (Hne_slot i hi).symm] at He
    iapply Hitems $$ %i %w %e %Hi %He

end proof

end EtcdGrove
end Perennial
