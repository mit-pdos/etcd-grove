/-
Proof of `Spec/ringBuffer__PeekLatest.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.ringBuffer__PeekLatest

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

theorem ringBuffer.PeekLatest.wp_proof : ringBuffer.PeekLatest.spec (GF := GF) (hG := hG) := by
  intro T' _ _ T _ V r cap isItem revOf items
  wp_start as H
  iNamed H
  wp_auto
  have Hc := Hok.cap_pos
  have Hl := Hok.len
  have Ht := Hok.tail_lt
  have Hs := Hok.size
  wp_if_destruct
  · -- empty
    have Hnil : items = [] := by
      apply List.eq_nil_of_length_eq_zero; word
    subst Hnil
    rw [show latestRev revOf ([] : List V) = W64 0 from rfl]
    iapply HΦ
    iapply ownRingBuffer_intro r cap isItem revOf [] rb ents Hok Hrev Hsorted $$ Hr Hbuf Hitems HrevOf
  · -- the newest item is at slot `(head - 1 + cap) % cap`
    have Hpos : 0 < items.length := by
      have : sint.Z rb.size' ≠ 0 := by word
      omega
    obtain ⟨v, Hv⟩ : ∃ v, items[items.length - 1]? = some v :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨e, He, Herev⟩ := Hrev _ v Hv
    have Hidx := latest_slot rb.tail' rb.head' rb.buffer'.len cap items.length Hc Hok.cap_le
      Hpos Ht Hok.head Hl
    have Hh0 : 0 ≤ sint.Z rb.head' := by rw [Hok.head]; exact Int.emod_nonneg _ (by omega)
    have Hh1 : sint.Z rb.head' < cap := by rw [Hok.head]; exact Int.emod_lt_of_pos _ (by omega)
    have Hc2 := Hok.cap_le
    have Hnn : 0 ≤ sint.Z (rb.head' - W64 1 + rb.buffer'.len) := by word
    rw [if_neg (show ¬ sint.Z rb.buffer'.len = 0 by omega)]
    wp_auto
    rw [srem_of_nonneg _ _ Hnn (by omega), Hidx]
    have Hslot : ringSlot rb.tail' cap (items.length - 1) < cap := Nat.mod_lt _ Hc
    rw [ite_eq_left (by omega)]
    icases ownSlice_elem_acc ((ringSlot rb.tail' cap (items.length - 1) : Nat) : Int) e rb.buffer'
      _ ents (by omega) (by rw [Int.toNat_natCast]; exact He) $$ Hbuf with ⟨He', Hclose⟩
    wp_auto
    ihave Hbuf := Hclose $$ %e He'
    rw [Int.toNat_natCast, list_set_lookup_self ents _ e He]
    have Hlast : latestRev revOf items = e.revision' := by
      simp [latestRev, List.getLast?_eq_getElem?, Hv, Herev]
    rw [Hlast]
    iapply HΦ
    iapply ownRingBuffer_intro r cap isItem revOf items rb ents Hok Hrev Hsorted $$ Hr Hbuf Hitems HrevOf

end proof

end EtcdGrove
end Perennial
