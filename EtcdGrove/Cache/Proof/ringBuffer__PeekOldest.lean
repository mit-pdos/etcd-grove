/-
Proof of `Spec/ringBuffer__PeekOldest.lean`. Lean-first (no Rocq counterpart).
-/
import EtcdGrove.Cache.Spec.ringBuffer__PeekOldest

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

theorem ringBuffer.PeekOldest.wp_proof : ringBuffer.PeekOldest.spec (GF := GF) (hG := hG) := by
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
    rw [show oldestRev revOf ([] : List V) = W64 0 from rfl]
    iapply HΦ
    iapply ownRingBuffer_intro r cap isItem revOf [] rb ents Hok Hrev Hsorted $$ Hr Hbuf Hitems HrevOf
  · -- the oldest item is at slot `tail`
    have Hpos : 0 < items.length := by
      have : sint.Z rb.size' ≠ 0 := by word
      omega
    obtain ⟨v, Hv⟩ : ∃ v, items[0]? = some v := ⟨_, List.getElem?_eq_getElem Hpos⟩
    obtain ⟨e, He, Herev⟩ := Hrev 0 v Hv
    have Hslot : ringSlot rb.tail' cap 0 = (sint.Z rb.tail').toNat := by
      simp only [ringSlot, Nat.add_zero]; apply Nat.mod_eq_of_lt; word
    rw [Hslot] at He
    rw [ite_eq_left (by omega)]
    icases ownSlice_elem_acc (sint.Z rb.tail') e rb.buffer' _ ents Ht.1 He $$ Hbuf with ⟨He', Hclose⟩
    wp_auto
    ihave Hbuf := Hclose $$ %e He'
    rw [list_set_lookup_self ents _ e He]
    have Hold : oldestRev revOf items = e.revision' := by
      simp [oldestRev, List.head?_eq_getElem?, Hv, Herev]
    rw [Hold]
    iapply HΦ
    iapply ownRingBuffer_intro r cap isItem revOf items rb ents Hok Hrev Hsorted $$ Hr Hbuf Hitems HrevOf

end proof

end EtcdGrove
end Perennial
