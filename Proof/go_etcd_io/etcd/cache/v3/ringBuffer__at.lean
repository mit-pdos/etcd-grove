/-
Proof of `Spec/ringBuffer__at.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.ringBuffer__at
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

-- `wp_load` from a fractional struct points-to: a field-store `AccessStrict` instance
-- (which needs `DFrac.own 1`) is found first and the search does not backtrack to the
-- load instance, so the store instances are switched off here (this proof only loads).
attribute [-instance] ringBuffer.ringBuffer_access_store_buffer
  ringBuffer.ringBuffer_access_store_head ringBuffer.ringBuffer_access_store_tail
  ringBuffer.ringBuffer_access_store_size ringBuffer.ringBuffer_access_store_revisionOf

theorem ringBuffer.«at».wp_proof
    (wp_moduloIndex : ringBuffer.moduloIndex.spec (GF := GF) (hG := hG)) :
    ringBuffer.«at».spec (GF := GF) (hG := hG) := by
  intro T' _ _ T _ V r cap isItem revOf items dq i
  wp_start as ⟨H, %Hi⟩
  iNamed H
  wp_auto
  have Hc := Hok.cap_pos
  have Hc2 := Hok.cap_le
  have Hl := Hok.len
  have Ht := Hok.tail_lt
  have Hs := Hok.size_le
  wp_apply wp_moduloIndex $$ [Hr] as Hr
  · iframe Hr; ipureintro; refine ⟨by omega, by word, by word⟩
  rw [Hl, ringSlot_sint rb.tail' i cap Hc Hc2 Ht ⟨Hi.1, by omega⟩]
  obtain ⟨v, Hv⟩ : ∃ v, items[sint.nat i]? = some v :=
    ⟨_, List.getElem?_eq_getElem (by word)⟩
  obtain ⟨e, He, Herev⟩ := Hrev _ _ Hv
  have Hslot : ringSlot rb.tail' cap (sint.nat i) < cap := Nat.mod_lt _ Hc
  rw [ite_eq_left (by omega)]
  wp_apply wp_load_slice_index rb.buffer' _ ents _ e (by omega) $$ [Hbuf] as Hbuf
  · iframe Hbuf; ipureintro; rw [Int.toNat_natCast]; exact He
  ihave Hit := Hitems $$ %(sint.nat i) %v %e %Hv %He
  iapply HΦ
  iframe Hit
  isplitl [Hr Hbuf]
  · iapply ownRingBuffer_intro r cap isItem revOf items rb ents Hok Hrev Hsorted dq $$ Hr Hbuf Hitems HrevOf
  ipureintro; exact ⟨Hv, Herev⟩

end proof

end EtcdGrove
end Perennial
