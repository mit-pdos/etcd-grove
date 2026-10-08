/-
Proof of `Spec/ringBuffer__RebaseHistory.lean`. Lean-first (no Rocq counterpart).
-/
import EtcdGrove.Cache.Spec.ringBuffer__RebaseHistory

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

theorem ringBuffer.RebaseHistory.wp_proof :
    ringBuffer.RebaseHistory.spec (GF := GF) (hG := hG) := by
  intro T' _ _ T _ V r cap isItem revOf items
  wp_start as H
  iNamed H
  wp_auto
  dsimp only at *
  rename_i gi_ptr
  irename : (gi_ptr ↦ zero_val w64 : IProp GF) => Hgi
  have Hl := Hok.len
  ihave %Hlen := ownSlice_len _ _ _ $$ Hbuf
  ihave HI : iprop(∃ (j k : w64) (ents' : List (entry T')),
      "i" ∷ i_ptr ↦ j ∗
      "Hgi" ∷ gi_ptr ↦ k ∗
      "Hbuf" ∷ rb.buffer' ↦* ents' ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ cap ∧ ents'.length = cap⌝) $$ [i Hgi Hbuf]
  · iexists W64 0, zero_val w64, ents
    simp only [named]
    iframe
    ipureintro; refine ⟨by word, by word, by word⟩
  wp_for HI
  wp_if_destruct
  · obtain ⟨e, He⟩ : ∃ e, ents'[sint.nat j]? = some e :=
      ⟨_, List.getElem?_eq_getElem (by word)⟩
    rw [ite_eq_left (by word)]
    wp_apply wp_load_slice_index rb.buffer' (sint.Z j) ents' _ e Hj.1 $$ [Hbuf] as Hbuf
    · iframe Hbuf; ipureintro; exact He
    rw [ite_eq_left (by word)]
    wp_apply wp_store_slice_index rb.buffer' (sint.Z j) ents' (zero_val (entry T')) $$ [Hbuf]
      as Hbuf
    · iframe Hbuf; ipureintro; word
    wp_for_post
    iframe
    iexists j + W64 1, j, _
    simp only [named]
    iframe
    ipureintro
    refine ⟨by word, by word, by simp [Hj.2.2]⟩
  · iapply HΦ
    iapply ownRingBuffer_intro r cap isItem revOf []
      { buffer' := rb.buffer', head' := W64 0, tail' := W64 0, size' := W64 0,
        revisionOf' := rb.revisionOf' } ents' ?_ (by simp) List.Pairwise.nil $$ Hr Hbuf [] HrevOf
    · have Hc := Hok.cap_pos
      have Hc2 := Hok.cap_le
      constructor <;> (try dsimp only) <;> (try simp only [List.length_nil]) <;> first | word | simp
    · imodintro; iintro %i %v %e %Hv; simp at Hv

end proof

end EtcdGrove
end Perennial
