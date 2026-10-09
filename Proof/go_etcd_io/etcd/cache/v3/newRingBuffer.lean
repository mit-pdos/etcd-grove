/-
Proof of `Spec/newRingBuffer.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.newRingBuffer

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

theorem newRingBuffer.wp_proof : newRingBuffer.spec (GF := GF) (hG := hG) := by
  intro T' _ _ T _ V capacity revisionOf isItem revOf
  wp_start as ⟨%Hcap, #HrevOf⟩
  wp_auto
  wp_apply (wp_slice_make2 (V := entry T') (t := entry.ty T)) as %sl ⟨Hbuf, -⟩
  · ipureintro; omega
  wp_alloc r as Hr
  wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hbuf
  simp only [List.length_replicate] at Hlen
  have Hok : RingOk (T' := T')
      { buffer' := sl, head' := 0, tail' := 0, size' := 0, revisionOf' := revisionOf }
      (sint.nat capacity) ([] : List V).length := by
    constructor <;> (try dsimp only) <;> (try simp only [List.length_nil]) <;> first | word | simp
  iapply HΦ
  iapply ownRingBuffer_intro r (sint.nat capacity) isItem revOf []
    { buffer' := sl, head' := 0, tail' := 0, size' := 0, revisionOf' := revisionOf } _
    Hok (by simp) (List.Pairwise.nil) $$ Hr Hbuf [] HrevOf
  imodintro; iintro %i %v %e %Hv; simp at Hv

end proof

end EtcdGrove
end Perennial
