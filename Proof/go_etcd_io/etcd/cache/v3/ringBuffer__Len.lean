/-
Proof of `Spec/ringBuffer__Len.lean` (etcd-io/etcd#21676). Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.ringBuffer__Len

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

-- `wp_load` from a fractional struct points-to: as in `ringBuffer__moduloIndex.lean`, the
-- field-store `AccessStrict` instances (which need `DFrac.own 1`) are switched off.
attribute [-instance] ringBuffer.ringBuffer_access_store_buffer
  ringBuffer.ringBuffer_access_store_head ringBuffer.ringBuffer_access_store_tail
  ringBuffer.ringBuffer_access_store_size ringBuffer.ringBuffer_access_store_revisionOf

theorem ringBuffer.Len.wp_proof : ringBuffer.Len.spec (GF := GF) (hG := hG) := by
  intro T' _ _ T _ V r cap isItem revOf items dq
  wp_start as H
  iNamed H
  wp_auto
  have Hs := Hok.size
  have Hc2 := Hok.cap_le
  have Hsl := Hok.size_le
  rw [show rb.size' = W64 items.length by word]
  iapply HΦ
  iapply ownRingBuffer_intro r cap isItem revOf items rb ents Hok Hrev Hsorted dq
    $$ Hr Hbuf Hitems HrevOf

end proof

end EtcdGrove
end Perennial
