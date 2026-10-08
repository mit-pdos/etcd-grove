/-
Proof of `Spec/ringBuffer__moduloIndex.lean`. Lean-first (no Rocq counterpart).
-/
import EtcdGrove.Cache.Spec.ringBuffer__moduloIndex

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

theorem ringBuffer.moduloIndex.wp_proof :
    ringBuffer.moduloIndex.spec (GF := GF) (hG := hG) := by
  intro T' _ _ T _ r rb dq index
  wp_start as ⟨Hr, %Hidx⟩
  wp_auto
  rw [srem_add_len index rb.buffer'.len _ rfl Hidx.1 Hidx.2.1 Hidx.2.2]
  iapply HΦ $$ Hr

end proof

end EtcdGrove
end Perennial
