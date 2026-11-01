module
public import Spec.go_etcd_io.bbolt.internal.common.LoadPageMeta
public import Proof.go_etcd_io.bbolt.internal.common.Bytes

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.common

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]

theorem LoadPageMeta.wp_proof : LoadPageMeta.spec (GF := GF) (hG := hG) := by
  intro buf Hlen Hc
  wp_start
  wp_auto
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
  unfold sliceIndexRef
  rw [arrayIndexRef_w8 (hG := hG) _ _ Hc, show sint.Z (W64 16) = 16 by rfl]
  wp_auto
  iapply HΦ; itrivial

end proof

end bbolt
end EtcdGrove
end Perennial
