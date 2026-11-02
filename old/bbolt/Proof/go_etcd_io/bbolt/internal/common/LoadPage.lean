module
public import Spec.go_etcd_io.bbolt.internal.common.LoadPage
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

theorem LoadPage.wp_proof : LoadPage.spec (GF := GF) (hG := hG) := by
  intro buf Hlen
  wp_start
  wp_auto
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
  unfold sliceIndexRef
  rw [show sint.Z (W64 0) = 0 by rfl, arrayIndexRef_zero]
  wp_auto
  iapply HΦ; itrivial

end proof

end bbolt
end EtcdGrove
end Perennial
