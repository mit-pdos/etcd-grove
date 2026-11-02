module
public import Spec.go_etcd_io.bbolt.internal.common.InBucket__String
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

theorem InBucket.String.wp_proof : InBucket.String.spec (GF := GF) (hG := hG) := by
  intro l v dq
  wp_start as Hl
  wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  wp_apply fmt.wp_Sprintf as %s _
  iapply HΦ; iframe

end proof

end bbolt
end EtcdGrove
end Perennial
