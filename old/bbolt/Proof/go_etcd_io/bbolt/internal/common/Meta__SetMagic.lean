module
public import Spec.go_etcd_io.bbolt.internal.common.Meta__SetMagic

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

theorem Meta.SetMagic.wp_proof : Meta.SetMagic.spec (GF := GF) (hG := hG) := by
  intro l v x
  wp_start as Hl
  wp_auto
  iapply HΦ; iframe

end proof

end bbolt
end EtcdGrove
end Perennial
