module
public import Spec.go_etcd_io.bbolt.internal.common.UnsafeAdd

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

theorem UnsafeAdd.wp_proof : UnsafeAdd.spec (GF := GF) (hG := hG) := by
  intro base offset
  wp_start
  wp_auto
  wp_func_call
  wp_auto
  iapply HΦ; itrivial

end proof

end bbolt
end EtcdGrove
end Perennial
