module
public import Spec.go_etcd_io.bbolt.internal.freelist.shared__pendingPageIds

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.freelist

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

theorem shared.pendingPageIds.wp_proof : shared.pendingPageIds.spec (GF := GF) (hG := hG) := by
  intro s sv dq
  wp_start as Hs
  wp_auto
  iapply HΦ; iframe

end proof

end bbolt
end EtcdGrove
end Perennial
