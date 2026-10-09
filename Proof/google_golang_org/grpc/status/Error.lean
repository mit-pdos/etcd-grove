/-
grpc's `status.Error` is not translated (see the spec): an axiom. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.google_golang_org.grpc.status.Error

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- grpc is not translated; see the comment at the spec. -/
axiom status.Error.wp_proof : status.Error.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
