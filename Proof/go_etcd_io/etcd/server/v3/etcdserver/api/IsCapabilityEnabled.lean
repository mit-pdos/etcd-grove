/-
The trust boundary: `api.IsCapabilityEnabled` (`etcdserver/api` is names-only; unit P3b).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.IsCapabilityEnabled

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

axiom api.IsCapabilityEnabled.wp_proof : api.IsCapabilityEnabled.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
