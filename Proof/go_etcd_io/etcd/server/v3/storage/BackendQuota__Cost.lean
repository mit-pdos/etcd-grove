/-
The trust boundary: `storage.BackendQuota.Cost` (`server/v3/storage` is names-only).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.BackendQuota__Cost

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
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

axiom storage.BackendQuota.Cost.wp_proof : storage.BackendQuota.Cost.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
