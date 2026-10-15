/-
The trust boundary: `storage.NewBackendQuota` (`server/v3/storage` is names-only).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.NewBackendQuota

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

axiom storage.NewBackendQuota.wp_proof : storage.NewBackendQuota.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
