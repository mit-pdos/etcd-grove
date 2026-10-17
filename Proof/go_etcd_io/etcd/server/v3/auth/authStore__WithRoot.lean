/-
The trust boundary: `authStore.WithRoot` (`server/auth/store.go`; names only).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__WithRoot

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.auth auth

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

axiom auth.authStore.WithRoot.wp_proof : auth.authStore.WithRoot.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
