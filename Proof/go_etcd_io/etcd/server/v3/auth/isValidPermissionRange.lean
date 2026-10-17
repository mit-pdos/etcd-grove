/-
The trust boundary: `isValidPermissionRange` (names only; PR etcd#21845, `pr-verify/etcd-21845`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.isValidPermissionRange

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.auth

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

axiom auth.isValidPermissionRange.wp_proof : auth.isValidPermissionRange.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
