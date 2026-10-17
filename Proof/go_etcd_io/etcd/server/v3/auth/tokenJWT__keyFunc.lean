/-
The trust boundary: `tokenJWT.keyFunc` (names only; see its spec). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.tokenJWT__keyFunc

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.auth auth

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- **Trust boundary**: the JWT provider's key function returns (names only: the crypto key
types are not translated). -/
axiom auth.tokenJWT.keyFunc.wp_proof : auth.tokenJWT.keyFunc.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
