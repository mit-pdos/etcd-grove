/-
The trust boundary: `jwt.Parse` (`github.com/golang-jwt/jwt/v5` is names-only; PR etcd#21909).
-/
module

public import Spec.github_com.golang_jwt.jwt.v5.Parse

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI jwt

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **Trust boundary**: `jwt.Parse` returns an error or a parsed token whose claims, when a
`MapClaims`, are a read-only map of JSON values. -/
axiom jwt.Parse.wp_proof : jwt.Parse.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
