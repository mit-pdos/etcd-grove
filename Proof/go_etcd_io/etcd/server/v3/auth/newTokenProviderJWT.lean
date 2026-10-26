/-
The trust boundary: `auth.newTokenProviderJWT(lg, optMap)` (`jwt.go`): names-only (its options'
and keys' parsing: `crypto`, `golang-jwt`). Lean-first (no Rocq counterpart); the auth plan's E2g
(2026-10-25), in place of `NewTokenProvider`'s axiom: why the statement is true of the Go code is in
its spec's docstring.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.newTokenProviderJWT

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
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

axiom auth.newTokenProviderJWT.wp_proof : auth.newTokenProviderJWT.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
