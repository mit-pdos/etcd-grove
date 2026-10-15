/-
The trust boundary: `redactToken` (names only: `crypto/sha256`, `encoding/hex`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.redactToken

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

axiom auth.redactToken.wp_proof : auth.redactToken.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
