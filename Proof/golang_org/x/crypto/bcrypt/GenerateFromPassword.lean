/-
The trust boundary: `bcrypt.GenerateFromPassword` (names only: password hashing is out of the
auth plan's scope, D-AU6; the auth plan's E2x, 2026-10-26).
-/
module

public import Spec.golang_org.x.crypto.bcrypt.GenerateFromPassword

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

axiom bcrypt.GenerateFromPassword.wp_proof : bcrypt.GenerateFromPassword.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
