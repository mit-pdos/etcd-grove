/-
The trust boundary: `bcrypt.CompareHashAndPassword` (names only: password hashing is out of the
auth plan's scope, D-AU6; the auth plan's E2j, 2026-10-26).
-/
module

public import Spec.golang_org.x.crypto.bcrypt.CompareHashAndPassword

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

axiom bcrypt.CompareHashAndPassword.wp_proof : bcrypt.CompareHashAndPassword.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
