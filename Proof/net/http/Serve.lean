/-
Trust boundary: `http.Serve` of a member's raft handler (an axiom; D21 stage M5, the user's (A);
why it is true of the Go code: `Spec/net/http/Serve.lean`).
-/
module

public import Spec.net.http.Serve

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

axiom net.http.Serve.wp_proof : net.http.Serve.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
