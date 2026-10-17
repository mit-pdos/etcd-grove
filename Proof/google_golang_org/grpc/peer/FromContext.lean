/-
**Trust boundary**: `peer.FromContext` returns the context's peer (an axiom; see
`Spec/google_golang_org/grpc/peer/FromContext.lean`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.google_golang_org.grpc.peer.FromContext

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

axiom peer.FromContext.wp_proof : peer.FromContext.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
