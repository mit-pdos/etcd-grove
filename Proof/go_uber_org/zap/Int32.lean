/-
The trust boundary: `zap.Int32` (names-only).
-/
module

public import Spec.go_uber_org.zap.Int32

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

axiom zap.Int32.wp_proof : zap.Int32.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
