/-
The trust boundary: `zap.Logger.Sugar` (`go.uber.org/zap` is names-only).
-/
module

public import Spec.go_uber_org.zap.Logger__Sugar

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_uber_org

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

axiom zap.Logger.Sugar.wp_proof : zap.Logger.Sugar.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
