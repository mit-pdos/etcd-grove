/-
The trust boundary: `zap.Bool` (`go.uber.org/zap` is names-only).
-/
module

public import Spec.go_uber_org.zap.Bool

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_uber_org

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

axiom zap.Bool.wp_proof : zap.Bool.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
