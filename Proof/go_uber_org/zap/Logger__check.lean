/-
The trust boundary: `zap.Logger.check` (unexported; zap's cores, encoders and clocks are not
translated). Until 2026-11-20 the boundary was the five exported methods over it (`Check`, `Debug`,
`Info`, `Warn`, `Error`), proved from it since.
-/
module

public import Spec.go_uber_org.zap.Logger__check

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

axiom zap.Logger.check.wp_proof : zap.Logger.check.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
