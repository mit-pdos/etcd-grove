/-
**Trust boundary**: `zap.Uint` returns a field (an axiom; see `Spec/go_uber_org/zap/Uint.lean`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_uber_org.zap.Uint

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

/-- **Trust boundary**: `zap.Uint` returns a field. -/
axiom zap.Uint.wp_proof : zap.Uint.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
