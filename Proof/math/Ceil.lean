/-
The trust boundary: `math.Ceil(x)`: Perennial translates `math` but specifies no float operation. Lean-first (no Rocq counterpart); the
server-construction unit, stage N0 (2026-10-16), for `NewServer`.
-/
module

public import Spec.math.Ceil

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

axiom math.Ceil.wp_proof : math.Ceil.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
