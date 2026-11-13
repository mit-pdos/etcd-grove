/-
The trust boundary: `fmt.Sscanf` of the WAL's segment names (names-only in Perennial; see
`Spec/fmt/SscanfWalName.lean`). **Pending the user's review** (WAL leaf specs, 2026-11-13).
-/
module

public import Spec.fmt.SscanfWalName

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
variable [package_sem : _root_.Perennial.fmt.Assumptions]

axiom fmt.SscanfWalName.wp_proof : fmt.SscanfWalName.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
