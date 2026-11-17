/-
The trust boundary: `fmt.Sprintf` of the WAL's segment names, `%016x` (beyond Perennial's model of
`Sprintf`, whose output there is arbitrary; see `Spec/fmt/SprintfWalName.lean`). To be replaced by
a proof once Perennial's model formats `%0Nx`. **Pending the user's review** (WAL leaf specs,
2026-11-13).
-/
module

public import Spec.fmt.SprintfWalName

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

axiom fmt.SprintfWalName.wp_proof : fmt.SprintfWalName.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
