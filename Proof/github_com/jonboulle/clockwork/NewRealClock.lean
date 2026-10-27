/-
The trust boundary: `clockwork.NewRealClock()` (names only). Lean-first (no Rocq counterpart); the
spec-first pilot (`notes/compactor-pilot-plan.md`): why the statement is true of clockwork v0.5.0
is in `Proof/github_com/jonboulle/clockwork/Defs.lean`'s header.
-/
module

public import Spec.github_com.jonboulle.clockwork.NewRealClock

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.jonboulle.clockwork.Assumptions]

axiom clockwork.NewRealClock.wp_proof : clockwork.NewRealClock.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
