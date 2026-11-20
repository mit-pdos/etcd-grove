/- Lean-first (no Rocq counterpart).

# `k8s/authz`: the top-level robustness result, stated

`k8s_authz_robust`: the closed theorem of Kubernetes' conditional authorization (KEP-5681) driven by
arbitrary leaf authorizers, as an instance of the generic robustness statement
(`Robustness/Statement.lean`, `Robust crashing stable g threads bound`: in every execution of the machines
that may crash and restart and of those that never crash, each a fresh Go process, of fewer than
`bound` steps, no thread is stuck and none has an unrecovered panic). The program
(`TopLevelDefs.lean`'s `authzProgram`) is the driver's initialization then `Main()`, which panics
unless (C1) the phase-2 decision is Allow, Deny or NoOpinion, (C2) it is one of phase 1's possible
decisions, and (C3) a non-Allow phase-1 decision's failure decision is one of its possible
decisions, for every behaviour of the leaves (each choice a `rand.Int63n`). This file only states
it (to audit); the proof is in
`Proof/github_com/mit_pdos/etcd_grove/examples/k8s/authz/TopLevelRobustness.lean`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.authz.TopLevelDefs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

namespace EtcdGrove

namespace k8s_authz

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

attribute [local instance] trivialExts trivialExtsSemantics trivialExtsInterp trivialExts_hasExt

section program

variable [go_gctx : GoGlobalContext]

/-- **Conditional authorization is robust** (`Robustness.Robust`, `Robustness/Statement.lean`): the
driver's program alone on one machine that never crashes, a fresh Go process (`Robust`'s premise),
for any Go semantics and package assumptions (the translated bodies behind the driver's, the
authorizer's, the union's and their imports' names): in every execution of fewer than `bound`
steps no thread is stuck and none has an unrecovered panic, so C1-C3 hold (`Main` panics
otherwise). -/
def k8s_authz_robust.spec : Prop :=
  ∀ [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.authz.Assumptions]
    (σ : state) (g : GlobalState) (bound : Nat),
    Robustness.Robust [] [(authzProgram, σ)] g (threads := bound + 1) (bound := bound)

end program
end k8s_authz
end EtcdGrove
end Perennial

end
