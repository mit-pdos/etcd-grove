/- Lean-first (no Rocq counterpart).

# `k8s/smd`: the top-level robustness result, stated

`smd_driver_robust`: structured-merge-diff's driver (`examples/k8s/smd`, `Main`: nine server-side
apply and update steps through `merge.Updater.Apply`/`Update`, each checked against the expected
object, managed fields and conflicts, with a panic on any difference) as an instance of the generic
robustness statement (`Robustness/Statement.lean`, `Robust crashing stable g bound`: in every
execution of the machines, each a fresh Go process, of fewer than `bound` steps, no thread is stuck
and none has an unrecovered panic). Here one machine that never crashes runs the program
(`smdProgram`: the package's initialization, then `Main()`), at any bound, so no check of `Main`
ever fails. This file only states it (to audit); the proof is in
`Proof/github_com/mit_pdos/etcd_grove/examples/k8s/smd/TopLevelRobustness.lean`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.smd.TopLevelDefs

@[expose] public section

noncomputable section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace EtcdGrove

namespace k8s_smd

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

attribute [local instance] trivialExts trivialExtsSemantics trivialExtsInterp

section program

variable [go_gctx : GoGlobalContext]

/-- **The structured-merge-diff driver never fails a check** (`Robustness.Robust`): the program
alone on one machine that never crashes, a fresh Go process (`Robust`'s premise), for any Go
semantics and package assumptions (the translated bodies of the driver, SMD and the standard
library): in every execution of fewer than `bound` steps, for every `bound`, no thread is stuck
and none has an unrecovered panic. -/
def smd_driver_robust.spec : Prop :=
  ∀ [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.smd.Assumptions] (σ : state) (g : GlobalState) (bound : Nat),
    Robustness.Robust [] [(smdProgram, σ)] g bound

end program
end k8s_smd
end EtcdGrove
end Perennial

end
