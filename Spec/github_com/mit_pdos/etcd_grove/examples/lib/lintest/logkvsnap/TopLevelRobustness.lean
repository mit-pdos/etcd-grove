/- Lean-first (no Rocq counterpart).

# `lib/lintest/logkvsnap`: the top-level robustness result, stated

`logkvsnap_robust`: the example's closed theorem as an instance of the generic robustness statement
(`Robustness/Statement.lean`, `Robust crashing stable g bound`: in every execution of the
machines that may crash and restart and of those that never crash, each a fresh Go process, of
fewer than `bound` steps, no thread is stuck and none has an unrecovered panic). This file only
states it (to audit); the proof is in
`Proof/github_com/mit_pdos/etcd_grove/examples/lib/lintest/logkvsnap/TopLevelRobustness.lean`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.lintest.logkvsnap.TopLevelDefs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

namespace EtcdGrove

namespace lintest

namespace logkvsnap

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

attribute [local instance] trivialExts trivialExtsSemantics trivialExtsInterp trivialExts_hasExt

section adequacy

variable [go_gctx : GoGlobalContext]

/-- **`logkvsnap_adequate` as a robustness statement** (`Robustness.Robust`,
`Robustness/Statement.lean`): the program alone on one machine that never crashes,
a fresh Go process (`Robust`'s premise), under `logkvsnap_adequate`'s other hypotheses: in every
execution of fewer than `2 ^ 63` steps no thread is stuck and none has an unrecovered panic. -/
def logkvsnap_robust.spec : Prop :=
  ∀ [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.lintest.logkvsnap.Assumptions]
    (σ : state) (g : GlobalState),
    Robustness.Robust [] [(logkvsnapProgram, σ)] g (2 ^ 63)

end adequacy
end logkvsnap
end lintest
end EtcdGrove
end Perennial

end
