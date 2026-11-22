/- Lean-first (no Rocq counterpart).

# `lib/lintest/logkvrw`: the top-level robustness result, stated

`logkvrw_robust`: the example's closed theorem as an instance of the generic robustness statement
(`Robustness/Statement.lean`, `Robust crashing stable g threads bound`: in every execution of the
machines that may crash and restart and of those that never crash, each a fresh Go process, of
fewer than `bound` steps along which every machine keeps fewer than `threads` threads,
no thread is stuck and none has an unrecovered panic). This file only
states it (to audit); the proof is in
`Proof/github_com/mit_pdos/etcd_grove/examples/lib/lintest/logkvrw/TopLevelRobustness.lean`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.lintest.logkvrw.TopLevelDefs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

namespace EtcdGrove

namespace lintest

namespace logkvrw

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

attribute [local instance] trivialExts trivialExtsSemantics trivialExtsInterp trivialExts_hasExt

section adequacy

variable [go_gctx : GoGlobalContext]

/-- **`logkvrw_adequate` as a robustness statement** (`Robustness.Robust`,
`Robustness/Statement.lean`): the program alone on one machine that never crashes,
a fresh Go process (`Robust`'s premise), under `logkvrw_adequate`'s other hypotheses: in every
execution of fewer than `2 ^ 63` steps along which fewer than `2 ^ 30` threads are live (the server's
`RWMutex` readers), no thread is stuck and none has an unrecovered panic. -/
def logkvrw_robust.spec : Prop :=
  ∀ [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.lintest.logkvrw.Assumptions]
    (σ : state) (g : GlobalState),
    Robustness.Robust [] [(logkvrwProgram, σ)] g (threads := 2 ^ 30)
      (bound := 2 ^ 63)

end adequacy
end logkvrw
end lintest
end EtcdGrove
end Perennial

end
