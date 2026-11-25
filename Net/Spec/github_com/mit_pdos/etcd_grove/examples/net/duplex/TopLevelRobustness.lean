/- Lean-first (no Rocq counterpart).

# `net/duplex`: the top-level robustness result, stated

`duplex_crash_robust`: the example's closed theorem as an instance of the generic robustness statement
(`Robustness/Statement.lean`, `Robust crashing stable g threads bound`: in every execution of the
machines that may crash and restart and of those that never crash, each a fresh Go process, of
fewer than `bound` steps along which every machine keeps fewer than `threads` threads,
no thread is stuck and none has an unrecovered panic). This file only
states it (to audit); the proof is in
`Net/Proof/github_com/mit_pdos/etcd_grove/examples/net/duplex/TopLevelRobustness.lean`.
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.duplex.TopLevelDefs

@[expose] public section

noncomputable section

set_option linter.iris.style.nameCheck false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.mit_pdos.etcd_grove.examples.net.duplex

attribute [local instance] netExts netExtsSemantics netExtsInterp netExts_hasNet
  netExtsCrashInterp

attribute [local instance] GooseGlobalGS.gooseInvGS

section adequacy

variable [GoGlobalContext] {GF : BundledGFunctors}

/-- **`duplex_crash_safety` as a robustness statement** (`Robustness.Robust`,
`Robustness/Statement.lean`): the system's machines, each of which may crash at any step and
restart, each a fresh Go process (`Robust`'s premise), under `duplex_crash_safety`'s other
hypotheses: in every execution, of any length, no thread of any machine is stuck and none has an
unrecovered panic. -/
def duplex_crash_robust.spec : Prop :=
  ∀ [lctx : GoLocalContext] [sem : go.Semantics] [server_sem : cmd.server.Assumptions]
    [client_sem : cmd.client.Assumptions] [field_sem : net.FieldAssumptions]
    (σs σc : state) (g : GlobalState) (bound : Nat),
    Robustness.Robust (system σs σc) [] g (threads := bound + 1) (bound := bound)

end adequacy
end github_com.mit_pdos.etcd_grove.examples.net.duplex
end Perennial

end
