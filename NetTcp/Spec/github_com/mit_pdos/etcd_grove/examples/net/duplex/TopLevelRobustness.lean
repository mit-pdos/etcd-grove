/- Lean-first (no Rocq counterpart).

# `net/duplex`: the top-level robustness result, stated

`duplex_crash_robust`: the example's closed theorem as an instance of the generic robustness statement
(`Robustness/Statement.lean`, `Robust crashing stable g bound`: in every execution of the
machines that may crash and restart and of those that never crash, each a fresh Go process, of
fewer than `bound` steps, no thread is stuck and none has an unrecovered panic). This file only
states it (to audit); the proof is in
`NetTcp/Proof/github_com/mit_pdos/etcd_grove/examples/net/duplex/TopLevelRobustness.lean`.
-/
module

public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.duplex.Results
public import Robustness.Statement

@[expose] public section

noncomputable section

set_option linter.iris.style.nameCheck false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Tcp

namespace github_com.mit_pdos.etcd_grove.examples.net.duplex

attribute [local instance] tcpExts tcpExtsSemantics tcpExtsInterp tcpExts_hasTcp
  tcpExtsCrashInterp

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
    [client_sem : cmd.client.Assumptions] [field_sem : net.FieldAssumptions] [go.BasicIntoValInj]
    (σs σc : state) (g : GlobalState) (h : GoString) (Hhost : (extLocal tcpExt σs.world).host = h)
    (Hplan : (extGlobal tcpExt g.globalWorld).plan.lookup srvAddr = some h)
    (pl : List (GoString × GoString)) (Hwf : PlanWellFormed pl)
    (Hpl : (extGlobal tcpExt g.globalWorld).plan = GMap.ofList pl)
    (Hconns : (extGlobal tcpExt g.globalWorld).conns = ∅) (bound : Nat),
    Robustness.Robust (system σs σc) [] g bound

end adequacy
end github_com.mit_pdos.etcd_grove.examples.net.duplex
end Perennial

end
