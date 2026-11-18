/- Lean-first (no Rocq counterpart).

# `raft/tracecheck`: the top-level robustness result, stated

`raft_tracecheck_robust`: the example's closed theorem as an instance of the generic robustness statement
(`Robustness/Statement.lean`, `Robust crashing stable g bound`: in every execution of the
machines that may crash and restart and of those that never crash, each a fresh Go process, of
fewer than `bound` steps, no thread is stuck and none has an unrecovered panic). This file only
states it (to audit); the proof is in
`RaftTla/Proof/github_com/mit_pdos/etcd_grove/examples/raft/tracecheck/TopLevelRobustness.lean`.
-/
module

public import RaftTla.Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Results
public import Robustness.Statement

@[expose] public section

noncomputable section

set_option pp.fullNames true

set_option linter.unusedSectionVars false

namespace Perennial

namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 TraceCheck

section closed

attribute [local instance] trivialExts trivialExtsSemantics trivialExtsInterp trivialExts_hasExt

variable [go_gctx : GoGlobalContext]

/-- **`raft_tracecheck_safe` as a robustness statement** (`Robustness.Robust`,
`Robustness/Statement.lean`): the program alone on one machine that never crashes,
a fresh Go process (`Robust`'s premise), under `raft_tracecheck_safe`'s other hypotheses: in every
execution of fewer than `2 ^ 31 - 1` steps no thread is stuck and none has an unrecovered panic. -/
def raft_tracecheck_robust.spec : Prop :=
  ∀ [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Assumptions]
    [hLog : log.NewModel] (boot : List LogEntry) (Hbf : tracecheck.BootLogFacts boot)
    (Hprem : ∀ hG : HeapGS .hasLC tcGF,
      ⊢ tracecheck.premises (GF := tcGF) (hG := heapWith hG lctx) boot)
    (σ : state) (g : GlobalState),
    Robustness.Robust [] [(tracecheckProgram, σ)] g (2 ^ 31 - 1)

end closed
end EtcdGrove
end Perennial

end
