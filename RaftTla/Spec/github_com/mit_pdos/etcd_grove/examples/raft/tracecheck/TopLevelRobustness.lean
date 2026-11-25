/- Lean-first (no Rocq counterpart).

# `raft/tracecheck`: the top-level robustness result, stated

`raft_tracecheck_robust`: the example's closed theorem as an instance of the generic robustness statement
(`Robustness/Statement.lean`, `Robust crashing stable g threads bound`: in every execution of the
machines that may crash and restart and of those that never crash, each a fresh Go process, of
fewer than `bound` steps along which every machine keeps fewer than `threads` threads,
no thread is stuck and none has an unrecovered panic). This file only
states it (to audit); the proof is in
`RaftTla/Proof/github_com/mit_pdos/etcd_grove/examples/raft/tracecheck/TopLevelRobustness.lean`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.TopLevelDefs
public import RaftTla.Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.TopLevelDefs
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
execution of fewer than `2 ^ 61 - 5` steps along which fewer than `2 ^ 31` threads are live, no
thread is stuck and none has an unrecovered panic. (2026-11-24) `Main` draws the number of voters, `1 + below(5)` (until then three), and the
bootstrap log of `nv` voters is `tracecheck.bootLog nv`, the bytes Go computes (until then a premise
`boot` with its pure facts `tracecheck.BootLogFacts boot`, unprovable while the decoder was opaque);
`proto.Marshal`'s contract at its conf changes, at each size `Main` can draw, follows from the
trust-boundary axiom `proto.MarshalBootConfChange.wp_proof` (`tracecheck.premises_of_spec`; premises to
axioms, 2026-11-24: until then a premise, `Hprem`). -/
def raft_tracecheck_robust.spec : Prop :=
  ∀ [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Assumptions]
    [hLog : log.NewModel]
    (σ : state) (g : GlobalState),
    Robustness.Robust [] [(tracecheckProgram, σ)] g (threads := 2 ^ 31)
      (bound := 2 ^ 61 - 5)

end closed
end EtcdGrove
end Perennial

end
