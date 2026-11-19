/- Lean-first (no Rocq counterpart).

# `raft/tracecheck`: the top-level robustness result, proved

`raft_tracecheck_robust`, stated in
`RaftTla/Spec/github_com/mit_pdos/etcd_grove/examples/raft/tracecheck/TopLevelRobustness.lean`,
from the example's closed theorem (`Results.lean`): an execution of fewer than `2^31 - 1` steps from
one thread has fewer than `2^31` threads live throughout (`RealNstepsBelow.of_one`). `Robust` has no
thread bound of its own, so the step bound stays the thread bound's.
-/
module

public import RaftTla.Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.TopLevelRobustness
public import RaftTla.Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Results

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

/-- `raft_tracecheck_robust.spec`
(`RaftTla/Spec/github_com/mit_pdos/etcd_grove/examples/raft/tracecheck/TopLevelRobustness.lean`). -/
theorem raft_tracecheck_robust : raft_tracecheck_robust.spec := by
  intro lctx sem package_sem hLog boot Hbf Hprem σ g
  exact
    Robustness.Robust.of_single fun hf n κs t2 σ2 hn Hsteps =>
      (raft_tracecheck_safe
        boot Hbf Hprem σ g hf.1 hf.2.1 hf.2.2 n (by omega) κs t2 σ2
        ((RealNstepsBelow.of_one Hsteps hf.2.2).mono (by omega))).2

end closed
end EtcdGrove
end Perennial

end
