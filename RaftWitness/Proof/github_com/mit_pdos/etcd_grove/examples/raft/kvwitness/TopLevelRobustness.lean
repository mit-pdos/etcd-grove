/- Lean-first (no Rocq counterpart).

# `raft/kvwitness`: the top-level robustness results, proved

`kv_porcupine_robust`, `raft_kvwitness_porcupine_robust`, stated in
`RaftWitness/Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvwitness/TopLevelRobustness.lean`,
from the example's closed theorems (`Results.lean`).
-/
module

public import RaftWitness.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvwitness.TopLevelRobustness

@[expose] public section

noncomputable section

set_option pp.fullNames true

set_option linter.unusedSectionVars false

namespace Perennial

namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section closed

attribute [local instance] trivialExts trivialExtsSemantics trivialExtsInterp

variable [go_gctx : GoGlobalContext]

/-- `kv_porcupine_robust.spec`
(`RaftWitness/Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvwitness/TopLevelRobustness.lean`). -/
theorem kv_porcupine_robust : kv_porcupine_robust.spec := by
  intro lctx sem package_sem hLog σ g
  exact
    Robustness.Robust.of_single fun hf n κs t2 σ2 hn Hsteps =>
      (kv_porcupine_safe
        σ g hf.1 hf.2.1 hf.2.2 n (by omega) κs t2 σ2 Hsteps).2

/-- `raft_kvwitness_porcupine_robust.spec`
(`RaftWitness/Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvwitness/TopLevelRobustness.lean`). -/
theorem raft_kvwitness_porcupine_robust : raft_kvwitness_porcupine_robust.spec := by
  intro lctx sem package_sem hLog σ g
  exact
    Robustness.Robust.of_single fun hf n κs t2 σ2 hn Hsteps =>
      (raft_kvwitness_porcupine_safe
        σ g hf.1 hf.2.1 hf.2.2 n (by omega) κs t2 σ2 Hsteps).2

end closed
end EtcdGrove
end Perennial

end
