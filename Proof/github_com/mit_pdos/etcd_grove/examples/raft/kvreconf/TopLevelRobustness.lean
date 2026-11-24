/- Lean-first (no Rocq counterpart).

# `raft/kvreconf`: the top-level robustness results, proved

`raft_kvreconf_porcupine_robust`, `raft_kvreconfN_porcupine_robust`, stated in
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvreconf/TopLevelRobustness.lean`,
from the example's closed theorems (`Results.lean`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvreconf.TopLevelRobustness
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvreconf.Results

@[expose] public section

noncomputable section

set_option pp.fullNames true

set_option linter.unusedSectionVars false

namespace Perennial

namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section closed

attribute [local instance] trivialExts trivialExtsSemantics trivialExtsInterp trivialExts_hasExt

variable [go_gctx : GoGlobalContext]

/-- `raft_kvreconf_porcupine_robust.spec`
(`Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvreconf/TopLevelRobustness.lean`). -/
theorem raft_kvreconf_porcupine_robust : raft_kvreconf_porcupine_robust.spec := by
  intro lctx sem package_sem hLog σ g
  exact
    Robustness.Robust.of_single fun hf n κs t2 σ2 hn Hsteps =>
      (raft_kvreconf_porcupine_safe
        σ g hf.1 hf.2.1 hf.2.2 n (by omega) κs t2 σ2 Hsteps).2

/-- `raft_kvreconfN_porcupine_robust.spec`
(`Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvreconf/TopLevelRobustness.lean`). -/
theorem raft_kvreconfN_porcupine_robust : raft_kvreconfN_porcupine_robust.spec := by
  intro lctx sem package_sem hLog k σ g
  exact
    Robustness.Robust.of_single fun hf n κs t2 σ2 hn Hsteps =>
      (raft_kvreconfN_porcupine_safe
        k σ g hf.1 hf.2.1 hf.2.2 n (by omega) κs t2 σ2 Hsteps).2

end closed
end EtcdGrove
end Perennial

end
