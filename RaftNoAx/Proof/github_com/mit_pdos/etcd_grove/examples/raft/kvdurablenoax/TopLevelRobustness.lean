-- The copy for the part `RaftNoAx/` of `Proof/github_com/mit_pdos/etcd_grove/examples/raft/kvdurable/TopLevelRobustness.lean` (etc/copy-part.py; rerun it, do not edit).
/- Lean-first (no Rocq counterpart).

# `raft/kvdurable`: the top-level robustness results, proved

`raft_kvdurable_porcupine_robust`, `raft_kvdurableN_porcupine_robust`, stated in
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvdurablenoax/TopLevelRobustness.lean`,
from the example's closed theorems (`Results.lean`).
-/
module

public import RaftNoAx.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvdurablenoax.TopLevelRobustness
public import RaftNoAx.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvdurablenoax.Results

@[expose] public section

noncomputable section

set_option pp.fullNames true

set_option linter.unusedSectionVars false

namespace Perennial

namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section closed

attribute [local instance] durableExts durableExtsSemantics durableExtsInterp durableExts_hasExt

variable [go_gctx : GoGlobalContext]

/-- `raft_kvdurable_porcupine_robust.spec`
(`Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvdurablenoax/TopLevelRobustness.lean`). -/
theorem raft_kvdurable_porcupine_robust : raft_kvdurable_porcupine_robust.spec := by
  intro lctx sem package_sem hLog dir σ g Hfiles
  exact
    Robustness.Robust.of_single fun hf n κs t2 σ2 hn Hsteps =>
      (raft_kvdurable_porcupine_safe
        dir σ g hf.1 hf.2.1 hf.2.2 Hfiles n (by omega) κs t2 σ2 Hsteps).2

/-- `raft_kvdurableN_porcupine_robust.spec`
(`Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvdurablenoax/TopLevelRobustness.lean`). -/
theorem raft_kvdurableN_porcupine_robust : raft_kvdurableN_porcupine_robust.spec := by
  intro lctx sem package_sem hLog dir k σ g Hfiles
  exact
    Robustness.Robust.of_single fun hf n κs t2 σ2 hn Hsteps =>
      (raft_kvdurableN_porcupine_safe
        dir k σ g hf.1 hf.2.1 hf.2.2 Hfiles n (by omega) κs t2 σ2 Hsteps).2

end closed
end EtcdGrove
end Perennial

end
