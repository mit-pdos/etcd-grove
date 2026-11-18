/- Lean-first (no Rocq counterpart).

# `goose/prophkv`: the top-level robustness result, proved

`goose_prophkv_robust`, stated in
`Spec/github_com/mit_pdos/etcd_grove/examples/goose/prophkv/TopLevelRobustness.lean`,
from the example's closed theorem (`Results.lean`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.goose.prophkv.TopLevelRobustness

@[expose] public section

noncomputable section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace EtcdGrove

namespace goose_prophkv

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

open github_com.mit_pdos.etcd_grove.examples.goose.prophkv

attribute [local instance] trivialExts trivialExtsSemantics trivialExtsInterp

section program

variable [go_gctx : GoGlobalContext]

/-- `goose_prophkv_robust.spec`
(`Spec/github_com/mit_pdos/etcd_grove/examples/goose/prophkv/TopLevelRobustness.lean`). -/
theorem goose_prophkv_robust : goose_prophkv_robust.spec := by
  intro lctx sem package_sem σ g bound
  exact
    Robustness.Robust.of_single fun hf n κs t2 σ2 _ Hsteps =>
      (goose_prophkv_safe
        σ g hf.1 hf.2.1 hf.2.2 n κs t2 σ2 Hsteps).2

end program
end goose_prophkv
end EtcdGrove
end Perennial

end
