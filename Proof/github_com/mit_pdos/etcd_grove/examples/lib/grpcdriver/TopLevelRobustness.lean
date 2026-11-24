/- Lean-first (no Rocq counterpart).

# `lib/grpcdriver`: the top-level robustness result, proved

`grpcdriver_robust`, stated in
`Spec/github_com/mit_pdos/etcd_grove/examples/lib/grpcdriver/TopLevelRobustness.lean`, through the
all-stable bridge with `Robust`'s thread bound (`robust_of_distBootIT`, `Net/Statement/DistBridgeExts.lean`,
at `netExts`). Skeleton: the proof is to come.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.TopLevelRobustness
public import Net.Statement.DistBridgeExts

@[expose] public section

noncomputable section

set_option linter.iris.style.nameCheck false

namespace Perennial

open Iris Iris.BI Net

namespace github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver

theorem grpcdriver_robust : grpcdriver_robust.spec := by
  sorry

end github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver
end Perennial

#print axioms Perennial.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.grpcdriver_robust
