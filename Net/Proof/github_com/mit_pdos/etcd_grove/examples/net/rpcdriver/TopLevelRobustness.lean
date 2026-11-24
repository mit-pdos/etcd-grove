/- Lean-first (no Rocq counterpart).

# `net/rpcdriver`: the top-level robustness result, proved

`rpcdriver_robust`, stated in
`Net/Spec/github_com/mit_pdos/etcd_grove/examples/net/rpcdriver/TopLevelRobustness.lean`.
A skeleton for now (2026-11-24): the proof goes through the distributed bridge
(`robust_of_distBoot`, `Net/Statement/DistBridge.lean`), as echo's `echo_dist_robust`, over the
proved specs of net/rpc (`Net/Proof/net/rpc`), once the server side over HTTP (`HandleHTTP`,
`http.Serve`) and the driver's own specs are proved (notes/library-drivers.md).
-/
module

public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.TopLevelRobustness
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.cmd.server.PkgTable
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.cmd.client.PkgTable

@[expose] public section

noncomputable section

set_option linter.iris.style.nameCheck false

namespace Perennial

open Iris Iris.BI Net

namespace github_com.mit_pdos.etcd_grove.examples.net.rpcdriver

/-- `rpcdriver_robust.spec`
(`Net/Spec/github_com/mit_pdos/etcd_grove/examples/net/rpcdriver/TopLevelRobustness.lean`). -/
theorem rpcdriver_robust : rpcdriver_robust.spec := by
  sorry

end github_com.mit_pdos.etcd_grove.examples.net.rpcdriver
end Perennial
