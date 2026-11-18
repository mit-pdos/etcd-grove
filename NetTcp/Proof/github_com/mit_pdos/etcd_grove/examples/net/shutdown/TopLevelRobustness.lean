/- Lean-first (no Rocq counterpart).

# `net/shutdown`: the top-level robustness result, proved

`shutdown_crash_robust`, stated in
`NetTcp/Spec/github_com/mit_pdos/etcd_grove/examples/net/shutdown/TopLevelRobustness.lean`,
from the example's closed theorem (`Results.lean`).
-/
module

public import NetTcp.Spec.github_com.mit_pdos.etcd_grove.examples.net.shutdown.TopLevelRobustness
public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.shutdown.Results

@[expose] public section

noncomputable section

set_option linter.iris.style.nameCheck false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Tcp

open github_com.mit_pdos.etcd_grove.examples.net.wire (addrInv)

namespace github_com.mit_pdos.etcd_grove.examples.net.shutdown

attribute [local instance] tcpExts tcpExtsSemantics tcpExtsInterp tcpExts_hasTcp
  tcpExtsCrashInterp

attribute [local instance] GooseGlobalGS.gooseInvGS

section adequacy

variable [GoGlobalContext] {GF : BundledGFunctors}

/-- `shutdown_crash_robust.spec`
(`NetTcp/Spec/github_com/mit_pdos/etcd_grove/examples/net/shutdown/TopLevelRobustness.lean`). -/
theorem shutdown_crash_robust : shutdown_crash_robust.spec := by
  intro lctx sem package_sem field_sem _ σ0 g h Hhost Hplan pl Hwf Hpl Hconns bound
  refine Robustness.Robust.of_all fun hf n κs c Hsteps _ i tp σ hi => ?_
  have hfresh : ∀ σ', (∃ e, (e, σ') ∈ system σ0) → NodeStart lctx σ' := fun σ' ⟨e, he⟩ =>
    ⟨(hf (e, σ') he).1, (hf (e, σ') he).2.1, (hf (e, σ') he).2.2⟩
  exact (shutdown_crash_safety
      σ0 g h (hfresh σ0 ⟨boot_node, by simp [system]⟩) Hhost Hplan pl Hwf Hpl Hconns n κs c Hsteps i tp σ hi).2

end adequacy
end github_com.mit_pdos.etcd_grove.examples.net.shutdown
end Perennial

end
