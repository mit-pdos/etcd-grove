/- Lean-first (no Rocq counterpart).

# `net/shutdown`: the top-level robustness result, proved

`shutdown_crash_robust`, stated in
`Net/Spec/github_com/mit_pdos/etcd_grove/examples/net/shutdown/TopLevelRobustness.lean`,
from the example's closed theorem (`Results.lean`).
-/
module

public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.net.shutdown.TopLevelRobustness
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.shutdown.Results

@[expose] public section

noncomputable section

set_option linter.iris.style.nameCheck false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

open github_com.mit_pdos.etcd_grove.examples.net.wire (addrInv)

namespace github_com.mit_pdos.etcd_grove.examples.net.shutdown

attribute [local instance] netExts netExtsSemantics netExtsInterp netExts_hasNet
  netExtsCrashInterp

attribute [local instance] GooseGlobalGS.gooseInvGS

section adequacy

variable [GoGlobalContext] {GF : BundledGFunctors}

/-- `shutdown_crash_robust.spec`
(`Net/Spec/github_com/mit_pdos/etcd_grove/examples/net/shutdown/TopLevelRobustness.lean`). -/
theorem shutdown_crash_robust : shutdown_crash_robust.spec := by
  intro lctx sem package_sem σ0 g bound hf hig
  -- `Robust`'s premise `extsInitGlobal g` is, for `netExts = [netExt]`, no connection
  -- (`NetGlobal.init`, `GooseLang/Ext/Net/Impl.lean`)
  have Hconns : (extGlobal netExt g.globalWorld).conns = ∅ := hig.1
  revert hf hig
  refine Robustness.Robust.of_all fun hf n κs c Hsteps _ i tp σ hi => ?_
  have hfresh : ∀ σ', (∃ e, (e, σ') ∈ system σ0) → NodeStart lctx σ' := fun σ' ⟨e, he⟩ =>
    ⟨(hf (e, σ') he).1, (hf (e, σ') he).2.1, (hf (e, σ') he).2.2⟩
  exact (shutdown_crash_safety
      σ0 g (hfresh σ0 ⟨boot_node, by simp [system]⟩)
      Hconns n κs c Hsteps i tp σ hi).2

end adequacy
end github_com.mit_pdos.etcd_grove.examples.net.shutdown
end Perennial

end
