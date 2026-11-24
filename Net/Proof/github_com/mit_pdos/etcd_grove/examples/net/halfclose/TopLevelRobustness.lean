/- Lean-first (no Rocq counterpart).

# `net/halfclose`: the top-level robustness result, proved

`halfclose_crash_robust`, stated in
`Net/Spec/github_com/mit_pdos/etcd_grove/examples/net/halfclose/TopLevelRobustness.lean`,
from the example's closed theorem (`Results.lean`).
-/
module

public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.net.halfclose.TopLevelRobustness
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.halfclose.Results

@[expose] public section

noncomputable section

set_option linter.iris.style.nameCheck false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.mit_pdos.etcd_grove.examples.net.halfclose

attribute [local instance] netExts netExtsSemantics netExtsInterp netExts_hasNet
  netExtsCrashInterp

attribute [local instance] GooseGlobalGS.gooseInvGS

section adequacy

variable [GoGlobalContext] {GF : BundledGFunctors}

/-- `halfclose_crash_robust.spec`
(`Net/Spec/github_com/mit_pdos/etcd_grove/examples/net/halfclose/TopLevelRobustness.lean`). -/
theorem halfclose_crash_robust : halfclose_crash_robust.spec := by
  intro lctx sem server_sem client_sem _ σs σc g Hconns bound
  refine Robustness.Robust.of_all fun hf n κs c Hsteps _ i tp σ hi => ?_
  have hfresh : ∀ σ', (∃ e, (e, σ') ∈ system σs σc) → NodeStart lctx σ' := fun σ' ⟨e, he⟩ =>
    ⟨(hf (e, σ') he).1, (hf (e, σ') he).2.1, (hf (e, σ') he).2.2⟩
  exact (halfclose_crash_safety
      σs σc g (hfresh σs ⟨boot_server, by simp [system]⟩)
      (hfresh σc ⟨boot_client, by simp [system]⟩)
      Hconns n κs c Hsteps i tp σ hi).2

end adequacy
end github_com.mit_pdos.etcd_grove.examples.net.halfclose
end Perennial

end
