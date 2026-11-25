/- Lean-first (no Rocq counterpart).

# `net/acceptloop`: the top-level robustness result, proved

`acceptloop_crash_robust`, stated in
`Net/Spec/github_com/mit_pdos/etcd_grove/examples/net/acceptloop/TopLevelRobustness.lean`,
from the example's closed theorem (`Results.lean`).
-/
module

public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.net.acceptloop.TopLevelRobustness
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.acceptloop.Results

@[expose] public section

noncomputable section

set_option linter.iris.style.nameCheck false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.mit_pdos.etcd_grove.examples.net.acceptloop

attribute [local instance] netExts netExtsSemantics netExtsInterp netExts_hasNet
  netExtsCrashInterp

attribute [local instance] GooseGlobalGS.gooseInvGS

section adequacy

variable [GoGlobalContext] {GF : BundledGFunctors}

/-- `acceptloop_crash_robust.spec`
(`Net/Spec/github_com/mit_pdos/etcd_grove/examples/net/acceptloop/TopLevelRobustness.lean`). -/
theorem acceptloop_crash_robust : acceptloop_crash_robust.spec := by
  intro lctx sem server_sem client_sem field_sem σs σc g bound hf hig
  -- `Robust`'s premise `extsInitGlobal g` is, for `netExts = [netExt]`, no connection
  -- (`NetGlobal.init`, `GooseLang/Ext/Net/Impl.lean`)
  have Hconns : (extGlobal netExt g.globalWorld).conns = ∅ := hig.1
  revert hf hig
  refine Robustness.Robust.of_all fun hf n κs c Hsteps _ i tp σ hi => ?_
  have hfresh : ∀ σ', (∃ e, (e, σ') ∈ system σs σc) → NodeStart lctx σ' := fun σ' ⟨e, he⟩ =>
    ⟨(hf (e, σ') he).1, (hf (e, σ') he).2.1, (hf (e, σ') he).2.2⟩
  exact (acceptloop_crash_safety
      σs σc g (hfresh σs ⟨boot_server, by simp [system]⟩)
      (hfresh σc ⟨boot_client, by simp [system]⟩)
      Hconns n κs c Hsteps i tp σ hi).2

end adequacy
end github_com.mit_pdos.etcd_grove.examples.net.acceptloop
end Perennial

end
