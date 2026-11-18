/- Lean-first (no Rocq counterpart).

# `net/preface`: the top-level robustness result, proved

`preface_crash_robust`, stated in
`NetTcp/Spec/github_com/mit_pdos/etcd_grove/examples/net/preface/TopLevelRobustness.lean`,
from the example's closed theorem (`Results.lean`).
-/
module

public import NetTcp.Spec.github_com.mit_pdos.etcd_grove.examples.net.preface.TopLevelRobustness

@[expose] public section

noncomputable section

set_option linter.iris.style.nameCheck false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Tcp

namespace github_com.mit_pdos.etcd_grove.examples.net.preface

attribute [local instance] tcpExts tcpExtsSemantics tcpExtsInterp tcpExts_hasTcp
  tcpExtsCrashInterp

attribute [local instance] GooseGlobalGS.gooseInvGS

section adequacy

variable [GoGlobalContext] {GF : BundledGFunctors}

/-- `preface_crash_robust.spec`
(`NetTcp/Spec/github_com/mit_pdos/etcd_grove/examples/net/preface/TopLevelRobustness.lean`). -/
theorem preface_crash_robust : preface_crash_robust.spec := by
  intro lctx sem package_s package_c package_j field_sem _ σs σc σj g h Hhost Hplan pl Hwf Hpl
    Hconns bound
  refine Robustness.Robust.of_all fun hf n κs c Hsteps _ i tp σ hi => ?_
  have hfresh : ∀ σ', (∃ e, (e, σ') ∈ system σs σc σj) → NodeStart lctx σ' := fun σ' ⟨e, he⟩ =>
    ⟨(hf (e, σ') he).1, (hf (e, σ') he).2.1, (hf (e, σ') he).2.2⟩
  exact (preface_crash_safety
      σs σc σj g h (hfresh σs ⟨boot_server, by simp [system]⟩)
      (hfresh σc ⟨boot_client, by simp [system]⟩) (hfresh σj ⟨boot_junk, by simp [system]⟩) Hhost
      Hplan pl Hwf Hpl Hconns n κs c Hsteps i tp σ hi).2

end adequacy
end github_com.mit_pdos.etcd_grove.examples.net.preface
end Perennial

end
