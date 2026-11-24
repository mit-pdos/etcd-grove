/- Lean-first (no Rocq counterpart).

# `osfs/crashlog`: the top-level robustness result, proved

`crash_robust`, stated in
`Spec/github_com/mit_pdos/etcd_grove/examples/osfs/crashlog/TopLevelRobustness.lean`,
from the example's closed theorem (`Results.lean`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.osfs.crashlog.TopLevelRobustness
public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.crashlog.Results

@[expose] public section

noncomputable section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace EtcdGrove

namespace osfs_crashlog

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.osfs.crashlog

open Fs

attribute [local instance] fsExts fsExtsSemantics fsExtsInterp fsExts_hasFs fsExtsCrashInterp

section adequacy

variable [GoGlobalContext] {GF : BundledGFunctors}

/-- `crash_robust.spec`
(`Spec/github_com/mit_pdos/etcd_grove/examples/osfs/crashlog/TopLevelRobustness.lean`). -/
theorem crash_robust : crash_robust.spec := by
  intro lctx sem package_sem _ _ σ g dir Hinit Hdir Hnd Hlog bound
  exact
    Robustness.Robust.of_single_crashing fun hf n κs t2 σ2 b _ Hsteps =>
      (crash_safety
        σ g dir hf.1 hf.2.1 Hinit Hdir Hnd Hlog hf.2.2 n κs t2 σ2 b Hsteps).2

end adequacy
end osfs_crashlog
end EtcdGrove
end Perennial

end
