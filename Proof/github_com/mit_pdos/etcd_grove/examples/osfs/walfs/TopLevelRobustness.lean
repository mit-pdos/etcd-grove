/- Lean-first (no Rocq counterpart).

# `osfs/walfs`: the top-level robustness results, proved

`dirswap_crash_robust`, `crash_robust`, `seglog_crash_robust`, stated in
`Spec/github_com/mit_pdos/etcd_grove/examples/osfs/walfs/TopLevelRobustness.lean`,
from the example's closed theorems (`DirSwapLinked.lean`, `Results.lean`, `SegLogLinked.lean`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.osfs.walfs.TopLevelRobustness
public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.walfs.DirSwapLinked
public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.walfs.Results
public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.walfs.SegLogLinked

@[expose] public section

noncomputable section

section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace EtcdGrove

namespace osfs_walfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

open Fs DSBase DS
  github_com.mit_pdos.etcd_grove.examples.osfs.walfs

attribute [local instance] fsExts fsExtsSemantics fsExtsInterp fsExts_hasFs fsExtsCrashInterp

section adequacy

variable [GoGlobalContext] {GF : BundledGFunctors}

/-- `dirswap_crash_robust.spec`
(`Spec/github_com/mit_pdos/etcd_grove/examples/osfs/walfs/TopLevelRobustness.lean`). -/
theorem dirswap_crash_robust : dirswap_crash_robust.spec := by
  intro lctx sem package_sem _ _ Hinit_wp σ g dir j Hinit Hdir Hsafe bound
  exact
    Robustness.Robust.of_single_crashing fun hf n κs t2 σ2 b _ Hsteps =>
      (dirswap_crash_safety
        Hinit_wp σ g dir j hf.1 hf.2.1 Hinit Hdir Hsafe hf.2.2 n κs t2 σ2 b Hsteps).2

end adequacy
end osfs_walfs
end EtcdGrove
end Perennial

end

section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace EtcdGrove

namespace osfs_walfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

open Fs
  github_com.mit_pdos.etcd_grove.examples.osfs.walfs

attribute [local instance] fsExts fsExtsSemantics fsExtsInterp fsExts_hasFs fsExtsCrashInterp

section adequacy

variable [GoGlobalContext] {GF : BundledGFunctors}

/-- `crash_robust.spec`
(`Spec/github_com/mit_pdos/etcd_grove/examples/osfs/walfs/TopLevelRobustness.lean`). -/
theorem crash_robust : crash_robust.spec := by
  intro lctx sem package_sem _ _ Hinit_wp σ g dir Hinit Hdir Hnd Hseg bound
  exact
    Robustness.Robust.of_single_crashing fun hf n κs t2 σ2 b _ Hsteps =>
      (crash_safety
        Hinit_wp σ g dir hf.1 hf.2.1 Hinit Hdir Hnd Hseg hf.2.2 n κs t2 σ2 b Hsteps).2

end adequacy
end osfs_walfs
end EtcdGrove
end Perennial

end

section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace EtcdGrove

namespace osfs_walfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

open Fs DSBase
  github_com.mit_pdos.etcd_grove.examples.osfs.walfs

attribute [local instance] fsExts fsExtsSemantics fsExtsInterp fsExts_hasFs fsExtsCrashInterp

section adequacy

variable [GoGlobalContext] {GF : BundledGFunctors}

/-- `seglog_crash_robust.spec`
(`Spec/github_com/mit_pdos/etcd_grove/examples/osfs/walfs/TopLevelRobustness.lean`). -/
theorem seglog_crash_robust : seglog_crash_robust.spec := by
  intro lctx sem package_sem _ _ _ Hinit_wp σ g dir Hinit Hdir bound
  exact
    Robustness.Robust.of_single_crashing fun hf n κs t2 σ2 b _ Hsteps =>
      (seglog_crash_safety
        Hinit_wp σ g dir hf.1 hf.2.1 Hinit Hdir hf.2.2 n κs t2 σ2 b Hsteps).2

end adequacy
end osfs_walfs
end EtcdGrove
end Perennial

end

end
