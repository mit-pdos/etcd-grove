/- Lean-first (no Rocq counterpart).

# `osfs/bboltfs`: the top-level robustness result, proved

`bootCrashRobust`, stated in
`Spec/github_com/mit_pdos/etcd_grove/examples/osfs/bboltfs/TopLevelRobustness.lean`,
from the example's closed theorem (`Results.lean`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.TopLevelRobustness
public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.Results

@[expose] public section

noncomputable section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace EtcdGrove

namespace osfs_bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs

open Fs

attribute [local instance] fsExts fsExtsInterp

local instance : GooseSemantics := fsExtsSemanticsWithS AnyStep P1

local instance : ExtSemantics fsExt := fsSemWithS AnyStep P1

local instance : HasExt fsExt := fsExtsWithS_hasFs AnyStep P1

section adequacy

variable [GoGlobalContext] {GF : BundledGFunctors}

/-- `bootCrashRobust.spec`
(`Spec/github_com/mit_pdos/etcd_grove/examples/osfs/bboltfs/TopLevelRobustness.lean`). -/
theorem bootCrashRobust : bootCrashRobust.spec := by
  intro lctx sem package_sem _ _ dir σ g Hinit Hdir Hnone
  refine Robustness.Robust.of_single_crashing fun hf n κs t2 σ2 b hn Hsteps => ?_
  exact bootCrashSafety dir σ g hf.1 hf.2.1 Hinit Hdir Hnone hf.2.2 n κs t2 σ2 b Hsteps
    (fun k κs' ρ' b' hk hs => Nat.lt_of_lt_of_le
      (RealCrashThreadsBelow.of_single hf.2.2 k κs' ρ' b' hk hs) (by omega))

end adequacy
end osfs_bboltfs
end EtcdGrove
end Perennial

end
