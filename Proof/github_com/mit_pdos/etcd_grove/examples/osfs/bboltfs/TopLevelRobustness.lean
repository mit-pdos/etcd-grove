/- Lean-first (no Rocq counterpart).

# `osfs/bboltfs`: the top-level robustness result, proved

`bootCrashRobust`, stated in
`Spec/github_com/mit_pdos/etcd_grove/examples/osfs/bboltfs/TopLevelRobustness.lean`,
from the example's closed theorem (`Results.lean`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.TopLevelRobustness
public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.Results
public import Robustness.CrashBelow

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
  refine Robustness.Robust.of_single_crashing_below fun hf n κs t2 σ2 b _ Hsteps => ?_
  exact bootCrashSafety_bounded (GF := fsGF) (n + 1) (2 ^ 30) (Nat.le_refl _) σ g dir hf.1 hf.2.1
    Hinit Hdir Hnone n κs t2 σ2 b Hsteps (by omega) hf.2.2

end adequacy
end osfs_bboltfs
end EtcdGrove
end Perennial

end
