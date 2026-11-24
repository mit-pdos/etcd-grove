/- Lean-first (no Rocq counterpart).

# `osfs/bboltfs`: the definitions its top-level statement is written in

The program the example's top-level theorem is about, and the other definitions its statement
names, moved here unchanged out of `Results.lean` so that the statement
(`Spec/.../TopLevelRobustness.lean`) imports no proof (CLAUDE.md, "Import tiers").
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.BootMinibolt
public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.P1Sat
public import Robustness.Statement

@[expose] public section

noncomputable section

section

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

/-- `AnyStep` keeps every step. -/
theorem anyStep_keeps : StepKeeps AnyStep := by
  intro _ _ _ _ _ _ _ _ _ _ hs
  exact ⟨_, _, _, hs, trivial⟩


end osfs_bboltfs
end EtcdGrove
end Perennial

end


end
