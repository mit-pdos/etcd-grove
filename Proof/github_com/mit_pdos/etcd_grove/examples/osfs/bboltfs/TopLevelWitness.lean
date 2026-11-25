/- Lean-first (no Rocq counterpart).

# `osfs/bboltfs`: its top-level statement's premises are satisfiable

`premise_sat%` (`Robustness/PremiseSat.lean`): `bootCrashRobust`'s premises hold together with
`Robust`'s antecedents (under P1's semantics, whose `initLocal` is Perennial's default): the
directory `/w`, the machine's file system that root alone, empty (`Robustness/FsStart.lean`), so
that nothing is at `/w/db` (`fsOneRoot_lookup_append`). Checked by `etc/premise-witness.py`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.TopLevelRobustness
public import Robustness.FsStart

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace osfs_bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs
open Fs

attribute [local instance] fsExts fsExtsInterp

local instance : GooseSemantics := fsExtsSemanticsWithS AnyStep P1

local instance : ExtSemantics fsExt := fsSemWithS AnyStep P1

local instance : HasExt fsExt := fsExtsWithS_hasFs AnyStep P1

open Robustness

theorem bootCrashRobust.premisesSat : premise_sat% bootCrashRobust.spec := by
  intros
  have hr : RootForm (slashB :: go!"w") := rootForm_one _ (by decide)
  exact ⟨slashB :: go!"w", freshState (fsOneRoot (slashB :: go!"w"), ()), ⟨((), ()), ∅⟩,
    fsInit_fsOneRoot _ hr, ⟨0, List.mem_singleton.2 rfl⟩,
    fsOneRoot_lookup_append _ _ (by decide),
    (robustStart_one (σ := freshState (fsOneRoot (slashB :: go!"w"), ())) (g := ⟨((), ()), ∅⟩)
      (fresh_freshState _) (by exts_init) (by exts_init)).2⟩

end osfs_bboltfs
end EtcdGrove
end Perennial

end
