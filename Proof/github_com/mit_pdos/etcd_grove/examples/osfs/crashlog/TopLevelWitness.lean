/- Lean-first (no Rocq counterpart).

# `osfs/crashlog`: its top-level statement's premises are satisfiable

`premise_sat%` (`Robustness/PremiseSat.lean`): `crash_robust`'s premises hold together with
`Robust`'s antecedents: the directory `/w`, the machine's file system that root alone, empty
(`Robustness/FsStart.lean`), so that nothing is at `/w/log` (`fsOneRoot_lookup_append`). Checked by
`etc/premise-witness.py`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.osfs.crashlog.TopLevelRobustness
public import Robustness.FsStart

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace osfs_crashlog

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs
attribute [local instance] fsExts fsExtsSemantics fsExtsInterp fsExts_hasFs fsExtsCrashInterp

open Robustness

theorem crash_robust.premisesSat : premise_sat% crash_robust.spec := by
  intros
  have hr : RootForm (slashB :: go!"w") := rootForm_one _ (by decide)
  have h0 : ∀ b, (fsOneRoot (slashB :: go!"w")).lookup (child (slashB :: go!"w") b) = none :=
    fun b => fsOneRoot_lookup_append _ _ (List.cons_ne_nil _ _)
  exact ⟨freshState (fsOneRoot (slashB :: go!"w"), ()), ⟨((), ()), ∅⟩, slashB :: go!"w",
    fsInit_fsOneRoot _ hr, ⟨0, List.mem_singleton.2 rfl⟩,
    fun J h => absurd ((h0 _).symm.trans h) (by simp),
    fun k h => absurd ((h0 _).symm.trans h) (by simp),
    0,
    (robustStart_one (σ := freshState (fsOneRoot (slashB :: go!"w"), ())) (g := ⟨((), ()), ∅⟩)
      (fresh_freshState _) (by exts_init) (by exact ⟨fsInit_fsOneRoot _ hr, trivial⟩)).2⟩

end osfs_crashlog
end EtcdGrove
end Perennial

end
