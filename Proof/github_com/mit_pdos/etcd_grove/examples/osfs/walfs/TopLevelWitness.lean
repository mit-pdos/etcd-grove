/- Lean-first (no Rocq counterpart).

# `osfs/walfs`: its top-level statements' premises are satisfiable

`premise_sat%` (`Robustness/PremiseSat.lean`): `seglog_crash_robust`'s premises hold together with
`Robust`'s antecedents: the directory `/w`, the machine's file system that root alone, empty
(`Robustness/FsStart.lean`). (`Hinit_wp`, an Iris contract, is left out by `premise_sat%` itself.)
`dirswap_crash_robust` and `crash_robust` are in `etc/premise-witness-baseline.txt` (their premises on
the files below `dir` need lookups in the start state). Checked by `etc/premise-witness.py`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.osfs.walfs.TopLevelRobustness
public import Robustness.FsStart

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace osfs_walfs


open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs DSBase DS
attribute [local instance] fsExts fsExtsSemantics fsExtsInterp fsExts_hasFs fsExtsCrashInterp

open Robustness Fs

theorem seglog_crash_robust.premisesSat : premise_sat% seglog_crash_robust.spec := by
  intros
  have hr : RootForm (slashB :: go!"w") := rootForm_one _ (by decide)
  exact ⟨freshState (fsOneRoot (slashB :: go!"w"), ()), ⟨((), ()), ∅⟩, slashB :: go!"w",
    fsInit_fsOneRoot _ hr, ⟨0, List.mem_singleton.2 rfl⟩, 0,
    (robustStart_one (σ := freshState (fsOneRoot (slashB :: go!"w"), ())) (g := ⟨((), ()), ∅⟩)
      (fresh_freshState _) (by exts_init) (by exact ⟨fsInit_fsOneRoot _ hr, trivial⟩)).2⟩

end osfs_walfs
end EtcdGrove
end Perennial

end
