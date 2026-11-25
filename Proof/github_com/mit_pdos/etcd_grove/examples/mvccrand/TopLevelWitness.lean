/- Lean-first (no Rocq counterpart).

# `mvccrand`: its top-level statement's premises are satisfiable

`premise_sat%` (`Robustness/PremiseSat.lean`): the statement of
`Spec/github_com/mit_pdos/etcd_grove/examples/mvccrand/TopLevelRobustness.lean` has premises that hold
together with `Robust`'s antecedents: the directory `r = /w` (a root), the machine's file system that
root alone, empty (`Robustness/FsStart.lean`) (P3, 2026-11-24: that `r` fits and the database's name is
free are no longer premises, the program checks them; the etcd file semantics `etcdFsSem` keeps the default `initLocal`, so `Robust` itself does not ask
`FsInit`: `Hfs` is a premise of its own here, witnessed by `fsInit_fsOneRoot`). Left out:
`HEnv` (`EtcdVerifyOff`, over the opaque value `etcdVerifyEnv`: no Lean proof can establish it, but its
value predicate holds of the unset variable, `etcdVerifyOffValue_unset`; `etc/premise-witness-baseline.txt`);
(until 2026-11-25 also `Hsort`, an Iris contract, which `premise_sat%` left out). Checked by `etc/premise-witness.py`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.TopLevelRobustness
public import Robustness.FsStart

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove


open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
attribute [local instance] etcdFsExts etcdFsExtsSemantics etcdFsExtsInterp etcdFsExts_hasIdIssue

open Robustness Fs

theorem mvccrand_robust.premisesSat : premise_sat% mvccrand_robust.spec without [HEnv] := by
  intros
  have hr : RootForm (slashB :: go!"w") := rootForm_one _ (by decide)
  exact ⟨slashB :: go!"w", freshState ((∅ : IdIssueState), fsOneRoot (slashB :: go!"w"), ()),
    ⟨((), (), ()), ∅⟩, fsInit_fsOneRoot _ hr, 0, List.mem_singleton.2 rfl,
    (robustStart_one (σ := freshState ((∅ : IdIssueState), fsOneRoot (slashB :: go!"w"), ()))
      (g := ⟨((), (), ()), ∅⟩) (fresh_freshState _) (by exts_init)
      (by exts_init)).1⟩

end EtcdGrove
end Perennial

end
