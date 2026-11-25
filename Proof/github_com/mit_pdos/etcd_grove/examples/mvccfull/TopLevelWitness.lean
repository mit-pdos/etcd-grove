/- Lean-first (no Rocq counterpart).

# `mvccfull`: its top-level statement's premises are satisfiable

`premise_sat%` (`Robustness/PremiseSat.lean`): the statement of
`Spec/github_com/mit_pdos/etcd_grove/examples/mvccfull/TopLevelRobustness.lean` has premises that hold
together with `Robust`'s antecedents: the directory `r = /w` (a root, fitting), the machine's file
system that root alone, empty (`Robustness/FsStart.lean`), so the database names are absent
(the etcd file semantics `etcdFsSem` keeps the default `initLocal`, so `Robust` itself does not ask
`FsInit`: `Hfs` is a premise of its own here, witnessed by `fsInit_fsOneRoot`). Left out:
`HEnv` (`EtcdVerifyOff`, over the opaque value `etcdVerifyEnv`: no Lean proof can establish it, but its
value predicate holds of the unset variable, `etcdVerifyOffValue_unset`; `etc/premise-witness-baseline.txt`);
`Hsort`, an Iris contract, is left out by `premise_sat%` itself. Checked by `etc/premise-witness.py`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.TopLevelRobustness
public import Robustness.FsStart

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove


open Iris Iris.BI
attribute [local instance] etcdFsExts etcdFsExtsSemantics etcdFsExtsInterp etcdFsExts_hasIdIssue

open Robustness Fs

theorem mvccfull_robust.premisesSat : premise_sat% mvccfull_robust.spec without [HEnv] := by
  intros
  have hr : RootForm (slashB :: go!"w") := rootForm_one _ (by decide)
  exact ⟨slashB :: go!"w", freshState ((∅ : IdIssueState), fsOneRoot (slashB :: go!"w"), ()),
    ⟨((), (), ()), ∅⟩, fsInit_fsOneRoot _ hr, 0, List.mem_singleton.2 rfl, fun _ _ => fsOneRoot_entry _ _ _,
    ⟨by decide, winOk_short (by decide)⟩,
    (robustStart_one (σ := freshState ((∅ : IdIssueState), fsOneRoot (slashB :: go!"w"), ()))
      (g := ⟨((), (), ()), ∅⟩) (fresh_freshState _) (by exts_init)
      (by exts_init)).1⟩

end EtcdGrove
end Perennial

end
