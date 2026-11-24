/- Lean-first (no Rocq counterpart).

# `raft/kvdurable`: its top-level statements' premises are satisfiable

`premise_sat%` (`Robustness/PremiseSat.lean`): each statement of `Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvdurable/TopLevelRobustness.lean` has premises that hold
together with `Robust`'s antecedents: one fresh machine whose durable store (`durableExt`) is empty,
so no member's file is there (`Hfiles`). Checked by `etc/premise-witness.py`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvdurable.TopLevelRobustness
public import Robustness.PremiseSat

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Robustness

theorem raft_kvdurable_porcupine_robust.premisesSat :
    premise_sat% raft_kvdurable_porcupine_robust.spec := by
  intros
  exact ⟨go!"d", freshState ((∅ : DurableState), ()), ⟨((), ()), ∅⟩,
    fun _ _ => by simp [freshState],
    (robustStart_one (fresh_freshState _) ⟨trivial, trivial⟩ ⟨trivial, trivial⟩).1⟩

theorem raft_kvdurableN_porcupine_robust.premisesSat :
    premise_sat% raft_kvdurableN_porcupine_robust.spec := by
  intros
  exact ⟨go!"d", 1, by decide, by decide, freshState ((∅ : DurableState), ()), ⟨((), ()), ∅⟩,
    fun _ _ => by simp [freshState],
    (robustStart_one (fresh_freshState _) ⟨trivial, trivial⟩ ⟨trivial, trivial⟩).1⟩

end EtcdGrove
end Perennial

end
