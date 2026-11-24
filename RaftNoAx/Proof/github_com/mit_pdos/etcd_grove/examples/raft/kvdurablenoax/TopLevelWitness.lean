/- Lean-first (no Rocq counterpart).

# `raft/kvdurable`: its top-level statements' premises are satisfiable

`premise_sat%` (`Robustness/PremiseSat.lean`): each statement of `RaftNoAx/Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvdurablenoax/TopLevelRobustness.lean` has premises that hold
together with `Robust`'s antecedents: one fresh machine whose durable store (`durableExt`) is empty,
so no member's file is there (`Hfiles`). Checked by `etc/premise-witness.py`.
-/
module

public import RaftNoAx.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvdurablenoax.TopLevelRobustness
public import Robustness.PremiseSat

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3
attribute [local instance] durableExts durableExtsSemantics durableExtsInterp durableExts_hasExt

open Robustness

theorem raft_kvdurable_porcupine_robust.premisesSat :
    premise_sat% raft_kvdurable_porcupine_robust.spec := by
  intros
  exact ⟨go!"d", freshState ((∅ : DurableState), ()), ⟨((), ()), ∅⟩,
    fun _ _ => rfl,
    (robustStart_one (fresh_freshState _) (by exts_init) (by exts_init)).1⟩

theorem raft_kvdurableN_porcupine_robust.premisesSat :
    premise_sat% raft_kvdurableN_porcupine_robust.spec := by
  intros
  exact ⟨go!"d", 1, by decide, by decide, freshState ((∅ : DurableState), ()), ⟨((), ()), ∅⟩,
    fun _ _ => rfl,
    (robustStart_one (fresh_freshState _) (by exts_init) (by exts_init)).1⟩

end EtcdGrove
end Perennial

end
