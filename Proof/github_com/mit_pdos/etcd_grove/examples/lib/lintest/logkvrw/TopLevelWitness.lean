/- Lean-first (no Rocq counterpart).

# `lib/lintest/logkvrw`: its top-level statements' premises are satisfiable

`premise_sat%` (`Robustness/PremiseSat.lean`): each statement of `Spec/github_com/mit_pdos/etcd_grove/examples/lib/lintest/logkvrw/TopLevelRobustness.lean` has premises that hold
together with `Robust`'s antecedents (one fresh machine, no extension, `Robustness.noExts`).
Checked by `etc/premise-witness.py`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.lintest.logkvrw.TopLevelRobustness
public import Robustness.PremiseSat

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace lintest
namespace logkvrw

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
attribute [local instance] Robustness.noExts Robustness.noExtsSemantics Robustness.noExtsInterp

open Robustness

theorem logkvrw_robust.premisesSat : premise_sat% logkvrw_robust.spec := by
  intros
  exact ⟨freshState PUnit.unit, ⟨PUnit.unit, ∅⟩,
    (robustStart_one (fresh_freshState _) (by exts_init) (by exts_init)).1⟩

end logkvrw
end lintest
end EtcdGrove
end Perennial

end
