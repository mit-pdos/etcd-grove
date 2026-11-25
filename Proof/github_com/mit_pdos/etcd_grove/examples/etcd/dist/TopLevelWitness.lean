/- Lean-first (no Rocq counterpart).

# `etcd/dist`: the distributed theorems' premises are satisfiable

`premise_sat%` (`Robustness/PremiseSat.lean`): the premises of `etcd_robust.spec` and
`etcd_robust_nocrash.spec` (`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/TopLevelRobustness.lean`)
hold together with `Robust`'s antecedents, at the deployment `witnessDeployment` (the witness member
`putgetd` alone, one KV workload with two client machines), from the per-premise lemmas of
`PremiseWitness.lean`: bootstrap's results as Go computes them (`witnessDeployment_boot`, from
`bootFacts_witness`: the member id SHA-1's, evaluated by the kernel), the start states `Hσs`, `Hσc`, `Hσn`
(`serverStates_start`, `clientStates_start`), every machine a fresh process in its extensions' initial
state (`robustStart_nocrash`, `robustStart_crash`).

**Left out** (`etc/premise-witness-baseline.txt`, class `opaque`):
- `Henv` (`EtcdEnv`): at `witnessDeployment` it is exactly the opaque environment propositions
  (`etcdEnv_iff`, `witnessDeployment_noExpiry`), which no Lean proof can establish;
- `HEnv` (`EtcdVerifyOff`) and `Hfips` (`GodebugFips140Off`): over the opaque run values `etcdVerifyEnv`,
  `godebugFips140`; each holds when its variable is unset (`etcdVerifyOff_unset`,
  `godebugFips140Off_unset`).

Checked by `etc/premise-witness.py`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.TopLevelRobustness
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.PremiseWitness

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Robustness

attribute [local instance] etcdNetExts etcdNetExtsSemantics etcdNetExtsInterp etcdNetExts_hasIdIssue
  etcdNetExts_hasFs etcdNetExts_hasNet etcdFsSem

theorem etcd_robust_nocrash.premisesSat :
    premise_sat% etcd_robust_nocrash.spec without [Henv, HEnv, Hfips] := by
  intros
  exact ⟨witnessDeployment, _, _, _, witnessDeployment_boot, serverStates witnessDeployment,
    clientStates witnessDeployment.workloads.length, clientStates witnessDeployment.nodeList.length,
    initGlobal, serverStates_start _ witnessDeployment_names, clientStates_start _, clientStates_start _,
    robustStart_nocrash _⟩

theorem etcd_robust.premisesSat :
    premise_sat% etcd_robust.spec without [Henv, HEnv, Hfips] := by
  intros
  exact ⟨witnessDeployment, _, _, _, witnessDeployment_boot, serverStates witnessDeployment,
    clientStates witnessDeployment.workloads.length, clientStates witnessDeployment.nodeList.length,
    initGlobal, serverStates_start _ witnessDeployment_names, clientStates_start _, clientStates_start _,
    robustStart_crash _⟩

end etcd_dist
end EtcdGrove
end Perennial

end
