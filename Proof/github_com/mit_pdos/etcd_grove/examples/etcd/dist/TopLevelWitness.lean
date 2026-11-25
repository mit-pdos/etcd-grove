/- Lean-first (no Rocq counterpart).

# `etcd/dist`: the distributed theorems' premises are satisfiable

`premise_sat%` (`Robustness/PremiseSat.lean`): the premises of `etcd_robust.spec` and
`etcd_robust_nocrash.spec` (`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/TopLevelRobustness.lean`)
hold together with `Robust`'s antecedents, at the deployment `pwDeployment` (`dist_test.go`'s shape:
three members, one KV workload with two client machines), from the per-premise witnesses of
`PremiseWitness.lean`: the start states `Hσs`, `Hσc`, `Hσn` (each member's machine with its empty WAL
area and data directory, each other machine with `/tmp`), every machine a fresh process in its
extensions' initial state.

**Left out** (`etc/premise-witness-baseline.txt`):
- `Hbf` (`BootFacts`, class `pending-b`): bootstrap's results as Go computes them, pinned to `bootGo`'s
  values on the n5 line (#50, entry 142), witnessed once that statement is on this line;
- `Henv` (`EtcdEnv`, `opaque`): at `pwDeployment` it is exactly the opaque environment propositions
  (`witness.etcdEnv_iff`, `pwDeployment_noExpiry`), which no Lean proof can establish;
- `HEnv` (`EtcdVerifyOff`) and `Hfips` (`GodebugFips140Off`), `opaque`: over the opaque run values
  `etcdVerifyEnv`, `godebugFips140`; each holds when its variable is unset (`witness.etcdVerifyOff_unset`,
  `witness.godebugFips140Off_unset`).

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

open Robustness witness

attribute [local instance] etcdNetExts etcdNetExtsSemantics etcdNetExtsInterp etcdNetExts_hasIdIssue
  etcdNetExts_hasFs etcdNetExts_hasNet etcdFsSem

theorem etcd_robust_nocrash.premisesSat :
    premise_sat% etcd_robust_nocrash.spec without [Hbf, Henv, HEnv, Hfips] := by
  intros
  exact ⟨pwDeployment, [], [], [], serverStates pwDeployment,
    clientStates pwDeployment.workloads.length, clientStates pwDeployment.nodeList.length, initGlobal,
    serverStates_start _ pwDeployment_names, clientStates_start _, clientStates_start _,
    robustStart_nocrash _⟩

theorem etcd_robust.premisesSat :
    premise_sat% etcd_robust.spec without [Hbf, Henv, HEnv, Hfips] := by
  intros
  exact ⟨pwDeployment, [], [], [], serverStates pwDeployment,
    clientStates pwDeployment.workloads.length, clientStates pwDeployment.nodeList.length, initGlobal,
    serverStates_start _ pwDeployment_names, clientStates_start _, clientStates_start _,
    robustStart_crash _⟩

end etcd_dist
end EtcdGrove
end Perennial

end
