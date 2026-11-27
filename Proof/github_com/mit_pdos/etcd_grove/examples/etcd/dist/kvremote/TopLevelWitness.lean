/- Lean-first (no Rocq counterpart).

# `etcd/dist/kvremote`: M1's premises are satisfiable

`premise_sat%` (`Robustness/PremiseSat.lean`): the premises of `etcd_kv_safe_nocrash`
(`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/kvremote/TopLevelRobustness.lean`) hold together
with `Robust`'s antecedents, at a deployment of M1's scope, `kvDeployment`: the witness member alone
(`dist/PremiseWitness.lean`: `putgetd`, token `putgetd`), auth off, and one `kv` workload with one client
machine. The witness is built from the shared per-premise lemmas of `dist/PremiseWitness.lean`
(`bootFacts_witness`, `serverStart_witness`, `clientStart_witness`) and M1's scope, which is decided on the
value (`kvDeployment_scope`).

**Left out** (`etc/premise-witness-baseline.txt`, class `opaque`): `Henv` (`EtcdEnv`'s opaque environment
propositions), `HEnv` (`EtcdVerifyOff`) and `Hfips` (`GodebugFips140Off`). `putget_safe`'s witness leaves
out the same propositions. Checked by `etc/premise-witness.py`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.TopLevelRobustness
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.PremiseWitness

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open go_etcd_io.raft.v3 Robustness Fs

attribute [local instance] etcdNetExts etcdNetExtsSemantics etcdNetExtsInterp etcdNetExts_hasIdIssue
  etcdNetExts_hasFs etcdNetExts_hasNet etcdFsSem

/-- The client machine's address (a machine of its own, port `2390`). -/
def kvNodeA : GoString := go!"10.77.1.3:2390"

/-- **M1's witness deployment**: the witness member, its token, auth off, one `kv` workload (one client,
one operation) with one client machine. -/
def kvDeployment : Deployment :=
  { members := [witnessMember]
    token := witnessToken
    cfg := ⟨go!"", W64 0, W64 10000, W64 5000, false⟩
    workloads := [⟨W64 0, W64 1, W64 1⟩]
    nodes := [[kvNodeA]] }

/-- **M1's scope holds** at the witness deployment. -/
theorem kvDeployment_scope : KvOnly kvDeployment ∧ kvDeployment.cfg.auth = false := by
  refine ⟨fun w hw => ?_, rfl⟩
  simp only [kvDeployment, List.mem_singleton] at hw
  subst hw
  rfl

theorem etcd_kv_safe_nocrash.premisesSat :
    premise_sat% etcd_kv_safe_nocrash.spec without [Henv, HEnv, Hfips] := by
  intros
  refine ⟨kvDeployment, kvDeployment_scope, etcd_putget_dist.pgBoot, bootFacts_witness kvDeployment rfl rfl,
    [witnessMemberσ], [witnessClientσ], [witnessClientσ],
    ⟨((), (), (default : Net.NetGlobal), ()), ∅⟩,
    ⟨rfl, fun p hp => ?_⟩, ⟨rfl, fun σ hσ => ?_⟩,
    ⟨rfl, fun σ hσ => ?_⟩, ?_, by exts_init, ?_⟩
  · simp only [kvDeployment, List.zip_cons_cons, List.zip_nil_right, List.mem_cons,
      List.not_mem_nil, or_false] at hp
    subst hp
    exact serverStart_witness
  · simp only [List.mem_singleton] at hσ
    subst hσ
    exact clientStart_witness
  · simp only [List.mem_singleton] at hσ
    subst hσ
    exact clientStart_witness
  · intro m hm
    simp [machines, servers, clients, nodeMachines] at hm
    rcases hm with rfl | rfl | rfl <;> exact fresh_freshState _
  · intro m hm
    simp [machines, servers, clients, nodeMachines] at hm
    rcases hm with rfl | rfl | rfl <;>
      (try simp only [witnessMemberσ, witnessClientσ]) <;> exts_init

end etcd_dist
end EtcdGrove
end Perennial

end
