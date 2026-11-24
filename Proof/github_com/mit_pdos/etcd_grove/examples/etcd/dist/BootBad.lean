/- Lean-first (no Rocq counterpart).

# `etcd/dist`: every machine's boot on a malformed deployment

`etcdBootNCBad_holds`: `EtcdBootNCBad` (`TopLevelRobustness.lean`), each machine's boot program safe from
`True` when `¬ d.WellFormed`. Every program initializes its package (`server` or `client`: the machine's
prometheus registration rights allocated here, from no package initialized), evaluates the deployment's
literal (`wp_deploymentLit`), calls its entry point (`server.MainDeployment`, `client.Orchestrator`,
`client.NodeDeployment`), which calls `deployment.WellFormed` first and returns at once on its non-nil
error: `WellFormed.spec` returns `nil` only for a well-formed deployment.

**Hypotheses** (no axiom):
* `Hctx`: `ContextReadErrs` at every ghost state over the statement's local context (as `putget`'s
  `member_boot`): the packages' initializers need it (`server.wp_initialize'`, `client.wp_initialize'`). To
  be discharged by the per-function context axioms (premises-to-axioms), not a top-level premise.
* `HWF`: `deployment.WellFormed.spec`, the deployment check's spec (its proof is `etcd-safe-wf`'s).
* The packages' `Assumptions` (`server`, `client`): instance binders of `EtcdBootNCBad` itself, as
  `putget_safe`'s statement takes `putget.Assumptions`; `etcd_safe`'s statement does not take them yet.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.TopLevelRobustness
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.DeploymentLit
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.InitLinked
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.PkgTable
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.InitLinked
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.PkgTable
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.WellFormed
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Adequacy
public import Proof.go_uber_org.zap.NewNop

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic go_etcd_io.raft.v3 Net
open github_com.mit_pdos.etcd_grove.examples.etcd.dist

attribute [local instance] etcdNetExts etcdNetExtsSemantics etcdNetExtsInterp etcdNetExts_hasIdIssue
  etcdNetExts_hasFs etcdNetExts_hasNet etcdFsSem GooseGlobalGS.gooseInvGS

/-- The registering packages' IDs can have their rights (`server`'s; decided by the kernel). -/
theorem server_regQsOk : prometheus.regQsOk server.regQs :=
  prometheus.regQsOk_of_keys _ _ rfl (by decide +kernel) (by decide +kernel)

/-- The registering packages' IDs can have their rights (`client`'s; decided by the kernel). -/
theorem client_regQsOk : prometheus.regQsOk client.regQs :=
  prometheus.regQsOk_of_keys _ _ rfl (by decide +kernel) (by decide +kernel)

/-- A machine of the deployment runs one of the three programs. -/
theorem machines_prog [GoGlobalContext] [GoSemanticsFunctions] {d : Deployment}
    {σs σc σn : List state} {i : Nat} {m : Expr × state}
    (h : (machines d σs σc σn)[i]? = some m) :
    (∃ k σ, m = (serverProg d k, σ)) ∨ (∃ j σ, m = (clientProg d j, σ)) ∨
      (∃ n σ, m = (nodeProg d n, σ)) := by
  have hm : m ∈ machines d σs σc σn := List.mem_of_getElem? h
  simp only [machines, servers, clients, nodeMachines, List.mem_append, List.mem_mapIdx] at hm
  rcases hm with (⟨k, hk, rfl⟩ | ⟨j, hj, rfl⟩) | ⟨n, hn, rfl⟩
  · exact .inl ⟨k, _, rfl⟩
  · exact .inr (.inl ⟨j, _, rfl⟩)
  · exact .inr (.inr ⟨n, _, rfl⟩)

section boot
variable [GoGlobalContext] [lctx : GoLocalContext] [sem : go.Semantics]
  [_root_.Perennial.errors.Assumptions] [_root_.Perennial.fmt.Assumptions] [log.NewModel]

/-- **A member's machine on a malformed deployment** (see the file header). -/
theorem serverBootBad [srv_sem : server.Assumptions]
    (Hctx : ∀ hG : HeapGS .hasLC etcdDistGF, ContextReadErrs (GF := etcdDistGF) (hG := hG))
    (HWF : ∀ hG : HeapGS .hasLC etcdDistGF, deployment.WellFormed.spec (GF := etcdDistGF) (hG := hG))
    (d : Deployment) (Hd : ¬ d.WellFormed) (Hfips : crypto.fips140.GodebugFips140Off) (k : Nat)
    (σ : state) [G : GooseGlobalGS .hasLC etcdDistGF] :
    Net.DistBootWpSL srvLevelK (2 ^ 28 - 1) (serverProg d k) σ (iprop(True) : IProp etcdDistGF) := by
  intro hG hGG hL hlo hrb hT
  obtain ⟨G', ⟨fl, lc, nh, gs, th, cr⟩⟩ := hG
  simp only at hGG hL
  subst hGG hL
  letI hG : HeapGS .hasLC etcdDistGF := ⟨G', ⟨fl, lc, nh, gs, th, cr⟩⟩
  haveI := Hctx hG
  haveI := etcdFsSemOk
  iintro - Hls Hgs Htok
  imod (prometheus.regKeys_alloc (GF := etcdDistGF) server.regQs server_regQsOk) with ⟨%γreg, Hregs⟩
  letI : prometheus.PromRegGS etcdDistGF := ⟨γreg⟩
  ihave Hns := prometheus.idToks_regsFree (GF := etcdDistGF) server.regQs $$ Hregs
  ihave Hown := ownInitializing_of_empty (server.getIsPkgInit (GF := etcdDistGF)) $$ Hgs
  imodintro
  unfold serverProg
  wp_apply (server.wp_initialize' _ server.getIsPkgInit_wf) $$ [Hown Hns] as ⟨-, #Hpkg⟩
  · iframe
  first
    | wp_bind (deploymentLit d)
    | (wp_pure; wp_bind (deploymentLit d))
  iapply wp_deploymentLit
  iintro %v #Hrepr
  -- `MainDeployment(d, i)`
  wp_func_call
  wp_call
  wp_auto
  wp_apply zap.NewNop.wp_proof as %lg -
  wp_auto
  -- `MainDeploymentLogger(d, i, lg)`
  wp_func_call
  wp_call
  wp_auto
  wp_apply (HWF hG v d Hfips) $$ [Hrepr] as %err %Herr
  · iframe #
  have hne : err ≠ interface.nil := fun h => Hd (Herr h)
  wp_auto
  repeat' wp_if_destruct
  all_goals (try (exfalso; exact hne (by assumption)))
  all_goals wp_auto
  all_goals (try (ipureintro; rfl))
  all_goals (trace_state; sorry)

end boot

end etcd_dist
end EtcdGrove
end Perennial

end
