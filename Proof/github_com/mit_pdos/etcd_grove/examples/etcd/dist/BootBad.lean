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
The deployment check is `deployment`'s linked `wp_WellFormed` (`deployment/Link.lean`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.TopLevelRobustness
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.DeploymentLit
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.InitLinked
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.PkgTable
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.InitLinked
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.PkgTable
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.Link
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

-- Finish a program after the deployment's check failed (`WellFormed`'s error `hne` not `nil`).
set_option hygiene false in
local macro "bad_finish" hne:ident : tactic => `(tactic|
  repeat' (first
    | (ipureintro; rfl)
    | (wp_if_destruct <;> try (exfalso; exact $hne (by simpa using Hif)))
    | (wp_func_call; wp_call)
    | wp_auto))

/-- `ContextReadErrs` at a ghost state over the local context `lctx`. -/
abbrev CtxErrsAt [GoGlobalContext] [lctx : GoLocalContext] [go.Semantics]
    (hG : HeapGS .hasLC etcdDistGF) : Prop :=
  ContextReadErrs (GF := etcdDistGF)
    (hG := ⟨hG.goose_globalGS, { hG.goose_localGS with goose_go_local_context := lctx }⟩)

section boot
variable [GoGlobalContext] [lctx : GoLocalContext] [sem : go.Semantics]
  [_root_.Perennial.errors.Assumptions] [_root_.Perennial.fmt.Assumptions] [log.NewModel]

/-- **A member's machine on a malformed deployment** (see the file header). -/
theorem serverBootBad [srv_sem : server.Assumptions]
    (Hctx : ∀ hG : HeapGS .hasLC etcdDistGF, CtxErrsAt hG)
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
  try wp_auto
  wp_apply zap.NewNop.wp_proof as %lg -
  try wp_auto
  -- `MainDeploymentLogger(d, i, lg)`
  wp_func_call
  wp_call
  try wp_auto
  wp_apply (wp_WellFormed v d Hfips) $$ [Hrepr] as %err %Herr
  · iframe #
  have hne : err ≠ interface.nil := fun h => Hd (Herr h)
  cases err with
  | nil => exact absurd rfl hne
  | ok i =>
    bad_finish hne
    all_goals (trace_state; sorry)

/-- **A workload's orchestrator machine on a malformed deployment** (see the file header). -/
theorem clientBootBad [cl_sem : client.Assumptions]
    (Hctx : ∀ hG : HeapGS .hasLC etcdDistGF, CtxErrsAt hG)
    (d : Deployment) (Hd : ¬ d.WellFormed) (Hfips : crypto.fips140.GodebugFips140Off) (j : Nat)
    (σ : state) [G : GooseGlobalGS .hasLC etcdDistGF] :
    Net.DistBootWpSL srvLevelK (2 ^ 28 - 1) (clientProg d j) σ (iprop(True) : IProp etcdDistGF) := by
  intro hG hGG hL hlo hrb hT
  obtain ⟨G', ⟨fl, lc, nh, gs, th, cr⟩⟩ := hG
  simp only at hGG hL
  subst hGG hL
  letI hG : HeapGS .hasLC etcdDistGF := ⟨G', ⟨fl, lc, nh, gs, th, cr⟩⟩
  haveI := Hctx hG
  haveI := etcdFsSemOk
  iintro - Hls Hgs Htok
  imod (prometheus.regKeys_alloc (GF := etcdDistGF) client.regQs client_regQsOk) with ⟨%γreg, Hregs⟩
  letI : prometheus.PromRegGS etcdDistGF := ⟨γreg⟩
  ihave Hns := prometheus.idToks_regsFree (GF := etcdDistGF) client.regQs $$ Hregs
  ihave Hown := ownInitializing_of_empty (client.getIsPkgInit (GF := etcdDistGF)) $$ Hgs
  imodintro
  unfold clientProg
  wp_apply (client.wp_initialize' _ client.getIsPkgInit_wf) $$ [Hown Hns] as ⟨-, #Hpkg⟩
  · iframe
  first
    | wp_bind (deploymentLit d)
    | (wp_pure; wp_bind (deploymentLit d))
  iapply wp_deploymentLit
  iintro %v #Hrepr
  -- `Orchestrator(d, j)`
  wp_func_call
  wp_call
  try wp_auto
  -- `MainDeployment(d, j, func() {})`
  wp_func_call
  wp_call
  try wp_func_lits
  try wp_auto
  wp_apply (wp_WellFormed v d Hfips) $$ [Hrepr] as %err %Herr
  · iframe #
  have hne : err ≠ interface.nil := fun h => Hd (Herr h)
  cases err with
  | nil => exact absurd rfl hne
  | ok i =>
    bad_finish hne
    all_goals (trace_state; sorry)

/-- **A client machine on a malformed deployment** (see the file header). -/
theorem nodeBootBad [cl_sem : client.Assumptions]
    (Hctx : ∀ hG : HeapGS .hasLC etcdDistGF, CtxErrsAt hG)
    (d : Deployment) (Hd : ¬ d.WellFormed) (Hfips : crypto.fips140.GodebugFips140Off) (n : Nat)
    (σ : state) [G : GooseGlobalGS .hasLC etcdDistGF] :
    Net.DistBootWpSL srvLevelK (2 ^ 28 - 1) (nodeProg d n) σ (iprop(True) : IProp etcdDistGF) := by
  intro hG hGG hL hlo hrb hT
  obtain ⟨G', ⟨fl, lc, nh, gs, th, cr⟩⟩ := hG
  simp only at hGG hL
  subst hGG hL
  letI hG : HeapGS .hasLC etcdDistGF := ⟨G', ⟨fl, lc, nh, gs, th, cr⟩⟩
  haveI := Hctx hG
  haveI := etcdFsSemOk
  iintro - Hls Hgs Htok
  imod (prometheus.regKeys_alloc (GF := etcdDistGF) client.regQs client_regQsOk) with ⟨%γreg, Hregs⟩
  letI : prometheus.PromRegGS etcdDistGF := ⟨γreg⟩
  ihave Hns := prometheus.idToks_regsFree (GF := etcdDistGF) client.regQs $$ Hregs
  ihave Hown := ownInitializing_of_empty (client.getIsPkgInit (GF := etcdDistGF)) $$ Hgs
  imodintro
  unfold nodeProg
  wp_apply (client.wp_initialize' _ client.getIsPkgInit_wf) $$ [Hown Hns] as ⟨-, #Hpkg⟩
  · iframe
  first
    | wp_bind (deploymentLit d)
    | (wp_pure; wp_bind (deploymentLit d))
  iapply wp_deploymentLit
  iintro %v #Hrepr
  -- `NodeDeployment(d, n)`
  wp_func_call
  wp_call
  wp_auto
  wp_apply (wp_WellFormed v d Hfips) $$ [Hrepr] as %err %Herr
  · iframe #
  have hne : err ≠ interface.nil := fun h => Hd (Herr h)
  cases err with
  | nil => exact absurd rfl hne
  | ok i =>
    bad_finish hne
    all_goals (trace_state; sorry)

end boot

/-- **`EtcdBootNCBad`**: on a malformed deployment every machine's boot program is safe from `True`
(`serverBootBad`, `clientBootBad`, `nodeBootBad`). `Hctx` (`context`'s errors as Go defines them,
`ContextReadErrs`, at every ghost state over the statement's local context) is a named hypothesis, not
a top-level premise: it is to be discharged by the per-function context axioms. -/
theorem etcdBootNCBad_holds
    (Hctx : ∀ [GoGlobalContext] [lctx : GoLocalContext] [go.Semantics]
      (hG : HeapGS .hasLC etcdDistGF), CtxErrsAt hG) :
    EtcdBootNCBad := by
  intro _ lctx _ _ _ _ _ _ _ _ _ _ d Hd σs σc σn Hfips _ hlo hb i m hm
  rcases machines_prog hm with ⟨k, σ, rfl⟩ | ⟨j, σ, rfl⟩ | ⟨n, σ, rfl⟩
  · exact serverBootBad (fun hG => Hctx hG) d Hd Hfips k σ
  · exact clientBootBad (fun hG => Hctx hG) d Hd Hfips j σ
  · exact nodeBootBad (fun hG => Hctx hG) d Hd Hfips n σ

end etcd_dist
end EtcdGrove
end Perennial

end
