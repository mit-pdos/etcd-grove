/- Lean-first (no Rocq counterpart).

# `etcd/dist`: the orchestrators' and the client machines' boots over the full dispatch (F8, `notes/etcd-dist-plan.md` §27.4)

The two client-side machine kinds of a deployment, safe from their boot shares at `EtcdBootNC`'s bounds
(`Net.DistBootWpSLT etcdThreads 0 etcdSteps`), for every workload kind (M1's `kvremote/AdequacyClient.lean`
`kvOrchBoot`/`kvNodeBoot`, over the full dispatch):
- `orchBoot`: workload `j`'s orchestrator machine (`clientProg d j`), from `orchShareF d j` (`client/Shares.lean`: the
  start's `wlShare` of workload `j`, if `d` is well formed);
- `nodeBoot`: the `n`-th client machine (`nodeProg d n`), from `nodeShareF d n` (its `wlNodeShare`).

Each is the machine's initialization (the registration rights, `client`'s package initialization, as M1's), the
deployment's literal, then the linked dispatch (`wp_OrchestratorFull`, `wp_NodeDeploymentFull`,
`client/DispatchLinked.lean`), whose machine-level pure premises are discharged here: a watch environment
(`wenv_nonempty`), the thread bound from `etcdThreads`, the receipt bound from `etcdSteps`, `EtcdError` an
`errors.As` target (`rpctypesEtcdError_asTarget`); the client machine's level token from its thread token
(`threadTok_level0`). The deployment-level ones (bounds, plain endpoints) the dispatch derives from `WellFormed`
itself, so neither boot takes `d.WellFormed` nor `d.cfg.auth = false` (with auth on, a well-formed deployment's
only workload is `auth` or `authLease`, whose shares are `False`: D2).

No axiom, no `sorry`, no hypothesis beyond `EtcdBootNC`'s.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.BootBad
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.DispatchLinked
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.Defs

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
open github_com.mit_pdos.etcd_grove.examples.lib.remote

attribute [local instance] etcdNetExts etcdNetExtsSemantics etcdNetExtsInterp etcdNetExts_hasIdIssue
  etcdNetExts_hasFs etcdNetExts_hasNet etcdFsSem etcdFsSemOk GooseGlobalGS.gooseInvGS

/-- **Workload `j`'s orchestrator machine** (see the file header), from its share `orchShareF d j`. -/
theorem orchBoot [GoGlobalContext] [lctx : GoLocalContext] [sem : go.Semantics]
    [cl_sem : client.Assumptions] [go_etcd_io.etcd.cache.v3.Assumptions] [log.NewModel] [net.FieldAssumptions]
    (d : Deployment) (Hfips : crypto.fips140.GodebugFips140Off) (j : Nat) (σ : state)
    [G : GooseGlobalGS .hasLC etcdDistGF] [π : NetProtoGS] (ρ : RemoteGS) :
    Net.DistBootWpSLT etcdThreads 0 etcdSteps (clientProg d j) σ
      (orchShareF (GF := etcdDistGF) (ρ := ρ) d (W64 j)) := by
  intro hG hGG hL hlo hrb hT
  obtain ⟨G', ⟨fl, lc, nh, gs, th, cr⟩⟩ := hG
  simp only at hGG hL
  subst hGG hL
  letI hG : HeapGS .hasLC etcdDistGF := ⟨G', ⟨fl, lc, nh, gs, th, cr⟩⟩
  have hm : orchMachinePure (GF := etcdDistGF) :=
    ⟨etcd_putget_dist.wenv_nonempty mvcc.api.mvccApi_names_nonempty_law_holds,
      by rw [hT]; unfold etcdThreads; omega, by unfold etcdSteps at hrb; omega,
      EtcdGrove.rpctypesEtcdError_asTarget⟩
  iintro Hshare - Hgs Htok
  imod (prometheus.regKeys_alloc (GF := etcdDistGF) client.regQs client_regQsOk) with ⟨%γreg, Hregs⟩
  letI : prometheus.PromRegGS etcdDistGF := ⟨γreg⟩
  ihave Hns := prometheus.idToks_regsFree (GF := etcdDistGF) client.regQs $$ Hregs
  ihave Hown := ownInitializing_of_empty (client.getIsPkgInit (GF := etcdDistGF)) $$ Hgs
  imodintro
  unfold clientProg
  wp_apply (client.wp_initialize' _ client.getIsPkgInit_wf) $$ [Hown Hns] as ⟨-, #Hpkg⟩
  · iframe
  wp_bind (deploymentLit d)
  iapply wp_deploymentLit
  iintro %v #Hrepr
  wp_apply (wp_OrchestratorFull (GF := etcdDistGF) (hG := hG) (ρ := ρ) v d (W64 j)) $$ [Hshare Htok]
  · (try iframe #)
    isplitr [Hshare Htok]
    · ipureintro
      exact ⟨Hfips, hm⟩
    isplitl [Htok]
    · iexact Htok
    · iintro %_
      iexact Hshare
  all_goals first | done | (ipureintro; rfl) | itrivial

/-- **The `n`-th client machine** (see the file header), from its share `nodeShareF d n`. -/
theorem nodeBoot [GoGlobalContext] [lctx : GoLocalContext] [sem : go.Semantics]
    [cl_sem : client.Assumptions] [go_etcd_io.etcd.cache.v3.Assumptions] [log.NewModel] [net.FieldAssumptions]
    (d : Deployment) (Hfips : crypto.fips140.GodebugFips140Off) (n : Nat) (σ : state)
    [G : GooseGlobalGS .hasLC etcdDistGF] [π : NetProtoGS] (ρ : RemoteGS) :
    Net.DistBootWpSLT etcdThreads 0 etcdSteps (nodeProg d n) σ
      (nodeShareF (GF := etcdDistGF) (ρ := ρ) d (W64 n)) := by
  intro hG hGG hL hlo hrb hT
  obtain ⟨G', ⟨fl, lc, nh, gs, th, cr⟩⟩ := hG
  simp only at hGG hL
  subst hGG hL
  letI hG : HeapGS .hasLC etcdDistGF := ⟨G', ⟨fl, lc, nh, gs, th, cr⟩⟩
  haveI : ThreadBoundLe etcdDistGF (2 ^ 30) := ⟨by rw [hT]; unfold etcdThreads; omega⟩
  have hm : nodeMachinePure (GF := etcdDistGF) :=
    ⟨etcd_putget_dist.wenv_nonempty mvcc.api.mvccApi_names_nonempty_law_holds,
      by rw [hT]; unfold etcdThreads; omega, EtcdGrove.rpctypesEtcdError_asTarget⟩
  iintro Hshare - Hgs Htok
  icases (threadTok_level0 (GF := etcdDistGF)).1 $$ Htok with ⟨Hlt, -⟩
  imod (prometheus.regKeys_alloc (GF := etcdDistGF) client.regQs client_regQsOk) with ⟨%γreg, Hregs⟩
  letI : prometheus.PromRegGS etcdDistGF := ⟨γreg⟩
  ihave Hns := prometheus.idToks_regsFree (GF := etcdDistGF) client.regQs $$ Hregs
  ihave Hown := ownInitializing_of_empty (client.getIsPkgInit (GF := etcdDistGF)) $$ Hgs
  imodintro
  unfold nodeProg
  wp_apply (client.wp_initialize' _ client.getIsPkgInit_wf) $$ [Hown Hns] as ⟨-, #Hpkg⟩
  · iframe
  wp_bind (deploymentLit d)
  iapply wp_deploymentLit
  iintro %v #Hrepr
  wp_apply (wp_NodeDeploymentFull (GF := etcdDistGF) (hG := hG) (ρ := ρ) v d (W64 n)) $$ [Hshare Hlt]
  · (try iframe #)
    isplitr [Hshare Hlt]
    · ipureintro
      exact ⟨Hfips, hm⟩
    isplitl [Hlt]
    · iexact Hlt
    · iintro %_
      iexact Hshare
  all_goals first | done | (ipureintro; rfl) | itrivial

end etcd_dist
end EtcdGrove
end Perennial

end
