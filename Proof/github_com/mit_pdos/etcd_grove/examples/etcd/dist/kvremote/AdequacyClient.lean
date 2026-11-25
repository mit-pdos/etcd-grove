/- Lean-first (no Rocq counterpart).

# `dist/kvremote`: the orchestrator's and the client machines' boots (M1, `notes/etcd-dist-plan.md` §21.1, step 4)

The two client-side machine kinds of a well-formed `kv`-only deployment (`KvOnly`), safe from their boot shares at
`EtcdKvBootNC`'s bounds (`Net.DistBootWpSLT etcdThreads 0 etcdSteps`):
- `kvOrchBoot`: workload `j`'s orchestrator machine (`clientProg d j`), from `kvOrchPre ns w.ops`, the orchestrator's
  share at the global ghost state (`kvremote/Start.lean`'s `kv_start`, at the remote names `ρ` it allocated);
- `kvNodeBoot`: the `n`-th client machine (`nodeProg d n`), from `kvNodePre (W64 c) a eps`, its share at the global
  ghost state, `eps` the members' client addresses rotated by its index `c` in its workload. Its local part
  (`kvNodePreL`: `levelTok 0`, the thread bound) comes from the machine's thread token (`threadTok_level0`) and the
  thread bound `etcdThreads`.
Each is the machine's initialization (the registration rights, `client`'s package initialization, as `BootBad`'s
`clientBadWp`/`nodeBadWp`), the deployment's literal, then N7-kv's dispatch (`wp_OrchestratorKv`,
`wp_NodeDeploymentKv`, `client/KvLinked.lean`) at P9's linked `kvremote.wp_Orch` (its timeout specialized to the
dispatch's, `Orch.specWith`) and `kvremote.wp_Node` (`Node.specWith` at `kvNodePreL`).

No axiom, no `sorry`, no hypothesis beyond `EtcdKvBootNC`'s.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.BootBad
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.KvLinked
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.Link

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
open github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote
open github_com.mit_pdos.etcd_grove.examples.lib.remote

attribute [local instance] etcdNetExts etcdNetExtsSemantics etcdNetExtsInterp etcdNetExts_hasIdIssue
  etcdNetExts_hasFs etcdNetExts_hasNet etcdFsSem etcdFsSemOk GooseGlobalGS.gooseInvGS

/-- **Workload `j`'s orchestrator machine of a well-formed `kv`-only deployment** (see the file header), from the
orchestrator's share at workload `j`'s client machines `ns` and operation count. -/
theorem kvOrchBoot [GoGlobalContext] [lctx : GoLocalContext] [sem : go.Semantics]
    [cl_sem : client.Assumptions] [net.FieldAssumptions]
    (d : Deployment) (Hkv : KvOnly d) (Hfips : crypto.fips140.GodebugFips140Off)
    (j : Nat) (w : Workload) (ns : List GoString) (hj : j < 2 ^ 31)
    (hw : d.workloads[j]? = some w) (hns : d.nodes[j]? = some ns) (σ : state)
    [G : GooseGlobalGS .hasLC etcdDistGF] [π : NetProtoGS] (ρ : RemoteGS) :
    Net.DistBootWpSLT etcdThreads 0 etcdSteps (clientProg d j) σ
      (kvOrchPre (GF := etcdDistGF) (ρ := ρ) ns w.ops) := by
  intro hG hGG hL hlo hrb hT
  obtain ⟨G', ⟨fl, lc, nh, gs, th, cr⟩⟩ := hG
  simp only at hGG hL
  subst hGG hL
  letI hG : HeapGS .hasLC etcdDistGF := ⟨G', ⟨fl, lc, nh, gs, th, cr⟩⟩
  have hOrch : Orch.specWith (GF := etcdDistGF) (hG := hG)
      (kvOrchPre (GF := etcdDistGF) (Gg := hG.goose_globalGS) (ρ := ρ)) :=
    fun nodes ns ops => EtcdGrove.kvremote.wp_Orch (ρ := ρ) nodes ns ops (W64 120000000000)
  have hjZ : sint.Z (W64 j) = j := by word
  have hjN : sint.nat (W64 j) = j := by word
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
  wp_apply (wp_OrchestratorKv _ hOrch v d (W64 j)) $$ [Hshare]
  · (try iframe #)
    isplitr
    · ipureintro
      exact ⟨fun _ => Hkv, Hfips⟩
    · iintro %_
      rw [orchShare_eq _ d (W64 j) w ns (by omega) (by rw [hjN]; exact hw) (by rw [hjN]; exact hns)]
      iexact Hshare
  all_goals first | done | (ipureintro; rfl) | itrivial

/-- **The `n`-th client machine of a well-formed `kv`-only deployment** (see the file header), from its share at
its index `c` in its workload, its address `a` and the members' client addresses rotated by `c`. -/
theorem kvNodeBoot [GoGlobalContext] [lctx : GoLocalContext] [sem : go.Semantics]
    [cl_sem : client.Assumptions] [go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] [net.FieldAssumptions]
    (d : Deployment) (Hkv : KvOnly d) (Hfips : crypto.fips140.GodebugFips140Off)
    (n : Nat) (w : Workload) (c : Nat) (a : GoString) (hn : n < 2 ^ 31)
    (hl : d.nodeList[n]? = some (w, c, a)) (σ : state)
    [G : GooseGlobalGS .hasLC etcdDistGF] [π : NetProtoGS] (ρ : RemoteGS) :
    Net.DistBootWpSLT etcdThreads 0 etcdSteps (nodeProg d n) σ
      (kvNodePre (GF := etcdDistGF) (ρ := ρ) (W64 c) a (rotateL (d.members.map Member.client) c)) := by
  intro hG hGG hL hlo hrb hT
  obtain ⟨G', ⟨fl, lc, nh, gs, th, cr⟩⟩ := hG
  simp only at hGG hL
  subst hGG hL
  letI hG : HeapGS .hasLC etcdDistGF := ⟨G', ⟨fl, lc, nh, gs, th, cr⟩⟩
  haveI : ThreadBoundLe etcdDistGF (2 ^ 30) := ⟨by rw [hT]; unfold etcdThreads; omega⟩
  have hNode : Node.specWith (GF := etcdDistGF) (hG := hG) (kvNodePreL (GF := etcdDistGF) (ρ := ρ)) :=
    EtcdGrove.kvremote.wp_Node (ρ := ρ)
  have hnZ : sint.Z (W64 n) = n := by word
  have hnN : sint.nat (W64 n) = n := by word
  have htb : threadBound etcdDistGF ≤ 2 ^ 30 := by rw [hT]; unfold etcdThreads; omega
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
  wp_apply (wp_NodeDeploymentKv _ hNode v d (W64 n)) $$ [Hshare Hlt]
  · (try iframe #)
    isplitr
    · ipureintro
      exact ⟨fun _ => Hkv, Hfips⟩
    · iintro %_
      rw [nodeShare_eq _ d (W64 n) w c a (by omega) (by rw [hnN]; exact hl)]
      iunfold kvNodePreL
      isplitl [Hlt]
      · iexact Hlt
      isplitr
      · ipureintro
        exact htb
      · iexact Hshare
  all_goals first | done | (ipureintro; rfl) | itrivial

end etcd_dist
end EtcdGrove
end Perennial

end
