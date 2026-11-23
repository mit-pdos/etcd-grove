/- Lean-first (no Rocq counterpart).

# `etcd/dist`: the proof skeleton of `etcd_safe_nocrash` (`notes/etcd-dist-plan.md`, D9)

Not closed: `etcd_safe_nocrash_of_boot` proves `etcd_robust_nocrash.spec` from one named hypothesis,
`EtcdBootNC` (the start update from the deployment's addresses unset to a share per machine, each machine's
boot program safe from its share and its whole start), by the all-stable bridge over `etcdNetExts`
(`Net.robust_of_distBootIL`): `putget_safe_of_boot` over a deployment's list of machines (members,
orchestrators, client machines). No axiom and no `sorry`.

What discharges `EtcdBootNC`, in later steps: the start from S2's names (`S2Holds etcdDistGF`, the members'
client addresses: `cluster_svc_start`), S5's (`S5Holds etcdDistGF`, the members' peer addresses:
`S5Draft.http_addr_set`) and D7's cluster start (`etcdClusterStart`, after the idutil split); the k-member
boot; the workloads' starts and boots (D8). The reduction from S2's and S5's names is written once the
interim S2 interface (the member's and client's shares, `notes/putget-dist-plan.md`) is fixed.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.TopLevelRobustness
public import Net.Statement.DistBridgeExts
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.RevokeLevels

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI Iris.ProgramLogic Robustness go_etcd_io.raft.v3 Net

attribute [local instance] etcdNetExts etcdNetExtsSemantics etcdNetExtsInterp etcdNetExts_hasIdIssue
  etcdNetExts_hasFs etcdNetExts_hasNet etcdFsSem GooseGlobalGS.gooseInvGS

/-- Every machine of a deployment starts with no listener and its files as on disk. -/
theorem machines_start [GoGlobalContext] {d : Deployment} {σs σc σn : List state} {m : Expr × state}
    (Hσs : ∀ p ∈ d.members.zip σs, ServerStart p.1 p.2) (Hσc : ∀ σ ∈ σc, ClientStart σ)
    (Hσn : ∀ σ ∈ σn, ClientStart σ) (hm : m ∈ machines d σs σc σn) :
    (extLocal Net.netExt m.2.world).init ∧ Fs.FsInit (extLocal Fs.fsExt m.2.world) := by
  simp only [machines, servers, clients, nodeMachines, List.mem_append, List.mem_map] at hm
  rcases hm with (⟨⟨x, y⟩, hp, rfl⟩ | ⟨⟨x, y⟩, hp, rfl⟩) | ⟨⟨x, y⟩, hp, rfl⟩
  · exact ⟨(Hσs _ hp).1, (Hσs _ hp).2.1⟩
  · exact Hσc y (List.of_mem_zip hp).2
  · exact Hσn y (List.of_mem_zip hp).2

/-- **The machines' boot WPs** (see the file header): at `etcd_robust_nocrash.spec`'s premises, the start
update from the deployment's addresses unset to a share per machine from which its boot program is safe. -/
def EtcdBootNC : Prop :=
  ∀ [GoGlobalContext] [lctx : GoLocalContext] [sem : go.Semantics]
    [_root_.Perennial.errors.Assumptions] [_root_.Perennial.fmt.Assumptions]
    [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions] [go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] [log.NewModel] [net.FieldAssumptions]
    (d : Deployment) (_Hd : d.WellFormed)
    (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry) (_Hbf : BootFacts d ps ctxs boot)
    (_Henv : EtcdEnv d) (_Htb : TrustBoundary d ps ctxs boot) ∧
      ∀ n ∈ d.nodeList,
        prometheus.namesUnclaimed (nodeProg n.1 n.2.1 n.2.2 (d.members.map Member.client))
          clientNames)
    (σs σc σn : List state)
    (_Hσs : σs.length = d.members.length ∧ ∀ p ∈ d.members.zip σs, ServerStart p.1 p.2)
    (_Hσc : σc.length = d.workloads.length ∧ ∀ σ ∈ σc, ClientStart σ)
    (_Hσn : σn.length = d.nodeList.length ∧ ∀ σ ∈ σn, ClientStart σ)
    (_HEnv : ∀ m ∈ machines d σs σc σn, verifyEnvOff m.1)
    (_HEnvTok : ⊢ envVerifyOff (GF := etcdDistGF)),
    ∀ [GooseGlobalGS .hasLC etcdDistGF], srvLevelK ≤ receiptBound etcdDistGF →
      receiptBound etcdDistGF ≤ 2 ^ 28 - 1 →
      ⊢ ([∗list] a ∈ d.addrs, Net.addrUnset a) ={⊤}=∗
        ∃ Ps : Nat → IProp etcdDistGF,
          ⌜∀ (i : Nat) (m : Expr × state), (machines d σs σc σn)[i]? = some m →
            Net.DistBootWpSL srvLevelK (2 ^ 28 - 1) m.1 m.2 (Ps i)⌝ ∗
          [∗list] i ↦ _m ∈ machines d σs σc σn, Ps i

/-- **`etcd_safe_nocrash` from the machines' boot WPs** (see the file header), by the all-stable bridge
over `etcdNetExts` (`Net.robust_of_distBootIL`), each machine's `FsInit` and listener-free start from the
statement's `ServerStart`/`ClientStart`, the addresses' validity and distinctness from `WellFormed`. -/
theorem etcd_safe_nocrash_of_boot (HS : EtcdBootNC) : etcd_robust_nocrash.spec := by
  intro _ _ _ _ _ _ _ _ _ _ d Hd ps ctxs boot Hbf Henv Htb σs σc σn g Hσs Hσc Hσn Hg HEnv HEnvTok
  refine Net.robust_of_distBootIL (GF := etcdDistGF) d.addrs (machines d σs σc σn) g
    (2 ^ 28) (2 ^ 28 - 1) srvLevelK (by unfold srvLevelK srvRevokeK; omega) ?_
    (fun hlo hb => HS d Hd ps ctxs boot Hbf Henv Htb σs σc σn Hσs Hσc Hσn HEnv HEnvTok hlo hb) ?_
  · exact etcdNetExts_initP g _ (fun m hm => (machines_start Hσs.2 Hσc.2 Hσn.2 hm).2)
  · exact ⟨Hd.2.2.2.2.1, Hd.2.2.2.1, Hg, fun m hm => (machines_start Hσs.2 Hσc.2 Hσn.2 hm).1⟩

end etcd_dist
end EtcdGrove
end Perennial

end
