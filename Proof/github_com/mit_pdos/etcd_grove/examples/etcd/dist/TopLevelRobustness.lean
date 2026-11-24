/- Lean-first (no Rocq counterpart).

# `etcd/dist`: the proof skeleton of `etcd_safe_nocrash` (`notes/etcd-dist-plan.md`, D9)

Not closed: `etcd_safe_nocrash_of_boot` proves `etcd_robust_nocrash.spec` from two named hypotheses,
`EtcdBootNC` (a well-formed deployment: the start update from its addresses unset to a share per machine,
each machine's boot program safe from its share) and `EtcdBootNCBad` (a malformed one: every program
checks the deployment and returns), by the all-stable bridge over `etcdNetExts`
(`Net.robust_of_distBootIL`). No axiom and no `sorry`.

What discharges `EtcdBootNC`, in later steps: the start from S2's names (`S2Holds etcdDistGF`, the members'
client addresses: `cluster_svc_start`), S5's (`S5Holds etcdDistGF`, the members' peer addresses:
`S5Draft.http_addr_set`) and D7's cluster start (`etcdClusterStart`, after the idutil split); the k-member
boot; the workloads' starts and boots (D8). The reduction from S2's and S5's names is written once the
interim S2 interface (the member's and client's shares, `notes/putget-dist-plan.md`) is fixed.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.TopLevelRobustness
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.DeploymentDefs
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

/-- Every machine of a deployment starts with its files as on disk. -/
theorem machines_fsInit [GoGlobalContext] {d : Deployment} {σs σc σn : List state} {m : Expr × state}
    (Hσs : ∀ p ∈ d.members.zip σs, ServerStart p.1 p.2) (Hσc : ∀ σ ∈ σc, ClientStart σ)
    (Hσn : ∀ σ ∈ σn, ClientStart σ) (Hl : σs.length = d.members.length)
    (hm : m ∈ machines d σs σc σn) : Fs.FsInit (extLocal Fs.fsExt m.2.world) := by
  simp only [machines, servers, clients, nodeMachines, List.mem_append, List.mem_mapIdx] at hm
  rcases hm with (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩
  · have hi' : i < d.members.length := Hl ▸ hi
    exact (Hσs (d.members[i], σs[i]) (List.mem_iff_getElem.mpr
      ⟨i, by simp [List.length_zip]; omega, by simp [List.getElem_zip]⟩)).1
  · exact Hσc _ (List.getElem_mem hi)
  · exact Hσn _ (List.getElem_mem hi)

/-- The statement's premises except the deployment's well-formedness, as one hypothesis's binders. -/
abbrev BootPremises [GoGlobalContext] [lctx : GoLocalContext] (d : Deployment) (σs σc σn : List state) :
    Prop :=
  ∃ (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry),
    BootFacts d ps ctxs boot ∧ EtcdEnv d ∧
    (σs.length = d.members.length ∧ ∀ p ∈ d.members.zip σs, ServerStart p.1 p.2) ∧
    (σc.length = d.workloads.length ∧ ∀ σ ∈ σc, ClientStart σ) ∧
    (σn.length = d.nodeList.length ∧ ∀ σ ∈ σn, ClientStart σ) ∧
    (∀ m ∈ machines d σs σc σn, verifyEnvOff m.1)

/-- **The machines' boot WPs, for a well-formed deployment** (see the file header): at
`etcd_robust_nocrash.spec`'s premises, the start update from the deployment's addresses unset to a share
per machine from which its boot program is safe. -/
def EtcdBootNC : Prop :=
  ∀ [GoGlobalContext] [lctx : GoLocalContext] [sem : go.Semantics]
    [_root_.Perennial.errors.Assumptions] [_root_.Perennial.fmt.Assumptions]
    [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions] [go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] [log.NewModel] [net.FieldAssumptions]
    (d : Deployment) (_Hd : d.WellFormed) (σs σc σn : List state)
    (_Hp : BootPremises d σs σc σn) (_HEnvTok : ⊢ envVerifyOff (GF := etcdDistGF)),
    ∀ [GooseGlobalGS .hasLC etcdDistGF], srvLevelK ≤ receiptBound etcdDistGF →
      receiptBound etcdDistGF ≤ 2 ^ 28 - 1 →
      ⊢ ([∗list] a ∈ d.addrs, Net.addrUnset a) ={⊤}=∗
        ∃ Ps : Nat → IProp etcdDistGF,
          ⌜∀ (i : Nat) (m : Expr × state), (machines d σs σc σn)[i]? = some m →
            Net.DistBootWpSL srvLevelK (2 ^ 28 - 1) m.1 m.2 (Ps i)⌝ ∗
          [∗list] i ↦ _m ∈ machines d σs σc σn, Ps i

/-- **The machines' boot WPs, for a malformed deployment**: every program checks the deployment first
(Go's `deployment.WellFormed`) and returns, so the start allocates nothing (no address) and each machine's
boot WP holds from `True`. Discharged after D2 from the validator's spec (`WellFormed(d) == nil` only if
`d.WellFormed`). -/
def EtcdBootNCBad : Prop :=
  ∀ [GoGlobalContext] [lctx : GoLocalContext] [sem : go.Semantics]
    [_root_.Perennial.errors.Assumptions] [_root_.Perennial.fmt.Assumptions]
    [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions] [go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] [log.NewModel] [net.FieldAssumptions]
    (d : Deployment) (_Hd : ¬ d.WellFormed) (σs σc σn : List state),
    ∀ [GooseGlobalGS .hasLC etcdDistGF], srvLevelK ≤ receiptBound etcdDistGF →
      receiptBound etcdDistGF ≤ 2 ^ 28 - 1 →
      ∀ (i : Nat) (m : Expr × state), (machines d σs σc σn)[i]? = some m →
        Net.DistBootWpSL srvLevelK (2 ^ 28 - 1) m.1 m.2 iprop(True)

/-- **`etcd_safe_nocrash` from the machines' boot WPs** (see the file header), by the all-stable bridge
over `etcdNetExts` (`Net.robust_of_distBootIL`): on a well-formed deployment at its addresses (valid and
distinct by `WellFormed`), on a malformed one at none; each machine's `FsInit` from the statement's
`ServerStart`/`ClientStart`, the network's start from `Robust`'s own initial states. -/
theorem etcd_safe_nocrash_of_boot (HS : EtcdBootNC) (HB : EtcdBootNCBad) :
    etcd_robust_nocrash.spec := by
  intro _ _ _ _ _ _ _ _ _ _ d ps ctxs boot Hbf Henv σs σc σn g Hσs Hσc Hσn HEnv HEnvTok
  have HI := etcdNetExts_initP g (machines d σs σc σn)
    (fun m hm => machines_fsInit Hσs.2 Hσc.2 Hσn.2 Hσs.1 hm)
  intro hfresh hg hl
  have Hnet : (extGlobal Net.netExt g.globalWorld).init ∧
      ∀ m ∈ machines d σs σc σn, (extLocal Net.netExt m.2.world).init :=
    ⟨hg.2.2.1, fun m hm => (hl m (by simpa using hm)).2.2.1⟩
  by_cases Hd : d.WellFormed
  · exact Net.robust_of_distBootIL (GF := etcdDistGF) d.addrs (machines d σs σc σn) g
      (2 ^ 28) (2 ^ 28 - 1) srvLevelK (by unfold srvLevelK srvRevokeK; omega) HI
      (fun hlo hb => HS d Hd σs σc σn ⟨ps, ctxs, boot, Hbf, Henv, Hσs, Hσc, Hσn, HEnv⟩ HEnvTok hlo hb)
      ⟨Hd.addrs.1, Hd.addrs.2, Hnet.1, Hnet.2⟩ hfresh hg hl
  · refine Net.robust_of_distBootIL (GF := etcdDistGF) [] (machines d σs σc σn) g
      (2 ^ 28) (2 ^ 28 - 1) srvLevelK (by unfold srvLevelK srvRevokeK; omega) HI
      (fun hlo hb => ?_) ⟨List.nodup_nil, by simp, Hnet.1, Hnet.2⟩ hfresh hg hl
    iintro -
    imodintro
    iexists (fun _ => iprop(True))
    isplitr
    · ipure_intro
      exact HB d Hd σs σc σn hlo hb
    · iapply BigSepL.bigSepL_intro
      intro _ _ _
      iintro _
      iexact BI.true_intro

end etcd_dist
end EtcdGrove
end Perennial

end
