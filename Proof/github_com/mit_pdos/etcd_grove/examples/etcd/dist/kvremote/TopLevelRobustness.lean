/- Lean-first (no Rocq counterpart).

# `etcd/dist/kvremote`: M1, `etcd_kv_safe_nocrash` (`notes/etcd-dist-plan.md` §11.3 step 6, §21)

- `etcd_kv_safe_nocrash_of_full`: the full statement `etcd_robust_nocrash.spec` implies M1's
  `etcd_kv_safe_nocrash.spec`. This checks that M1 is the full statement with one premise added.
- `EtcdKvBootNC`: `EtcdBootNC` (`dist/TopLevelRobustness.lean`) at the deployments of M1's scope.
- `etcd_kv_safe_nocrash_of_boot`: M1 from `EtcdKvBootNC`, by the same all-stable bridge as
  `etcd_safe_nocrash_of_boot` (`Net.robust_of_distBootILT`). A malformed deployment is handled by
  `etcdBootNCBad_holds` (`BootBad.lean`): every machine checks the deployment and returns.

No axiom and no `sorry`. What is left is `EtcdKvBootNC` (§21): the start (the net extension's names, the
cluster's start, `kvremote/Start.lean`'s kv part) and each machine's boot WP: the members' from N5's
`member_boot_dist`, the orchestrators' and the client machines' from N7-kv's dispatch
(`wp_OrchestratorKv`, `wp_NodeDeploymentKv`) at `kvremote`'s `wp_Orch`/`wp_Node`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.TopLevelRobustness
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.BootBad
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.AdequacyMember

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

/-- **M1 is the full statement with one more premise**: `etcd_safe_nocrash` implies
`etcd_kv_safe_nocrash`. The proof applies the full statement to M1's arguments and drops the scope, so it
fails to compile if the two statements differ in anything but `Hscope`. -/
theorem etcd_kv_safe_nocrash_of_full (H : etcd_robust_nocrash.spec) : etcd_kv_safe_nocrash.spec := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ d _Hscope boot Hbf Henv σs σc σn g Hσs Hσc Hσn HEnv Hfips
  exact H d boot Hbf Henv σs σc σn g Hσs Hσc Hσn HEnv Hfips

/-- **The machines' boot WPs, for a well-formed deployment of M1's scope**: `EtcdBootNC` with the scope
`KvOnly d ∧ d.cfg.auth = false` as one more hypothesis. -/
def EtcdKvBootNC : Prop :=
  ∀ [GoGlobalContext] [lctx : GoLocalContext] [sem : go.Semantics]
    [_root_.Perennial.errors.Assumptions] [_root_.Perennial.fmt.Assumptions]
    [server_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.Assumptions] [client_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]
    [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions] [go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] [log.NewModel] [net.FieldAssumptions]
    (d : Deployment) (_Hd : d.WellFormed) (_Hscope : KvOnly d ∧ d.cfg.auth = false)
    (σs σc σn : List state) (_Hp : BootPremises d σs σc σn)
    (_Hfips : crypto.fips140.GodebugFips140Off),
    ∀ [GooseGlobalGS .hasLC etcdDistGF], receiptBound etcdDistGF ≤ etcdSteps →
      ⊢ ([∗list] a ∈ d.addrs, Net.addrUnset a) ={⊤}=∗
        ∃ Ps : Nat → IProp etcdDistGF,
          ⌜∀ (i : Nat) (m : Expr × state), (machines d σs σc σn)[i]? = some m →
            Net.DistBootWpSLT etcdThreads 0 etcdSteps m.1 m.2 (Ps i)⌝ ∗
          [∗list] i ↦ _m ∈ machines d σs σc σn, Ps i

/-- **`etcd_kv_safe_nocrash` from the boot WPs of M1's well-formed deployments** (see the file header):
`etcd_safe_nocrash_of_boot`'s bridge, with the scope passed to `EtcdKvBootNC` and the malformed case from
`etcdBootNCBad_holds`. -/
theorem etcd_kv_safe_nocrash_of_boot (HS : EtcdKvBootNC) : etcd_kv_safe_nocrash.spec := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ d Hscope boot Hbf Henv σs σc σn g Hσs Hσc Hσn HEnv Hfips
  have HI := etcdNetExts_initP g (machines d σs σc σn)
    (fun m hm => machines_fsInit Hσs.2 Hσc.2 Hσn.2 Hσs.1 hm)
  intro hfresh hg hl
  have Hnet : (extGlobal Net.netExt g.globalWorld).init ∧
      ∀ m ∈ machines d σs σc σn, (extLocal Net.netExt m.2.world).init :=
    ⟨hg.2.2.1, fun m hm => (hl m (by simpa using hm)).2.2.1⟩
  by_cases Hd : d.WellFormed
  · exact Net.robust_of_distBootILT (GF := etcdDistGF) d.addrs (machines d σs σc σn) g
      etcdThreads etcdSteps 0 (Nat.zero_le _) HI
      (fun _ hb => HS d Hd Hscope σs σc σn ⟨boot, Hbf, Henv, Hσs, Hσc, Hσn, HEnv⟩ Hfips hb)
      ⟨Hd.addrs.1, Hd.addrs.2, Hnet.1, Hnet.2⟩ hfresh hg hl
  · refine Net.robust_of_distBootILT (GF := etcdDistGF) [] (machines d σs σc σn) g
      etcdThreads etcdSteps 0 (Nat.zero_le _) HI
      (fun _ hb => ?_) ⟨List.nodup_nil, by simp, Hnet.1, Hnet.2⟩ hfresh hg hl
    iintro -
    imodintro
    iexists (fun _ => (iprop(True) : IProp etcdDistGF))
    isplitr
    · ipureintro
      exact etcdBootNCBad_holds d Hd σs σc σn Hfips hb
    · iapply (BigSepL.bigSepL_intro (P := (iprop(emp) : IProp etcdDistGF)) (fun _ _ _ => BI.true_intro))
      iempintro

/-- **Member `i`'s machine's boot at M1's premises** (`EtcdKvBootNC`'s member part): N5's `member_boot_dist`
from its share `∃ c, memberShareD c d (distPs d) (distCtxs d) boot i`, its start state `σs[i]` given by
`Hσs` and the scope's `d.cfg.auth = false`. -/
theorem kvMemberBoot [GoGlobalContext] [lctx : GoLocalContext] [sem : go.Semantics]
    [_root_.Perennial.errors.Assumptions] [_root_.Perennial.fmt.Assumptions]
    [server_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions] [log.NewModel] [net.FieldAssumptions]
    (d : Deployment) (Hd : d.WellFormed) (Hscope : KvOnly d ∧ d.cfg.auth = false)
    (boot : List LogEntry) (Hbf : BootFacts d boot) (Henv : EtcdEnv d) (HEnv : EtcdVerifyOff)
    (Hfips : crypto.fips140.GodebugFips140Off) (σs : List state)
    (Hσs : σs.length = d.members.length ∧ ∀ p ∈ d.members.zip σs, ServerStart p.1 p.2)
    (i : Nat) (σ : state) (hi : σs[i]? = some σ)
    [G : GooseGlobalGS .hasLC etcdDistGF] [π : NetProtoGS] :
    Net.DistBootWpSLT etcdThreads 0 etcdSteps (serverProg d i) σ
      (iprop(∃ c : ClusterNames, memberShareD (GF := etcdDistGF) c d (distPs d) (distCtxs d) boot i)) := by
  obtain ⟨hiσ, rfl⟩ := List.getElem?_eq_some_iff.1 hi
  have hl : i < d.members.length := Hσs.1 ▸ hiσ
  have Hst := Hσs.2 (d.members[i], σs[i]) (List.mem_iff_getElem.mpr
    ⟨i, by simp [List.length_zip]; omega, by simp [List.getElem_zip]⟩)
  exact member_boot_dist d Hd Hscope.2 boot Hbf Henv HEnv Hfips i d.members[i]
    (List.getElem?_eq_getElem hl) σs[i] Hst

end etcd_dist
end EtcdGrove
end Perennial

end
