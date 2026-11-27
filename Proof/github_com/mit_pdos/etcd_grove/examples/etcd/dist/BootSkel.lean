/- Lean-first (no Rocq counterpart).

# `etcd/dist`: the proof skeleton of `etcd_safe_nocrash` (`notes/etcd-dist-plan.md`, D9; the theorem is in `TopLevelRobustness.lean`)

Not closed: `etcd_safe_nocrash_of_boot` proves `etcd_robust_nocrash.spec` from two named hypotheses,
`EtcdBootNC` (a well-formed deployment: the start update from its addresses unset to a share per machine,
each machine's boot program safe from its share) and `EtcdBootNCBad` (a malformed one: every program
checks the deployment and returns), by the all-stable bridge over `etcdNetExts` with `Robust`'s thread
bound (`Net.robust_of_distBootILT`): each boot program is safe at the thread bound `etcdThreads` (which
gives the served member's `srvLevels`) and every receipt bound up to `etcdSteps` (`notes/etcd-dist-plan.md`
§14). No axiom and no `sorry`.

The crash form, at the end (moved here from `TopLevelRobustness.lean` on `etcd-safe-crash-r6`): `EtcdBootC`
and `EtcdBootCBad` (the members' generations' `Net.CrashBootWpGT`), and `etcd_safe_of_boot`, which proves
`etcd_robust.spec` from them by the crash bridge `robust_of_dist_crash_adequacy_etcdNet`.

What discharges `EtcdBootNC`, in later steps: the start from S2's names (`S2Holds etcdDistGF`, the members'
client addresses at the cluster's view: `members_svc_start`, O1 option B, `notes/etcd-dist-plan.md` §18.3), S5's (`S5Holds etcdDistGF`, the members' peer addresses:
`S5Draft.http_addr_set`) and D7's cluster start (`etcdClusterStart`, after the idutil split); the k-member
boot; the workloads' starts and boots (D8). The reduction from S2's and S5's names is written once the
interim S2 interface (the member's and client's shares, `notes/putget-dist-plan.md`) is fixed.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.TopLevelRobustness
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.DeploymentDefs
public import Net.Statement.DistBridgeExts
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.NetExtsCrash
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
theorem machines_fsInit [GoGlobalContext] [GoSemanticsFunctions] {d : Deployment} {σs σc σn : List state} {m : Expr × state}
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
abbrev BootPremises [GoGlobalContext] [GoSemanticsFunctions] [lctx : GoLocalContext] (d : Deployment) (σs σc σn : List state) :
    Prop :=
  ∃ boot : List LogEntry, BootFacts d boot ∧ EtcdEnv d ∧
    (σs.length = d.members.length ∧ ∀ p ∈ d.members.zip σs, ServerStart p.1 p.2) ∧
    (σc.length = d.workloads.length ∧ ∀ σ ∈ σc, ClientStart σ) ∧
    (σn.length = d.nodeList.length ∧ ∀ σ ∈ σn, ClientStart σ) ∧
    EtcdVerifyOff

/-- **The machines' boot WPs, for a well-formed deployment** (see the file header): at
`etcd_robust_nocrash.spec`'s premises, the start update from the deployment's addresses unset to a share
per machine from which its boot program is safe. -/
def EtcdBootNC : Prop :=
  ∀ [GoGlobalContext] [lctx : GoLocalContext] [sem : go.Semantics]
    [_root_.Perennial.errors.Assumptions] [_root_.Perennial.fmt.Assumptions]
    [server_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.Assumptions] [client_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]
    [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions] [go_etcd_io.etcd.cache.v3.Assumptions]
    [log.NewModel]
    (d : Deployment) (_Hd : d.WellFormed) (σs σc σn : List state)
    (_Hp : BootPremises d σs σc σn)
    (_Hfips : crypto.fips140.GodebugFips140Off),
    ∀ [GooseGlobalGS .hasLC etcdDistGF], receiptBound etcdDistGF ≤ etcdSteps →
      ⊢ ([∗list] a ∈ d.addrs, Net.addrUnset a) ={⊤}=∗
        ∃ Ps : Nat → IProp etcdDistGF,
          ⌜∀ (i : Nat) (m : Expr × state), (machines d σs σc σn)[i]? = some m →
            Net.DistBootWpSLT etcdThreads 0 etcdSteps m.1 m.2 (Ps i)⌝ ∗
          [∗list] i ↦ _m ∈ machines d σs σc σn, Ps i

/-- **The machines' boot WPs, for a malformed deployment**: every program checks the deployment first
(Go's `deployment.WellFormed`) and returns, so the start allocates nothing (no address) and each machine's
boot WP holds from `True`. Discharged after D2 from the validator's spec (`WellFormed(d) == nil` only if
`d.WellFormed`). -/
def EtcdBootNCBad : Prop :=
  ∀ [GoGlobalContext] [lctx : GoLocalContext] [sem : go.Semantics]
    [_root_.Perennial.errors.Assumptions] [_root_.Perennial.fmt.Assumptions]
    [server_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.Assumptions] [client_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]
    [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions] [go_etcd_io.etcd.cache.v3.Assumptions]
    [log.NewModel]
    (d : Deployment) (_Hd : ¬ d.WellFormed) (σs σc σn : List state)
    (_Hfips : crypto.fips140.GodebugFips140Off),
    ∀ [GooseGlobalGS .hasLC etcdDistGF], receiptBound etcdDistGF ≤ etcdSteps →
      ∀ (i : Nat) (m : Expr × state), (machines d σs σc σn)[i]? = some m →
        Net.DistBootWpSLT etcdThreads 0 etcdSteps m.1 m.2 (iprop(True) : IProp etcdDistGF)

/-- **`etcd_safe_nocrash` from the machines' boot WPs** (see the file header), by the all-stable bridge
over `etcdNetExts` (`Net.robust_of_distBootILT`, at no receipt floor): on a well-formed deployment at its addresses (valid and
distinct by `WellFormed`), on a malformed one at none; each machine's `FsInit` from the statement's
`ServerStart`/`ClientStart`, the network's start from `Robust`'s own initial states. -/
theorem etcd_safe_nocrash_of_boot (HS : EtcdBootNC) (HB : EtcdBootNCBad) :
    etcd_robust_nocrash.spec := by
  intro _ _ _ _ _ _ _ _ _ _ d boot Hbf Henv σs σc σn g Hσs Hσc Hσn HEnv Hfips
  have HI := etcdNetExts_initP g (machines d σs σc σn)
    (fun m hm => machines_fsInit Hσs.2 Hσc.2 Hσn.2 Hσs.1 hm)
  intro hfresh hg hl
  have Hnet : (extGlobal Net.netExt g.globalWorld).init ∧
      ∀ m ∈ machines d σs σc σn, (extLocal Net.netExt m.2.world).init :=
    ⟨hg.2.2.1, fun m hm => (hl m (by simpa using hm)).2.2.1⟩
  by_cases Hd : d.WellFormed
  · exact Net.robust_of_distBootILT (GF := etcdDistGF) d.addrs (machines d σs σc σn) g
      etcdThreads etcdSteps 0 (Nat.zero_le _) HI
      (fun _ hb => HS d Hd σs σc σn ⟨boot, Hbf, Henv, Hσs, Hσc, Hσn, HEnv⟩ Hfips hb)
      ⟨Hd.addrs.1, Hd.addrs.2, Hnet.1, Hnet.2⟩ hfresh hg hl
  · refine Net.robust_of_distBootILT (GF := etcdDistGF) [] (machines d σs σc σn) g
      etcdThreads etcdSteps 0 (Nat.zero_le _) HI
      (fun _ hb => ?_) ⟨List.nodup_nil, by simp, Hnet.1, Hnet.2⟩ hfresh hg hl
    iintro -
    imodintro
    iexists (fun _ => (iprop(True) : IProp etcdDistGF))
    isplitr
    · ipureintro
      exact HB d Hd σs σc σn Hfips hb
    · iapply (BigSepL.bigSepL_intro (P := (iprop(emp) : IProp etcdDistGF)) (fun _ _ _ => BI.true_intro))
      iempintro

section crash

-- (etcd-safe-crash-r6) the crash skeleton, moved here from `TopLevelRobustness.lean` (which imports
-- `BootBad.lean`, whose crash half needs these): the file semantics' `FsSemOk` instance as before
attribute [local instance] etcdFsSemOk

/-! ## The crash form: `etcd_safe` from the machines' boot WPs -/

/-- **The machines' boot WPs with crashing members, for a well-formed deployment** (the crashing analogue
of `EtcdBootNC`): at `etcd_robust.spec`'s premises, over `etcdNetExts` with D4b's crash interpretation of
the issue record (`etcdNetExtsCrashInterpD4b`), at the thread bound `etcdThreads` and every receipt bound
up to `etcdSteps`, the start update from the deployment's addresses unset to
- for each member `i`, a precondition `Pc i` of its generations (D6's `memberPc C cfg id`, at the names
  `C` the update allocates: chosen inside the update, since it names them), with its boot program safe in
  every generation (`Net.CrashBootWpGT` at `etcdFsSem`'s crash premise `etcdCQ`, the WAL's `W1`, and the
  issue record's crash rest `idIssueCrashStart`) and its first generation's `Pc i L` from the file start
  resources and the empty package state, and
- for each stable machine `j` (orchestrators, then client machines), a share `Ps j` with its boot
  program safe from it and its whole start (`Net.DistBootWpSLT`, as in `EtcdBootNC`). -/
def EtcdBootC : Prop :=
  ∀ [GoGlobalContext] [lctx : GoLocalContext] [sem : go.Semantics]
    [_root_.Perennial.errors.Assumptions] [_root_.Perennial.fmt.Assumptions]
    [server_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.Assumptions] [client_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]
    [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions] [go_etcd_io.etcd.cache.v3.Assumptions]
    [log.NewModel]
    (d : Deployment) (_Hd : d.WellFormed) (σs σc σn : List state)
    (_Hp : BootPremises d σs σc σn)
    (_Hfips : crypto.fips140.GodebugFips140Off),
    letI := etcdNetExtsCrashInterpD4b
    ∀ [GooseGlobalGS .hasLC etcdDistGF], receiptBound etcdDistGF ≤ etcdSteps →
      ⊢ ([∗list] a ∈ d.addrs, Net.addrUnset a) ={⊤}=∗
        ∃ (Pc : Nat → GooseLocalGS etcdDistGF → IProp etcdDistGF) (Ps : Nat → IProp etcdDistGF),
          ⌜∀ (i : Nat) (m : Expr × state), (servers d σs)[i]? = some m →
            Net.CrashBootWpGT etcdCQ (etcdIdCrashRest idIssue_crash_interp) etcdThreads 0 etcdSteps
              m.1 (Pc i)⌝ ∗
          ⌜∀ (j : Nat) (m : Expr × state), (clients d σc ++ nodeMachines d σn)[j]? = some m →
            Net.DistBootWpSLT etcdThreads 0 etcdSteps m.1 m.2 (Ps j)⌝ ∗
          ([∗list] i ↦ m ∈ servers d σs, ∀ L : GooseLocalGS etcdDistGF,
            ⌜L.goose_go_local_context = lctx⌝ -∗
            ⌜@ThreadGS.threadBound etcdDistGF L.goose_threadGS = etcdThreads⌝ -∗
            Net.fsStartResG L (extLocal Fs.fsExt m.2.world) -∗
            ownGoState (hG := L.goose_go_stateGS) ∅ ={⊤}=∗ Pc i L) ∗
          [∗list] j ↦ _m ∈ clients d σc ++ nodeMachines d σn, Ps j

/-- A generation's empty package state: the precondition of a member's generations on a malformed
deployment (its program initializes its package from it, checks the deployment and returns). -/
def emptyPkgs (L : GooseLocalGS etcdDistGF) : IProp etcdDistGF :=
  ownGoState (hG := L.goose_go_stateGS) ∅

/-- **The machines' boot WPs with crashing members, for a malformed deployment**: every program checks the
deployment first and returns, in every generation of a member (`Net.CrashBootWpGT` from the generation's
empty package state, `emptyPkgs`, which the crash gives back) and on every stable machine
(`Net.DistBootWpSLT` from `True`); the start allocates nothing (no address). -/
def EtcdBootCBad : Prop :=
  ∀ [GoGlobalContext] [lctx : GoLocalContext] [sem : go.Semantics]
    [_root_.Perennial.errors.Assumptions] [_root_.Perennial.fmt.Assumptions]
    [server_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.Assumptions] [client_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]
    [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions] [go_etcd_io.etcd.cache.v3.Assumptions]
    [log.NewModel]
    (d : Deployment) (_Hd : ¬ d.WellFormed) (σs σc σn : List state)
    (_Hfips : crypto.fips140.GodebugFips140Off),
    letI := etcdNetExtsCrashInterpD4b
    ∀ [GooseGlobalGS .hasLC etcdDistGF], receiptBound etcdDistGF ≤ etcdSteps →
      (∀ (i : Nat) (m : Expr × state), (servers d σs)[i]? = some m →
        Net.CrashBootWpGT etcdCQ (etcdIdCrashRest idIssue_crash_interp) etcdThreads 0 etcdSteps
          m.1 emptyPkgs) ∧
      ∀ (j : Nat) (m : Expr × state), (clients d σc ++ nodeMachines d σn)[j]? = some m →
        Net.DistBootWpSLT etcdThreads 0 etcdSteps m.1 m.2 (iprop(True) : IProp etcdDistGF)

/-- **`etcd_safe` from the machines' boot WPs** (the crash form of `etcd_safe_nocrash_of_boot`), by
Perennial's distributed crash adequacy with the thread bound on the execution
(`goose_dist_mixed_crash_adequacy_below`), restated as `Robust` over `etcdNetExts` with D4b's issue record
(`robust_of_dist_crash_adequacy_etcdNet idIssue_crash_interp`, at the thread bound `etcdThreads`, every
receipt bound up to `etcdSteps`, no receipt floor): the members crash, the orchestrators and client
machines do not; on a well-formed deployment at its addresses, on a malformed one at none; each
machine's `FsInit` from `ServerStart`/`ClientStart`. -/
theorem etcd_safe_of_boot (HS : EtcdBootC) (HB : EtcdBootCBad) : etcd_robust.spec := by
  intro _ _ _ _ _ _ _ _ _ _ _ d boot Hbf Henv σs σc σn g Hσs Hσc Hσn HEnv Hfips
  have Hfs : ∀ m, m ∈ servers d σs ++ (clients d σc ++ nodeMachines d σn) →
      Fs.FsInit (extLocal Fs.fsExt m.2.world) := fun m hm =>
    machines_fsInit Hσs.2 Hσc.2 Hσn.2 Hσs.1 (by simpa [machines, List.append_assoc] using hm)
  by_cases Hd : d.WellFormed
  · exact robust_of_dist_crash_adequacy_etcdNet idIssue_crash_interp (GF := etcdDistGF) d.addrs
      (servers d σs) (clients d σc ++ nodeMachines d σn) g etcdThreads etcdSteps 0 (Nat.zero_le _)
      Hd.addrs.1 Hd.addrs.2 Hfs
      (fun _ hb => HS d Hd σs σc σn ⟨boot, Hbf, Henv, Hσs, Hσc, Hσn, HEnv⟩ Hfips hb)
  · refine robust_of_dist_crash_adequacy_etcdNet idIssue_crash_interp (GF := etcdDistGF) []
      (servers d σs) (clients d σc ++ nodeMachines d σn) g etcdThreads etcdSteps 0 (Nat.zero_le _)
      List.nodup_nil (by simp) Hfs (fun _ hb => ?_)
    obtain ⟨Hc, Hst⟩ := HB d Hd σs σc σn Hfips hb
    iintro -
    imodintro
    iexists (fun _ (L : GooseLocalGS etcdDistGF) => ownGoState (hG := L.goose_go_stateGS) ∅),
      (fun _ => (iprop(True) : IProp etcdDistGF))
    isplitr
    · ipureintro
      exact Hc
    isplitr
    · ipureintro
      exact Hst
    isplitl
    · iapply (BigSepL.bigSepL_intro (P := (iprop(emp) : IProp etcdDistGF)) (fun _ _ _ => by
        iintro - %L %_ %_ - Hgs
        imodintro
        iexact Hgs))
      iempintro
    · iapply (BigSepL.bigSepL_intro (P := (iprop(emp) : IProp etcdDistGF)) (fun _ _ _ => BI.true_intro))
      iempintro

end crash

end etcd_dist
end EtcdGrove
end Perennial

end
