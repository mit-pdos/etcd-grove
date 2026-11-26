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
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.MembersStart
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.AdequacyClient
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.AddrPlain

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic Robustness go_etcd_io.raft.v3 Net
open github_com.mit_pdos.etcd_grove.examples.etcd.dist
open github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote
open github_com.mit_pdos.etcd_grove.examples.lib.remote

attribute [local instance] etcdNetExts etcdNetExtsSemantics etcdNetExtsInterp etcdNetExts_hasIdIssue
  etcdNetExts_hasFs etcdNetExts_hasNet etcdFsSem GooseGlobalGS.gooseInvGS

/-- **M1 is the full statement with one more premise**: `etcd_safe_nocrash` implies
`etcd_kv_safe_nocrash`. The proof applies the full statement to M1's arguments and drops the scope, so it
fails to compile if the two statements differ in anything but `Hscope`. -/
theorem etcd_kv_safe_nocrash_of_full (H : etcd_robust_nocrash.spec) : etcd_kv_safe_nocrash.spec := by
  intro _ _ _ _ _ _ _ _ _ _ _ d _Hscope boot Hbf Henv σs σc σn g Hσs Hσc Hσn HEnv Hfips
  exact H d boot Hbf Henv σs σc σn g Hσs Hσc Hσn HEnv Hfips

/-- **The machines' boot WPs, for a well-formed deployment of M1's scope**: `EtcdBootNC` with the scope
`KvOnly d ∧ d.cfg.auth = false` as one more hypothesis. -/
def EtcdKvBootNC : Prop :=
  ∀ [GoGlobalContext] [lctx : GoLocalContext] [sem : go.Semantics]
    [_root_.Perennial.errors.Assumptions] [_root_.Perennial.fmt.Assumptions]
    [server_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.Assumptions] [client_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]
    [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions] [go_etcd_io.etcd.cache.v3.Assumptions]
    [log.NewModel]
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
  intro _ _ _ _ _ _ _ _ _ _ _ d Hscope boot Hbf Henv σs σc σn g Hσs Hσc Hσn HEnv Hfips
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
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions] [log.NewModel]
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
  exact server.member_boot_dist d Hd Hscope.2 boot Hbf Henv HEnv Hfips i d.members[i]
    (List.getElem?_eq_getElem hl) σs[i] Hst


/-! ## `EtcdKvBootNC`, discharged (§21.1 step 5) -/

section shape

theorem forall₂_mem_left' {α β : Type} {R : α → β → Prop} :
    ∀ {l1 : List α} {l2 : List β}, List.Forall₂ R l1 l2 → ∀ a ∈ l1, ∃ b ∈ l2, R a b
  | _, _, .nil, a, ha => by simp at ha
  | _, _, .cons h t, a, ha => by
      rcases List.mem_cons.1 ha with rfl | ha
      · exact ⟨_, List.mem_cons_self, h⟩
      · obtain ⟨b, hb, h'⟩ := forall₂_mem_left' t a ha
        exact ⟨b, List.mem_cons_of_mem _ hb, h'⟩

/-- **The shape of a well-formed `kv`-only deployment**: no workload, or one `kv` workload `w` with its client
machines `ns`, within `kv_start`'s bounds (`BoundsOk`, `nodeCount`; `Compatible`'s distinct kinds). -/
theorem kvOnly_shape {d : Deployment} (Hd : d.WellFormed) (hkv : KvOnly d) :
    (d.workloads = [] ∧ d.nodes = []) ∨
    ∃ (w : Workload) (ns : List GoString), d.workloads = [w] ∧ d.nodes = [ns] ∧ ns.length < 2 ^ 31 ∧
      0 ≤ sint.Z w.ops ∧ (ns.length : Int) * sint.Z w.ops < 2 ^ 60 := by
  have hnl := wellFormed_nodes_length Hd
  obtain ⟨t, ⟨-, -, -, hws, hnn⟩, hwf⟩ := Hd
  -- `WellFormed`'s conjuncts by their statements, not their positions
  have hcnt : ∀ p ∈ t.workloads.zip t.nodes, p.2.length = p.1.nodeCount := by
    grind [typed.Deployment.WellFormed]
  have hcomp : typed.Compatible t.workloads := by grind [typed.Deployment.WellFormed]
  have hbnd : ∀ tw ∈ t.workloads, tw.BoundsOk := by grind [typed.Deployment.WellFormed]
  have hkind : ∀ tw ∈ t.workloads, ∃ c o, tw = .kv c o := by
    intro tw htw
    obtain ⟨w, hw, he⟩ := forall₂_mem_left' hws tw htw
    have hk := hkv w hw
    cases tw with
    | kv c o => exact ⟨c, o, rfl⟩
    | _ => simp [typed.Workload.Encodes, hk] at he
  have hlen : t.workloads.length ≤ 1 := by
    have hnd := hcomp.1
    rcases htw : t.workloads with _ | ⟨a, _ | ⟨b, r⟩⟩
    · simp
    · simp
    · exfalso
      try rw [htw] at hnd
      try rw [htw] at hkind
      obtain ⟨c, o, rfl⟩ := hkind a (by simp)
      obtain ⟨c', o', rfl⟩ := hkind b (by simp)
      simp [typed.Workload.kind] at hnd
  have hdl : d.workloads.length = t.workloads.length := hws.length_eq.symm
  rcases hdw : d.workloads with _ | ⟨w, _ | ⟨w2, r⟩⟩
  · left
    try rw [hdw] at hnl
    exact ⟨by first | rfl | exact hdw, List.eq_nil_of_length_eq_zero (by simpa using hnl)⟩
  · right
    try rw [hdw] at hnl
    try rw [hdw] at hws
    obtain ⟨ns, hn⟩ : ∃ ns, d.nodes = [ns] := by
      rcases hn : d.nodes with _ | ⟨ns, _ | ⟨_, _⟩⟩
      · rw [hn] at hnl; simp at hnl
      · exact ⟨ns, rfl⟩
      · rw [hn] at hnl; simp at hnl
    rcases htw : t.workloads with _ | ⟨tw, tws⟩
    · try rw [htw] at hws
      cases hws
    · try rw [htw] at hws
      cases hws with
      | cons he hr =>
        cases hr
        obtain ⟨c, o, rfl⟩ := hkind tw (by rw [htw]; simp)
        obtain ⟨-, -, hops⟩ := he
        have hb := hbnd (.kv c o) (by rw [htw]; simp)
        simp only [typed.Workload.BoundsOk] at hb
        have hc := hcnt (.kv c o, ns) (by rw [htw, hnn, hn]; simp)
        simp only [typed.Workload.nodeCount] at hc
        refine ⟨w, ns, by first | rfl | exact hdw, hn, by omega, by omega, ?_⟩
        rw [hc, hops]
        exact_mod_cast hb.2
  · exfalso
    try rw [hdw] at hdl
    simp at hdl
    omega

theorem mem_zipIdx_fst {α : Type} : ∀ (l : List α) (s : Nat) (q : α × Nat), q ∈ l.zipIdx s → q.1 ∈ l
  | [], _, _, h => by simp [List.zipIdx] at h
  | a :: l, s, q, h => by
    simp only [List.zipIdx, List.mem_cons] at h
    rcases h with rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_zipIdx_fst l (s + 1) q h)

/-- A client machine of the one workload has one of its addresses. -/
theorem nodeList_addr {d : Deployment} {w : Workload} {ns : List GoString} (hw : d.workloads = [w])
    (hn : d.nodes = [ns]) {k : Nat} {w' : Workload} {c : Nat} {a : GoString}
    (hk : d.nodeList[k]? = some (w', c, a)) : a ∈ ns := by
  have hm : (w', c, a) ∈ d.nodeList := List.mem_of_getElem? hk
  simp only [Deployment.nodeList, hw, hn, List.zip_cons_cons, List.zip_nil_right, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.mem_map] at hm
  obtain ⟨q, hq, he⟩ := hm
  have : q.1 = a := by
    have := congrArg (fun x => x.2.2) he
    simpa using this
  rw [← this]
  exact mem_zipIdx_fst ns 0 q hq

theorem nodeList_length {d : Deployment} {w : Workload} {ns : List GoString} (hw : d.workloads = [w])
    (hn : d.nodes = [ns]) : d.nodeList.length = ns.length := by
  simp [Deployment.nodeList, hw, hn]

theorem mem_rotateL {α : Type} [Inhabited α] {xs : List α} {i : Nat} {x : α} (h : x ∈ rotateL xs i) :
    x ∈ xs := by
  unfold rotateL at h
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 h
  have hlen : 0 < xs.length := by have := List.mem_range.1 hj; omega
  have hk : (i + j) % xs.length < xs.length := Nat.mod_lt _ hlen
  first
    | (rw [getElem!_pos xs ((i + j) % xs.length) hk]; exact List.getElem_mem hk)
    | (simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some];
       exact List.getElem_mem hk)
    | simp [hk]

/-- The rotated client addresses of a well-formed deployment are plain endpoints. -/
theorem rotateL_plain {d : Deployment} (Hd : d.WellFormed) (c : Nat) :
    plainEndpoints (rotateL (d.members.map Member.client) c) := by
  obtain ⟨hne, -⟩ := Hd.members
  refine ⟨fun h => ?_, fun ep hep => ?_⟩
  · have := congrArg List.length h
    rw [rotateL_length, List.length_map] at this
    exact hne (List.eq_nil_of_length_eq_zero this)
  · have hmem := mem_rotateL hep
    obtain ⟨m, hm', rfl⟩ := List.mem_map.1 hmem
    apply addrOk_plainEndpoint
    apply Hd.addrs.2
    simp only [Deployment.addrs]
    exact List.mem_append_left _ (List.mem_flatMap.2 ⟨m, hm', by simp⟩)

end shape

section bigops
variable {GF : BundledGFunctors}

theorem bigSepL_idx' {A B : Type _} :
    ∀ (Φ : Nat → IProp GF) (l : List A) (l' : List B), l.length = l'.length →
      ([∗list] i ↦ _x ∈ l, Φ i) ⊢ [∗list] i ↦ _y ∈ l', Φ i
  | _, [], [], _ => by
    iintro -
    iapply BigSepL.bigSepL_nil.2
    iempintro
  | Φ, a :: l, b :: l', h => by
    iintro H
    ihave H := BigSepL.bigSepL_cons.1 $$ H
    icases H with ⟨H0, H⟩
    iapply BigSepL.bigSepL_cons.2
    isplitl [H0]
    · iexact H0
    iapply (bigSepL_idx' (fun i => Φ (i + 1)) l l' (by simpa using h))
    iexact H
  | _, [], _ :: _, h => by simp at h
  | _, _ :: _, [], h => by simp at h

theorem bigSepL_of_box {A : Type _} {P : IProp GF} [Persistent P] :
    ∀ (l : List A) (Φ : Nat → A → IProp GF), (∀ k x, l[k]? = some x → P ⊢ Φ k x) →
      P ⊢ [∗list] k ↦ x ∈ l, Φ k x
  | [], _, _ => by
    iintro -
    iapply BigSepL.bigSepL_nil.2
    iempintro
  | a :: l, Φ, h => by
    iintro #HP
    iapply BigSepL.bigSepL_cons.2
    isplitl []
    · iapply (h 0 a rfl)
      iexact HP
    · iapply (bigSepL_of_box l (fun k x => Φ (k + 1) x) (fun k x hk => h (k + 1) x hk))
      iexact HP

end bigops

section shares
variable [GoGlobalContext] [lctx : GoLocalContext] [sem : go.Semantics]
  [cl_sem : client.Assumptions] [server_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.Assumptions]
  [G : GooseGlobalGS .hasLC etcdDistGF] [π : NetProtoGS]

/-- **The machines' shares of M1's start** (one `kv` workload with client machines `ns`, `w.ops` operations):
member `i`'s `memberShareD`, then the orchestrator's `kvOrchPre`, then each client machine's `kvNodePre` at its index
`c`, its address `a` and the members' client addresses rotated by `c`. -/
def kvShares (d : Deployment) (boot : List LogEntry) (w : Workload) (ns : List GoString) (ρ : RemoteGS) (i : Nat) :
    IProp etcdDistGF :=
  if i < d.members.length then
    iprop(∃ c : ClusterNames, memberShareD (GF := etcdDistGF) c d (distPs d) (distCtxs d) boot i)
  else if i = d.members.length then kvOrchPre (GF := etcdDistGF) (ρ := ρ) ns w.ops
  else match d.nodeList[i - (d.members.length + 1)]? with
    | some (_, c, a) =>
      kvNodePre (GF := etcdDistGF) (ρ := ρ) (W64 c) a (rotateL (d.members.map Member.client) c)
    | none => iprop(True)

theorem kvShares_member {d : Deployment} {boot : List LogEntry} {w : Workload} {ns : List GoString}
    {ρ : RemoteGS} {i : Nat} (h : i < d.members.length) :
    kvShares d boot w ns ρ i =
      iprop(∃ c : ClusterNames, memberShareD (GF := etcdDistGF) c d (distPs d) (distCtxs d) boot i) := by
  unfold kvShares; rw [if_pos h]

theorem kvShares_orch {d : Deployment} {boot : List LogEntry} {w : Workload} {ns : List GoString}
    {ρ : RemoteGS} : kvShares d boot w ns ρ d.members.length = kvOrchPre (GF := etcdDistGF) (ρ := ρ) ns w.ops := by
  unfold kvShares; rw [if_neg (Nat.lt_irrefl _), if_pos rfl]

theorem kvShares_node {d : Deployment} {boot : List LogEntry} {w : Workload} {ns : List GoString}
    {ρ : RemoteGS} {k : Nat} {w' : Workload} {c : Nat} {a : GoString} (hk : d.nodeList[k]? = some (w', c, a)) :
    kvShares d boot w ns ρ (k + (d.members.length + 1)) =
      kvNodePre (GF := etcdDistGF) (ρ := ρ) (W64 c) a (rotateL (d.members.map Member.client) c) := by
  unfold kvShares
  rw [if_neg (show ¬ (k + (d.members.length + 1) < d.members.length) by omega),
    if_neg (show ¬ (k + (d.members.length + 1) = d.members.length) by omega),
    show k + (d.members.length + 1) - (d.members.length + 1) = k by omega, hk]

end shares

/-- **`EtcdKvBootNC` holds** (see the file header): the net extension's registry (`netProto_alloc`), then
- no workload: the members' start (`member_boot_dist_law`), each member's machine from its `memberShareD`;
- one `kv` workload: `kv_start_deployment` over `member_boot_dist_law`, the members' machines from their
  `memberShareD` (`kvMemberBoot`), the orchestrator's from `kvOrchPre` (`kvOrchBoot`), each client machine's from its
  `kvNodePre` (`kvNodeBoot`), built from the members' address facts and its address's `remoteAddr`. -/
theorem etcdKvBootNC_holds : EtcdKvBootNC := by
  intro gctx lctx sem errA fmtA srvA clA rpcA cacheA logA fieldA d Hd Hscope σs σc σn Hp Hfips G hb
  obtain ⟨boot, Hbf, Henv, Hσs, Hσc, Hσn, HEnv⟩ := Hp
  have hrb : receiptBound etcdDistGF ≤ 2 ^ 60 := by unfold etcdSteps at hb; omega
  have hsl : (servers d σs).length = d.members.length := by simp [servers, Hσs.1]
  iintro Hs
  imod netProto_alloc ⊤ with ⟨%π, #Hreg⟩
  rcases kvOnly_shape Hd Hscope.1 with ⟨hw0, hn0⟩ | ⟨w, ns, hw1, hn1, hb1, hb2, hb3⟩
  · -- no workload: the members only
    have hc0 : σc = [] := by
      have := Hσc.1; rw [hw0] at this; exact List.eq_nil_of_length_eq_zero (by simpa using this)
    have hn0' : σn = [] := by
      have := Hσn.1
      simp only [Deployment.nodeList, hw0, List.zip_nil_left, List.flatMap_nil, List.length_nil] at this
      exact List.eq_nil_of_length_eq_zero this
    subst hc0 hn0'
    simp only [Deployment.addrs, hn0, List.flatten_nil, List.append_nil]
    imod (member_boot_dist_law (GF := etcdDistGF) d Hd boot Hbf hrb) $$ Hreg Hs with ⟨%Γ, -, -, -, HMS⟩
    iunfold membersShareKv at HMS
    icases HMS with ⟨%c, -, HMS⟩
    imodintro
    iexists (fun i => iprop(∃ c : ClusterNames, memberShareD (GF := etcdDistGF) c d (distPs d) (distCtxs d) boot i))
    isplitr
    · ipureintro
      intro i m hm
      simp only [machines, clients, nodeMachines, List.mapIdx_nil, List.append_nil, servers,
        List.getElem?_mapIdx] at hm
      obtain ⟨σ, hσ, rfl⟩ := Option.map_eq_some_iff.1 hm
      exact kvMemberBoot d Hd Hscope boot Hbf Henv HEnv Hfips σs Hσs i σ hσ
    · simp only [machines, clients, nodeMachines, List.mapIdx_nil, List.append_nil]
      iapply (bigSepL_idx' (fun i => iprop(∃ c : ClusterNames,
        memberShareD (GF := etcdDistGF) c d (distPs d) (distCtxs d) boot i)) d.members (servers d σs) hsl.symm)
      iapply (BigSepL.bigSepL_impl (Ψ := fun i _ => iprop(∃ c : ClusterNames,
        memberShareD (GF := etcdDistGF) c d (distPs d) (distCtxs d) boot i))) $$ HMS
      imodintro
      iintro %k %x %_ H
      iexists c
      iexact H
  · -- one `kv` workload
    obtain ⟨σo, rfl⟩ : ∃ σo, σc = [σo] := by
      have := Hσc.1
      rw [hw1] at this
      rcases σc with _ | ⟨σo, _ | ⟨_, _⟩⟩
      · simp at this
      · exact ⟨σo, rfl⟩
      · simp at this
    have hσn : σn.length = ns.length := by rw [Hσn.1, nodeList_length hw1 hn1]
    have hcl : (servers d σs ++ clients d [σo]).length = d.members.length + 1 := by
      simp [servers, clients, Hσs.1]
    imod (kv_start_deployment (GF := etcdDistGF) d w ns hw1 hn1 Hd.addrs.1
        ⟨by unfold etcdSteps at hb; omega, hb1, hb2, hb3⟩ (membersShareKv (GF := etcdDistGF) d boot)
        (member_boot_dist_law (GF := etcdDistGF) d Hd boot Hbf hrb)) $$ Hreg Hs
      with ⟨%Γ, %ρ, %Hauth, HMS, Ho, #Hmem, #Ha⟩
    iunfold membersShareKv at HMS
    icases HMS with ⟨%c, -, HMS⟩
    have Hnodes : (iprop(□ membersAt (GF := etcdDistGF) (d.members.map Member.client) Γ ∗
        □ [∗list] a ∈ ns, remoteAddr (kvR (GF := etcdDistGF) Γ.kv) a) : IProp etcdDistGF) ⊢
        [∗list] k ↦ _x ∈ nodeMachines d σn, kvShares d boot w ns ρ (k + (servers d σs ++ clients d [σo]).length) :=
      bigSepL_of_box _ _ (fun k x hk => by
        try dsimp only
        have hkl : k < d.nodeList.length := by
          have := (List.getElem?_eq_some_iff.1 hk).1
          simp only [nodeMachines, List.length_mapIdx] at this
          rw [nodeList_length hw1 hn1]; omega
        obtain ⟨⟨w', c', a⟩, hx⟩ : ∃ x, d.nodeList[k]? = some x := ⟨_, List.getElem?_eq_getElem hkl⟩
        rw [hcl, kvShares_node hx]
        iintro ⟨#Hm, #Ha'⟩
        iunfold kvNodePre
        iexists Γ
        isplitr
        · ipureintro
          exact ⟨Hauth, rotateL_plain Hd c', EtcdGrove.rpctypesEtcdError_asTarget,
            etcd_putget_dist.wenv_nonempty mvcc.api.mvccApi_names_nonempty_law_holds⟩
        isplitl []
        · iapply (membersAt_sub Γ (fun a h => mem_rotateL h)) $$ Hm
        · obtain ⟨j, hj⟩ := List.getElem?_of_mem (nodeList_addr hw1 hn1 hx)
          iapply (BigSepL.bigSepL_lookup hj) $$ Ha')
    imodintro
    iexists kvShares d boot w ns ρ
    isplitr
    · ipureintro
      intro i m hm
      unfold machines at hm
      rcases Nat.lt_trichotomy i d.members.length with hi | hi | hi
      · rw [List.getElem?_append_left (by omega), List.getElem?_append_left (by omega)] at hm
        unfold servers at hm
        rw [List.getElem?_mapIdx] at hm
        obtain ⟨σ, hσ, rfl⟩ := Option.map_eq_some_iff.1 hm
        rw [kvShares_member hi]
        exact kvMemberBoot d Hd Hscope boot Hbf Henv HEnv Hfips σs Hσs i σ hσ
      · subst hi
        rw [List.getElem?_append_left (by omega), List.getElem?_append_right (by omega),
          hsl, Nat.sub_self] at hm
        simp only [clients, List.mapIdx_cons, List.mapIdx_nil, List.getElem?_cons_zero, Option.some.injEq] at hm
        subst hm
        rw [kvShares_orch]
        exact kvOrchBoot d Hscope.1 Hfips 0 w ns (by omega) (by rw [hw1]; rfl) (by rw [hn1]; rfl) σo ρ
      · obtain ⟨k, rfl⟩ : ∃ k, i = k + (d.members.length + 1) := ⟨i - (d.members.length + 1), by omega⟩
        rw [List.getElem?_append_right (by omega), hcl, Nat.add_sub_cancel] at hm
        unfold nodeMachines at hm
        rw [List.getElem?_mapIdx] at hm
        obtain ⟨σ, hσ, rfl⟩ := Option.map_eq_some_iff.1 hm
        have hkl : k < d.nodeList.length := by
          have := (List.getElem?_eq_some_iff.1 hσ).1
          rw [nodeList_length hw1 hn1]; omega
        obtain ⟨⟨w', c', a⟩, hx⟩ : ∃ x, d.nodeList[k]? = some x := ⟨_, List.getElem?_eq_getElem hkl⟩
        rw [kvShares_node hx]
        exact kvNodeBoot d Hscope.1 Hfips k w' c' a (by rw [nodeList_length hw1 hn1] at hkl; omega) hx σ ρ
    · unfold machines
      iapply BigSepL.bigSepL_append.2
      isplitl [HMS Ho]
      · iapply BigSepL.bigSepL_append.2
        isplitl [HMS]
        · iapply (bigSepL_idx' (kvShares d boot w ns ρ) d.members (servers d σs) hsl.symm)
          iapply (BigSepL.bigSepL_impl (Ψ := fun k _ => kvShares d boot w ns ρ k)) $$ HMS
          imodintro
          iintro %k %x %hk H
          rw [kvShares_member (List.getElem?_eq_some_iff.1 hk).1]
          iexists c
          iexact H
        · simp only [clients, List.mapIdx_cons, List.mapIdx_nil]
          iapply BigSepL.bigSepL_singleton.2
          rw [hsl, Nat.zero_add, kvShares_orch]
          iexact Ho
      · iapply Hnodes
        isplitr
        · imodintro
          iexact Hmem
        · imodintro
          iexact Ha

/-- **M1: `etcd_kv_safe_nocrash`** (`notes/etcd-dist-plan.md` §11.3, §21). -/
theorem etcd_kv_safe_nocrash : etcd_kv_safe_nocrash.spec :=
  etcd_kv_safe_nocrash_of_boot etcdKvBootNC_holds

end etcd_dist
end EtcdGrove
end Perennial

end
