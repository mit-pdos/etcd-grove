/- Lean-first (no Rocq counterpart).

# `etcd/dist`: the premises of the distributed theorems are satisfiable, one by one

The per-premise witnesses of `etcd_robust.spec` and `etcd_robust_nocrash.spec`
(`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/TopLevelRobustness.lean`; #50's P12), shared by
every top-level witness of `examples/etcd/dist` (`TopLevelWitness.lean` here, M1's kv-only statement's):

- **the start states, for every deployment** whose member names pass `deployment.nameOk` (Go's
  `WellFormed` checks it): each member's machine with the two empty roots its member uses, its WAL area
  `/tmp/etcd-grove-wal/<name>.etcd` and its data directory `/tmp/etcd-grove-data/<name>.etcd`
  (`memberState`, `serverStates_start`: `Hσs`); each orchestrator's and client machine's with the root
  `/tmp` (`clientState`, `clientStates_start`: `Hσc`, `Hσn`); with no listener, no connection and an
  empty issue record, every machine a fresh process (`robustStart_nocrash`, `robustStart_crash`:
  `Robust`'s antecedents);
- **`EtcdEnv`**, at a deployment with no workload that needs no lease to expire (`AuthLease`,
  `LeaseCatchup`): its conditional `noExpiry` and its `peerRequests` placeholder hold, and what is left
  is exactly the conjunction of the opaque environment propositions (`etcdEnv_iff`), which no Lean proof
  can establish (`etc/premise-witness-baseline.txt`, class `opaque`);
- **`Hfips`, `HEnv`** (`GodebugFips140Off`, `EtcdVerifyOff`): stated over the opaque run values
  `godebugFips140`, `etcdVerifyEnv`; both hold when the variable is unset (`godebugFips140Off_unset`,
  `etcdVerifyOff_unset`);
- **a concrete deployment**, `pwDeployment` (`dist_test.go`'s shape: three members `wf-0`..`wf-2` at
  `10.77.{1,2,3}.1`, one KV workload with two client machines), its names valid (`pwDeployment_names`).

`BootFacts` (pinned to Go's `bootGo` values on the n5 line) is not witnessed here yet.
Untrusted: nothing but the witnesses uses it.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.DeploymentDefs
public import Proof.go_etcd_io.etcd.client.pkg.v3.verify.Env
public import Perennial.TrustedCode.crypto.fips140
public import Robustness.FsStart

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace etcd_dist
namespace witness

open Robustness Fs

attribute [local instance] etcdNetExts etcdNetExtsSemantics etcdNetExtsInterp etcdNetExts_hasIdIssue
  etcdNetExts_hasFs etcdNetExts_hasNet etcdFsSem

/-! ## Member names and their directories -/

/-- A name `deployment.nameOk` accepts has no `/` and no NUL. -/
theorem nameOk_bytes {n : GoString} (h : typed.nameOk n = true) : slashB ∉ n ∧ nulB ∉ n := by
  unfold typed.nameOk at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, List.all_eq_true,
    decide_eq_true_eq] at h
  refine ⟨fun hs => ?_, fun hs => ?_⟩
  · have := h.2 _ hs; simp [slashB] at this
  · have := h.2 _ hs; simp [nulB] at this

/-- `<name>.etcd` is a valid directory entry name. -/
theorem nameOk_etcd {n : GoString} (h : typed.nameOk n = true) : NameOk (n ++ go!".etcd") := by
  obtain ⟨hs, hn⟩ := nameOk_bytes h
  refine ⟨by simp, ?_, ?_, ?_, ?_⟩
  · intro he; have := congrArg List.length he; simp at this
  · intro he; have := congrArg List.length he; simp at this
  · simp only [List.mem_append, not_or]; exact ⟨hs, by simp [slashB]⟩
  · simp only [List.mem_append, not_or]; exact ⟨hn, by simp [nulB]⟩

theorem memberDataDir_join (n : GoString) :
    memberDataDir n = joinPath [] [go!"tmp", go!"etcd-grove-data", n ++ go!".etcd"] := by
  simp [memberDataDir, joinPath, slashB]

theorem walArea_join (n : GoString) :
    walAreaOf (memberDataDir n) = joinPath [] [go!"tmp", go!"etcd-grove-wal", n ++ go!".etcd"] := by
  rw [walAreaOf_memberDataDir]
  simp [joinPath, slashB]

theorem rootForm_memberDataDir {n : GoString} (h : typed.nameOk n = true) :
    RootForm (memberDataDir n) :=
  ⟨_, by simp, by
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · decide
    · decide
    · exact nameOk_etcd h, memberDataDir_join n⟩

theorem rootForm_walArea {n : GoString} (h : typed.nameOk n = true) :
    RootForm (walAreaOf (memberDataDir n)) :=
  ⟨_, by simp, by
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · decide
    · decide
    · exact nameOk_etcd h, walArea_join n⟩

/-- Two paths whose first `k` bytes differ, both at least `k` long: neither is the other or in its
tree. -/
theorem not_isUnder_of_take {x y : GoString} (k : Nat) (hx : k ≤ x.length)
    (hne : x.take k ≠ y.take k) : ¬ IsUnder x y := by
  rintro (rfl | hp)
  · exact hne rfl
  · apply hne
    obtain ⟨t, rfl⟩ := hp
    rw [List.append_assoc, List.take_append_of_le_length hx]

/-- The member's WAL area and data directory are apart. -/
theorem memberRoots_apart (n : GoString) :
    ¬ IsUnder (walAreaOf (memberDataDir n)) (memberDataDir n) ∧
      ¬ IsUnder (memberDataDir n) (walAreaOf (memberDataDir n)) := by
  rw [walAreaOf_memberDataDir]
  unfold memberDataDir
  constructor
  · exact not_isUnder_of_take 17 (by simp) (by simp)
  · exact not_isUnder_of_take 17 (by simp) (by simp)

/-! ## The members' machines -/

/-- The roots of the member `n`'s machine: its WAL area, then its data directory
(`etcdstart`'s `etcdAreaRoots [memberDataDir n]`). -/
def memberRoots (n : GoString) : List GoString := [walAreaOf (memberDataDir n), memberDataDir n]

/-- **The member `n`'s machine at the start**: a fresh process, its file system the two empty roots,
no listener, no connection, an empty issue record. -/
def memberState [GoLocalContext] (n : GoString) : state :=
  freshState ((∅ : IdIssueState), fsRoots (memberRoots n), (default : Net.NetLocal), ())

theorem memberRoots_init {n : GoString} (h : typed.nameOk n = true) : FsInit (fsRoots (memberRoots n)) := by
  obtain ⟨h1, h2⟩ := memberRoots_apart n
  refine fsInit_fsRoots _ ?_ ?_ ?_
  · simp only [memberRoots, List.nodup_cons, List.mem_singleton, List.not_mem_nil, not_false_eq_true,
      List.nodup_nil, and_true]
    intro he; exact h1 (Or.inl he.symm)
  · intro r hr
    simp only [memberRoots, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact rootForm_walArea h
    · exact rootForm_memberDataDir h
  · intro r hr r' hr' hne
    simp only [memberRoots, List.mem_cons, List.not_mem_nil, or_false] at hr hr'
    rcases hr with rfl | rfl <;> rcases hr' with rfl | rfl
    · exact absurd rfl hne
    · exact h1
    · exact h2
    · exact absurd rfl hne

theorem memberRoots_walAreas (n : GoString) :
    etcdWalAreasInit (fsRoots (memberRoots n)) [memberDataDir n] := by
  intro d hd
  simp only [List.mem_singleton] at hd
  subst hd
  refine ⟨⟨n, rfl⟩, ?_, ?_⟩
  · obtain ⟨j, hj⟩ := fsRoots_root (memberRoots n) (r := walAreaOf (memberDataDir n))
      (by simp [memberRoots])
    exact ⟨j, hj, fun b _ => fsRoots_entry _ _ _⟩
  · obtain ⟨j, hj⟩ := fsRoots_root (memberRoots n) (r := memberDataDir n) (by simp [memberRoots])
    exact ⟨j, hj, fun b => fsRoots_entry _ _ _⟩

/-- **`ServerStart`** holds of the member's machine at the start, for every valid name. -/
theorem memberState_start [GoLocalContext] (m : Member) (h : typed.nameOk m.name = true) :
    ServerStart m (memberState m.name) :=
  ⟨memberRoots_init h, memberRoots_walAreas m.name⟩

/-- The members' machines at the start, in the members' order. -/
def serverStates [GoLocalContext] (d : Deployment) : List state := d.members.map (fun m => memberState m.name)

/-- **`Hσs`** for every deployment whose member names are valid (Go's `WellFormed` checks it). -/
theorem serverStates_start [GoLocalContext] (d : Deployment) (h : ∀ m ∈ d.members, typed.nameOk m.name = true) :
    (serverStates d).length = d.members.length ∧
      ∀ p ∈ d.members.zip (serverStates d), ServerStart p.1 p.2 := by
  refine ⟨by simp [serverStates], ?_⟩
  intro p hp
  simp only [serverStates, List.zip_map_right, List.mem_map] at hp
  obtain ⟨⟨m, m'⟩, hmm, rfl⟩ := hp
  have he : m = m' := by
    obtain ⟨i, hi, hx⟩ := List.mem_iff_getElem.1 hmm
    simp only [List.getElem_zip, Prod.mk.injEq] at hx
    rw [← hx.1, ← hx.2]
  subst he
  exact memberState_start m (h m (List.of_mem_zip hmm).1)

/-! ## The orchestrators' and client machines -/

/-- The client machines' root, `/tmp`. -/
theorem tmp_rootForm : RootForm (slashB :: go!"tmp") := rootForm_one _ (by decide)

/-- **An orchestrator's or client machine at the start**: a fresh process, its file system the empty
root `/tmp`, no listener, no connection, an empty issue record. -/
def clientState [GoLocalContext] : state :=
  freshState ((∅ : IdIssueState), fsOneRoot (slashB :: go!"tmp"), (default : Net.NetLocal), ())

/-- **`ClientStart`** holds of it. -/
theorem clientState_start [GoLocalContext] : ClientStart clientState :=
  fsInit_fsOneRoot _ tmp_rootForm

def clientStates [GoLocalContext] (n : Nat) : List state := List.replicate n clientState

/-- **`Hσc`, `Hσn`** (`n` the number of workloads, of client machines). -/
theorem clientStates_start [GoLocalContext] (n : Nat) :
    (clientStates n).length = n ∧ ∀ σ ∈ clientStates n, ClientStart σ := by
  refine ⟨by simp [clientStates], ?_⟩
  intro σ hσ
  unfold clientStates at hσ
  rw [List.eq_of_mem_replicate hσ]
  exact clientState_start

/-! ## `Robust`'s antecedents -/

/-- The shared state at the start: no connection. -/
def initGlobal : GlobalState := ⟨((), (), (default : Net.NetGlobal), ()), ∅⟩

theorem mem_mapIdx_snd {α β : Type _} {f : Nat → α → β} {g : β → α} (hg : ∀ i a, g (f i a) = a)
    {l : List α} {x : β} (hx : x ∈ l.mapIdx f) : g x ∈ l := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
  rw [List.getElem_mapIdx, hg]
  exact List.getElem_mem _

/-- Every machine of the deployment, at these start states, is one of the two kinds. -/
theorem machine_state [GoGlobalContext] [GoLocalContext] [GoSemanticsFunctions] (d : Deployment) {m : Expr × state}
    (hm : m ∈ machines d (serverStates d) (clientStates d.workloads.length)
      (clientStates d.nodeList.length)) :
    (∃ n, m.2 = memberState n) ∨ m.2 = clientState := by
  simp only [machines, servers, clients, nodeMachines, List.mem_append] at hm
  rcases hm with (hm | hm) | hm
  · have := mem_mapIdx_snd (g := Prod.snd) (fun _ _ => rfl) hm
    simp only [serverStates, List.mem_map] at this
    obtain ⟨mm, _, he⟩ := this
    exact Or.inl ⟨mm.name, he.symm⟩
  · exact Or.inr (List.eq_of_mem_replicate (mem_mapIdx_snd (g := Prod.snd) (fun _ _ => rfl) hm))
  · exact Or.inr (List.eq_of_mem_replicate (mem_mapIdx_snd (g := Prod.snd) (fun _ _ => rfl) hm))

theorem start_state [GoGlobalContext] [lctx : GoLocalContext] {σ : state}
    (h : (∃ n, σ = memberState n) ∨ σ = clientState) : Fresh lctx σ ∧ extsInitLocal σ initGlobal := by
  rcases h with ⟨n, rfl⟩ | rfl
  · exact ⟨fresh_freshState _, by exts_init⟩
  · exact ⟨fresh_freshState _, by exts_init⟩

theorem initGlobal_init : extsInitGlobal initGlobal := by exts_init

/-- **`Robust`'s antecedents, no machine crashing** (`etcd_robust_nocrash`'s conclusion). -/
theorem robustStart_nocrash [GoGlobalContext] [GoLocalContext] [GoSemanticsFunctions] (d : Deployment) :
    RobustStart [] (machines d (serverStates d) (clientStates d.workloads.length)
      (clientStates d.nodeList.length)) initGlobal :=
  ⟨fun m hm => (start_state (machine_state d (by simpa using hm))).1, initGlobal_init,
    fun m hm => (start_state (machine_state d (by simpa using hm))).2⟩

/-- **`Robust`'s antecedents, the members crashing** (`etcd_robust`'s conclusion). -/
theorem robustStart_crash [GoGlobalContext] [GoLocalContext] [GoSemanticsFunctions] (d : Deployment) :
    RobustStart (servers d (serverStates d))
      (clients d (clientStates d.workloads.length) ++ nodeMachines d (clientStates d.nodeList.length))
      initGlobal := by
  have hm : ∀ m, m ∈ servers d (serverStates d) ++
      (clients d (clientStates d.workloads.length) ++ nodeMachines d (clientStates d.nodeList.length)) →
      m ∈ machines d (serverStates d) (clientStates d.workloads.length)
        (clientStates d.nodeList.length) := by
    intro m hm; simpa [machines, List.append_assoc] using hm
  exact ⟨fun m h => (start_state (machine_state d (hm m h))).1, initGlobal_init,
    fun m h => (start_state (machine_state d (hm m h))).2⟩

/-! ## `EtcdEnv` -/

/-- **`EtcdEnv` is the opaque environment propositions**, at a deployment with no workload that needs
no lease to expire: its `noExpiry` and `peerRequests` fields hold. -/
theorem etcdEnv_iff (d : Deployment) (h : ∀ w ∈ d.workloads, w.needsNoExpiry = false) :
    EtcdEnv d ↔ (authRecordsFit ∧ apply.backendUnderQuota ∧ grpcRepliesFit ∧ storage.diskOk ∧
      leasePeersOk) := by
  constructor
  · intro he; exact ⟨he.authRecords, he.underQuota, he.repliesFit, he.disk, he.leasePeers⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨h1, h2, h3, h4, h5, ?_, trivial⟩
    rintro ⟨w, hw, hn⟩
    rw [h w hw] at hn
    exact absurd hn (by decide)

theorem etcdEnv_of (d : Deployment) (h : ∀ w ∈ d.workloads, w.needsNoExpiry = false)
    (h1 : authRecordsFit) (h2 : apply.backendUnderQuota) (h3 : grpcRepliesFit) (h4 : storage.diskOk)
    (h5 : leasePeersOk) : EtcdEnv d :=
  (etcdEnv_iff d h).2 ⟨h1, h2, h3, h4, h5⟩

/-! ## The run's environment variables -/

/-- **`Hfips`** holds when `GODEBUG` carries no `fips140` setting. -/
theorem godebugFips140Off_unset (h : crypto.fips140.godebugFips140 = go!"") :
    crypto.fips140.GodebugFips140Off :=
  Or.inl h

/-- **`HEnv`** holds when `ETCD_VERIFY` is unset. -/
theorem etcdVerifyOff_unset (h : etcdVerifyEnv = go!"") : EtcdVerifyOff := by
  unfold EtcdVerifyOff; rw [h]; exact etcdVerifyOffValue_unset

/-! ## A concrete deployment -/

/-- **A deployment of `dist_test.go`'s shape**: three members `wf-0`, `wf-1`, `wf-2` at
`10.77.{1,2,3}.1` (peer port `2380`, client port `2379`), the token `wf-0`, the compactor off, auth
off, one KV workload of two clients, its client machines at `10.78.0.{1,2}`. -/
def pwDeployment : Deployment where
  members := [⟨go!"wf-0", go!"10.77.1.1:2380", go!"10.77.1.1:2379"⟩,
    ⟨go!"wf-1", go!"10.77.2.1:2380", go!"10.77.2.1:2379"⟩,
    ⟨go!"wf-2", go!"10.77.3.1:2380", go!"10.77.3.1:2379"⟩]
  token := go!"wf-0"
  cfg := ⟨go!"periodic", W64 0, W64 10000, W64 5000, false⟩
  workloads := [⟨W64 0, W64 2, W64 20⟩]
  nodes := [[go!"10.78.0.1:2379", go!"10.78.0.2:2379"]]

theorem pwDeployment_names : ∀ m ∈ pwDeployment.members, typed.nameOk m.name = true := by
  intro m hm
  simp only [pwDeployment, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl <;> decide

theorem pwDeployment_noExpiry : ∀ w ∈ pwDeployment.workloads, w.needsNoExpiry = false := by
  intro w hw
  simp only [pwDeployment, List.mem_singleton] at hw
  subst hw
  decide

end witness
end etcd_dist
end EtcdGrove
end Perennial

end
