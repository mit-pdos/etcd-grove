/- Lean-first (no Rocq counterpart).

# `etcd/dist`: per-premise satisfiability lemmas for the dist statements

These are the premises of `etcd_robust_nocrash.spec` (and of its scoped variants, M1's
`etcd_kv_safe_nocrash.spec`) at concrete values. A statement's `TopLevelWitness.lean` composes them
into its `premise_sat%` theorem (`Robustness/PremiseSat.lean`). The module is shared with P12 (#50), which
adds the remaining premises' lemmas here under these names.

The member is `putget_safe`'s witness member (`putget/TopLevelWitness.lean`): `putgetd`, peer address
`10.77.1.1:2380`, client address `10.77.1.1:2379`, in the cluster with token `putgetd`.

- `witnessMember`, `witnessToken`: that member and token.
- `witnessMember_id`: its id is the one Go computes, `memberId "http://10.77.1.1:2380" "putgetd" =
  pgId`, evaluated by the kernel.
- `bootFacts_witness`: `BootFacts` of any deployment whose members are `[witnessMember]` and whose token
  is `witnessToken`, at the peers `[pgId]`, the contexts `[pgCtx]` and the log `pgBoot` (`pgBootCore`).
- `serverStart_witness`: `ServerStart` of the member at `witnessMemberσ`, a fresh machine whose files are
  its two empty roots (data directory, WAL area).
- `clientStart_witness`: `ClientStart` at `witnessClientσ`, a fresh machine with the empty root `/tmp`.

P12's lemmas, for every deployment or the run's environment (#50):

- `memberState n`, `memberState_start`, `serverStates d`, `serverStates_start`: `ServerStart` of each
  member's machine (its two empty roots) at every deployment whose member names pass `typed.nameOk`
  (Go's `WellFormed` checks it); `witnessMemberσ` is `memberState`'s (`witnessMemberσ_eq`).
- `clientStates n`, `clientStates_start`: `ClientStart` of any number of `witnessClientσ` machines.
- `initGlobal`, `robustStart_nocrash`, `robustStart_crash`: `Robust`'s antecedents at those start states.
- `etcdEnv_iff`, `etcdEnv_of`: at a deployment with no `AuthLease`/`LeaseCatchup` workload, `EtcdEnv` is
  exactly the opaque environment propositions below (its `noExpiry` and `peerRequests` hold).
- `godebugFips140Off_unset`, `etcdVerifyOff_unset`: `Hfips` and `HEnv` hold when the variable is unset.
- `witnessDeployment` (the witness member, one KV workload, two client machines; its `BootFacts`
  `witnessDeployment_boot`) and `pwDeployment` (`dist_test.go`'s shape, three members; its names valid).

Not here, because no Lean proof can establish them: `EtcdEnv`'s fields (`authRecordsFit`,
`apply.backendUnderQuota`, `grpcRepliesFit`, `storage.diskOk`, `leasePeersOk`), `EtcdVerifyOff` and
`GodebugFips140Off`, all stated over opaque values. A witness leaves them out (class `opaque` of
`etc/premise-witness-baseline.txt`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.TopLevelRobustness
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.TopLevelWitness
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.DeploymentDefs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver Robustness Fs

attribute [local instance] etcdNetExts etcdNetExtsSemantics etcdNetExtsInterp etcdNetExts_hasIdIssue
  etcdNetExts_hasFs etcdNetExts_hasNet etcdFsSem

/-- The witness member: `putget_safe`'s witness member `putgetd`. -/
def witnessMember : Member :=
  ⟨etcd_putget_dist.name, etcd_putget_dist.peerA, etcd_putget_dist.clientA⟩

/-- The witness cluster's token, `putgetd` (the token `etcd_putget_dist.pgId` is computed in). -/
def witnessToken : GoString := etcd_putget_dist.name

/-- **The witness member's id is SHA-1's**, as `etcd_putget_dist.pgId_eq` (`crypto.sha1.sha1` evaluated by
the kernel, its message schedule's loops as folds). -/
theorem witnessMember_id :
    memberId (go!"http://" ++ witnessMember.peer) witnessToken = etcd_putget_dist.pgId := by
  unfold witnessMember witnessToken memberId membership.memberIdOf crypto.sha1.sha1 crypto.sha1.compress
  rw [show crypto.sha1.schedule = _ from funext crypto.sha1.schedule_eq]
  decide +kernel

/-- **`bootstrap`'s results** at a deployment of the witness member alone. -/
theorem bootFacts_witness (d : Deployment) (hm : d.members = [witnessMember])
    (ht : d.token = witnessToken) :
    BootFacts d [etcd_putget_dist.pgId] [etcd_putget_dist.pgCtx] etcd_putget_dist.pgBoot := by
  have hids : d.ids = [etcd_putget_dist.pgId] := by
    simp only [Deployment.ids, hm, ht, List.map_cons, List.map_nil, witnessMember_id]
  exact ⟨etcd_putget_dist.pgBootCore, by rw [hids]; try exact List.Perm.refl _⟩

/-- The witness member machine's start state: a fresh machine whose files are the member's two roots. -/
def witnessMemberσ [GoLocalContext] : state :=
  freshState ((∅ : IdIssueState), fsRoots etcd_putget_dist.memberRoots, (default : Net.NetLocal), ())

/-- A witness client machine's start state: a fresh machine with the root `/tmp`. -/
def witnessClientσ [GoLocalContext] : state :=
  freshState ((∅ : IdIssueState), fsOneRoot (slashB :: go!"tmp"), (default : Net.NetLocal), ())

theorem serverStart_witness [GoLocalContext] : ServerStart witnessMember witnessMemberσ :=
  ⟨etcd_putget_dist.memberRoots_init, etcd_putget_dist.memberRoots_walAreas⟩

theorem clientStart_witness [GoLocalContext] : ClientStart witnessClientσ :=
  fsInit_fsOneRoot _ etcd_putget_dist.tmp_rootForm

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

/-- **An orchestrator's or client machine at the start**: a fresh process, its file system the empty
root `/tmp`, no listener, no connection, an empty issue record (`witnessClientσ`, above). -/

def clientStates [GoLocalContext] (n : Nat) : List state := List.replicate n witnessClientσ

/-- **`Hσc`, `Hσn`** (`n` the number of workloads, of client machines). -/
theorem clientStates_start [GoLocalContext] (n : Nat) :
    (clientStates n).length = n ∧ ∀ σ ∈ clientStates n, ClientStart σ := by
  refine ⟨by simp [clientStates], ?_⟩
  intro σ hσ
  unfold clientStates at hσ
  rw [List.eq_of_mem_replicate hσ]
  exact clientStart_witness

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
    (∃ n, m.2 = memberState n) ∨ m.2 = witnessClientσ := by
  simp only [machines, servers, clients, nodeMachines, List.mem_append] at hm
  rcases hm with (hm | hm) | hm
  · have := mem_mapIdx_snd (g := Prod.snd) (fun _ _ => rfl) hm
    simp only [serverStates, List.mem_map] at this
    obtain ⟨mm, _, he⟩ := this
    exact Or.inl ⟨mm.name, he.symm⟩
  · exact Or.inr (List.eq_of_mem_replicate (mem_mapIdx_snd (g := Prod.snd) (fun _ _ => rfl) hm))
  · exact Or.inr (List.eq_of_mem_replicate (mem_mapIdx_snd (g := Prod.snd) (fun _ _ => rfl) hm))

theorem start_state [GoGlobalContext] [lctx : GoLocalContext] {σ : state}
    (h : (∃ n, σ = memberState n) ∨ σ = witnessClientσ) : Fresh lctx σ ∧ extsInitLocal σ initGlobal := by
  rcases h with ⟨n, rfl⟩ | rfl
  · exact ⟨fresh_freshState _, by exts_init⟩
  · exact ⟨fresh_freshState _, by simp only [witnessClientσ]; exts_init⟩

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

/-- The witness member's machine is `memberState`'s, at its name. -/
theorem witnessMemberσ_eq [GoLocalContext] : witnessMemberσ = memberState witnessMember.name := rfl

/-- **A deployment of the witness member alone** (so `bootFacts_witness` gives its `BootFacts`): the
token `witnessToken`, the compactor off, auth off, one KV workload of two clients, its client
machines at `10.78.0.{1,2}`. -/
def witnessDeployment : Deployment where
  members := [witnessMember]
  token := witnessToken
  cfg := ⟨go!"periodic", W64 0, W64 10000, W64 5000, false⟩
  workloads := [⟨W64 0, W64 2, W64 20⟩]
  nodes := [[go!"10.78.0.1:2379", go!"10.78.0.2:2379"]]

theorem witnessDeployment_names : ∀ m ∈ witnessDeployment.members, typed.nameOk m.name = true := by
  intro m hm
  simp only [witnessDeployment, List.mem_singleton] at hm
  subst hm
  decide

theorem witnessDeployment_boot :
    BootFacts witnessDeployment [etcd_putget_dist.pgId] [etcd_putget_dist.pgCtx] etcd_putget_dist.pgBoot :=
  bootFacts_witness witnessDeployment rfl rfl

theorem witnessDeployment_noExpiry : ∀ w ∈ witnessDeployment.workloads, w.needsNoExpiry = false := by
  intro w hw
  simp only [witnessDeployment, List.mem_singleton] at hw
  subst hw
  decide

end etcd_dist
end EtcdGrove
end Perennial

end
