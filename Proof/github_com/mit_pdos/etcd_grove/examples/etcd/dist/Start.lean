/- Lean-first (no Rocq counterpart).

# `etcd/dist`: the full start, for a well-formed deployment with auth off (`notes/etcd-dist-plan.md` §27.2, F8)

`etcd_start`: from the net extension's registry (`regCtx`) and every address of the deployment unset, the remote
library's names `ρ` and every machine's share (`startShares d boot ρ i`, in the order of `machines`):
- member `i`: `∃ c, memberShareD c (lmOf d) d (distPs d) (distCtxs d) boot i`;
- orchestrator `j`: `orchAt d j`, its workload's `wlShare w eps ns` (`client/Shares.lean`) at the members' client
  addresses `eps` and its client machines `ns`;
- client machine `n`: `nodeAt d n`, its `wlNodeShare w (W64 c) a (rotateL eps c)`.
In order (§27.2): the cluster (`clusterStartDC` at `lmOf d` and `cmpOf d`), the persistent client facts
(`membersAt`, every member's `leaseMember`, `leaseMembers_of`; the cluster's KV invariant, `kvInv_of_clusterFacts`),
then by the deployment's class (`class_authOff`):
- E, Ls: the lease workloads' shares only (`lease_arm`); the KV half dropped;
- S, kv: M1's `kv_start` over `kvSys_boot` (the store `kvR` at the boot state); the client machines' `kvNodePre`;
- S, watch or cache: `watch_start` (the KV half whole, `σ₀.changes = [[]]` at the boot state, `bootSt_facts`; the
  writers' slot map with one call each, `mapCtx_alloc`, every client machine's address set to the writer service);
  the client machines' `writerNodePre`;
- P: `pfx_start` (`kvPfx_alloc` over `pg/`, `du/`, `cw/` with compact's discipline `cwOk`; putget's and durable's
  `kvPfxShare`, compact's `compactShare` once the cluster compacts at retention `1`, `cmpOf_compact`).
The workloads' exclusive shares go to the orchestrators by kind (`distribute`: the kinds are distinct,
`kinds_nodup`); every other workload of a class is a lease workload, whose share is persistent.

The pure premises of the client machines' shares that are not the deployment's (`Nonempty (WEnv GF)`, `EtcdError` an
`errors.As` target) are hypotheses: the linking module has them (M1's `etcdKvBootNC_holds`).

No axiom, no `sorry`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.DeploymentClass
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Shares
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.MembersStart

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI Iris.ProofMode Net client
open etcd_dist.view etcd_dist_client etcd_txnlin
open go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver
open github_com.mit_pdos.etcd_grove.examples.etcd.dist
open github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote
open github_com.mit_pdos.etcd_grove.examples.lib.remote

/-! ## Lists (pure) -/

section pure
variable [GooseExts]

theorem cls_mem_zipIdx_fst {α : Type} : ∀ (l : List α) (s : Nat) (q : α × Nat), q ∈ l.zipIdx s → q.1 ∈ l
  | [], _, _, h => by simp [List.zipIdx] at h
  | a :: l, s, q, h => by
    simp only [List.zipIdx, List.mem_cons] at h
    rcases h with rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (cls_mem_zipIdx_fst l (s + 1) q h)

/-- A list of lists empty but at `j` flattens to its `j`-th. -/
theorem cls_flatten_single {α : Type} :
    ∀ (L : List (List α)) (j : Nat) (x : List α), L[j]? = some x →
      (∀ (j' : Nat) (y : List α), L[j']? = some y → j' ≠ j → y = []) → L.flatten = x
  | [], _, _, h, _ => by simp at h
  | a :: L, 0, x, h, ho => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    have : L.flatten = [] := List.flatten_eq_nil_iff.2 (fun y hy => by
      obtain ⟨i, hi⟩ := List.getElem?_of_mem hy
      exact ho (i + 1) y (by simpa using hi) (by omega))
    simp [this]
  | a :: L, j + 1, x, h, ho => by
    simp only [List.getElem?_cons_succ] at h
    have ha : a = [] := ho 0 a rfl (by omega)
    subst ha
    simp only [List.flatten_cons, List.nil_append]
    exact cls_flatten_single L j x h (fun j' y hy hne => ho (j' + 1) y (by simpa using hy) (by omega))

/-- No client machine when every node list is empty. -/
theorem nodeList_nil {d : Deployment} (h : ∀ ns ∈ d.nodes, ns = []) : d.nodeList = [] := by
  unfold Deployment.nodeList
  rw [List.flatMap_eq_nil_iff]
  intro p hp
  obtain ⟨a, b⟩ := p
  have hb : b = [] := h b (List.of_mem_zip hp).2
  subst hb
  rfl

/-- **A sole writer's client machines** (class S): every client machine is one of the sole writer's. -/
theorem nodeList_sole {d : Deployment} {j : Nat} {s : Workload} {ns : List GoString}
    (hj : d.workloads[j]? = some s) (hns : d.nodes[j]? = some ns)
    (hoth : ∀ (j' : Nat) (ns' : List GoString), d.nodes[j']? = some ns' → j' ≠ j → ns' = [])
    {n : Nat} {w : Workload} {c : Nat} {a : GoString} (hn : d.nodeList[n]? = some (w, c, a)) :
    w = s ∧ a ∈ ns := by
  have hm := List.mem_of_getElem? hn
  unfold Deployment.nodeList at hm
  obtain ⟨p, hp, hq⟩ := List.mem_flatMap.1 hm
  obtain ⟨q, hq, he⟩ := List.mem_map.1 hq
  simp only [Prod.mk.injEq] at he
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hp
  obtain ⟨h1, h2⟩ := List.getElem?_zip_eq_some.1 hi
  by_cases hij : i = j
  · subst hij
    rw [hj] at h1
    rw [hns] at h2
    have e1 : s = p.1 := Option.some.inj h1
    have e2 : ns = p.2 := Option.some.inj h2
    refine ⟨he.1.symm.trans e1.symm, ?_⟩
    rw [← he.2.2, e2]
    exact cls_mem_zipIdx_fst _ _ _ hq
  · have h0 := hoth i p.2 h2 hij
    rw [h0] at hq
    simp at hq

/-- **The boot state's KV**: no key-value, one revision of no change (`σ₀.changes = [[]]`), revision `1`. -/
theorem bootSt_facts (γk : KVNames) (hlog : γk.log0 = [[], []]) (ps : List w64) (bl : List EntryM)
    (hb : srvBootLogOk ps bl) :
    (kvModelSt γk (bootEntries bl)).kvs = [] ∧ (kvModelSt γk (bootEntries bl)).changes = [[]] ∧
      (kvModelSt γk (bootEntries bl)).rev = 1 := by
  have h : kvModel γk (bootEntries bl) = [[], []] := by
    unfold kvModel
    rw [linkv.kvRaftOf_boot _ _ _ (fun _ _ => True) ps bl hb, hlog]
  unfold kvModelSt
  rw [h]
  refine ⟨?_, rfl, ?_⟩
  · rw [kvStateOf_kvs]; rfl
  · rw [kvStateOf_rev]; rfl

/-- The shared KV's disciplines (F5): compact's (`cwOk`) at `cw/`, none elsewhere. -/
def pfxOk (p : GoString) : mvcc.Change → Prop :=
  if p = compactPfx then cwOk else fun _ => True

end pure

/-! ## The shares of the start -/

section shares
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext] [GoLocalContext] [sem : go.Semantics]
variable [go_etcd_io.etcd.client.v3.Assumptions] [go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions] [go_etcd_io.raft.v3.Assumptions]
variable [github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.Assumptions]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS .hasLC GF] [π : NetProtoGS] [ρ : RemoteGS]

/-- **Orchestrator `j`'s share**: its workload's `wlShare` at the members' client addresses and its client
machines (`orchShareF d (W64 j)` for `j < 2 ^ 63`). -/
def orchAt (d : Deployment) (j : Nat) : IProp GF :=
  match d.workloads[j]?, d.nodes[j]? with
  | some w, some ns => wlShare (Gg := Gg) w (d.members.map Member.client) ns
  | _, _ => iprop(True)

/-- **Client machine `n`'s share**: its `wlNodeShare` at its index `c` in its workload, its address, and the
members' client addresses rotated by `c` (`nodeShareF d (W64 n)` for `n < 2 ^ 63`). -/
def nodeAt (d : Deployment) (n : Nat) : IProp GF :=
  match d.nodeList[n]? with
  | some (w, c, a) => wlNodeShare (Gg := Gg) w (W64 c) a (rotateL (d.members.map Member.client) c)
  | none => iprop(True)

/-- **Every machine's share of the start** (see the file header), in `machines`' order: the members, then the
orchestrators, then the client machines. -/
def startShares (d : Deployment) (boot : List LogEntry) (i : Nat) : IProp GF :=
  if i < d.members.length then
    iprop(∃ c : ClusterNames, memberShareD (G := Gg) c (lmOf d) d (distPs d) (distCtxs d) boot i)
  else if i < d.members.length + d.workloads.length then orchAt (Gg := Gg) d (i - d.members.length)
  else nodeAt (Gg := Gg) d (i - d.members.length - d.workloads.length)

theorem orchAt_eq {d : Deployment} {j : Nat} {w : Workload} {ns : List GoString}
    (hw : d.workloads[j]? = some w) (hns : d.nodes[j]? = some ns) :
    orchAt (Gg := Gg) d j = wlShare (Gg := Gg) w (d.members.map Member.client) ns := by
  unfold orchAt; rw [hw, hns]

theorem nodeAt_eq {d : Deployment} {n : Nat} {w : Workload} {c : Nat} {a : GoString}
    (hn : d.nodeList[n]? = some (w, c, a)) :
    nodeAt (Gg := Gg) d n = wlNodeShare (Gg := Gg) w (W64 c) a (rotateL (d.members.map Member.client) c) := by
  unfold nodeAt; rw [hn]

theorem W64_nat_bounds (j : Nat) (hj : j < 2 ^ 63) : 0 ≤ sint.Z (W64 (j : Int)) ∧ sint.nat (W64 (j : Int)) = j := by
  have h : sint.Z (W64 (j : Int)) = (j : Int) := by word
  refine ⟨by omega, ?_⟩
  first | (unfold sint.nat; rw [h]; simp) | word

/-- **Orchestrator `j`'s share is the dispatch's** (`orchShareF` at the Go index `W64 j`). -/
theorem orchShareF_at (d : Deployment) (j : Nat) (hj : j < 2 ^ 63) :
    orchShareF (Gg := Gg) d (W64 (j : Int)) = orchAt (Gg := Gg) d j := by
  obtain ⟨h0, hn⟩ := W64_nat_bounds j hj
  unfold orchShareF orchAt
  rw [if_pos h0, hn]
  rcases d.workloads[j]? with _ | w <;> rcases d.nodes[j]? with _ | ns <;> rfl

/-- **Client machine `n`'s share is the dispatch's** (`nodeShareF` at the Go index `W64 n`). -/
theorem nodeShareF_at (d : Deployment) (n : Nat) (hn : n < 2 ^ 63) :
    nodeShareF (Gg := Gg) d (W64 (n : Int)) = nodeAt (Gg := Gg) d n := by
  obtain ⟨h0, hn'⟩ := W64_nat_bounds n hn
  unfold nodeShareF nodeAt
  rw [if_pos h0, hn']
  rcases d.nodeList[n]? with _ | ⟨w, c, a⟩ <;> rfl

theorem startShares_member {d : Deployment} {boot : List LogEntry} {i : Nat} (h : i < d.members.length) :
    startShares (Gg := Gg) d boot i =
      iprop(∃ c : ClusterNames, memberShareD (G := Gg) c (lmOf d) d (distPs d) (distCtxs d) boot i) := by
  unfold startShares; rw [if_pos h]

theorem startShares_orch {d : Deployment} {boot : List LogEntry} {j : Nat} (h : j < d.workloads.length) :
    startShares (Gg := Gg) d boot (d.members.length + j) = orchAt (Gg := Gg) d j := by
  unfold startShares
  rw [if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left]

theorem startShares_node {d : Deployment} {boot : List LogEntry} (n : Nat) :
    startShares (Gg := Gg) d boot (d.members.length + d.workloads.length + n) = nodeAt (Gg := Gg) d n := by
  unfold startShares
  rw [if_neg (by omega), if_neg (by omega),
    show d.members.length + d.workloads.length + n - d.members.length - d.workloads.length = n by omega]

/-- Workload `j`'s orchestrator share, with its client machines. -/
theorem startShares_orch' {d : Deployment} (Hd : d.WellFormed) {boot : List LogEntry} {j : Nat} {w : Workload}
    (hw : d.workloads[j]? = some w) : ∃ ns, d.nodes[j]? = some ns ∧
      startShares (Gg := Gg) d boot (d.members.length + j) =
        wlShare (Gg := Gg) w (d.members.map Member.client) ns := by
  have hj : j < d.workloads.length := (List.getElem?_eq_some_iff.1 hw).1
  have hjn : j < d.nodes.length := by rw [wellFormed_nodes_length Hd]; exact hj
  refine ⟨d.nodes[j], List.getElem?_eq_getElem hjn, ?_⟩
  rw [startShares_orch hj, orchAt_eq hw (List.getElem?_eq_getElem hjn)]

end shares

/-! ## The start's pieces -/

section start
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext] [GoLocalContext] [sem : go.Semantics]
variable [go_etcd_io.etcd.client.v3.Assumptions] [go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions] [go_etcd_io.raft.v3.Assumptions]
variable [github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.Assumptions]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS .hasLC GF] [π : NetProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **The workloads' shares, by kind** (pure in the logic): with distinct kinds, the exclusive resources `R k`
of the kinds `K` (distinct) go to the workloads of those kinds, a persistent `P` to the others. -/
theorem distribute {A : Type} (key : A → w64) (R : w64 → IProp GF) (P : IProp GF) [Persistent P] :
    ∀ (l : List A) (K : List w64) (F : Nat → A → IProp GF), K.Nodup → (l.map key).Nodup →
      (∀ k x, l[k]? = some x → key x ∈ K → R (key x) ⊢ F k x) →
      (∀ k x, l[k]? = some x → key x ∉ K → P ⊢ F k x) →
      P ∗ ([∗list] k ∈ K, R k) ⊢ [∗list] k ↦ x ∈ l, F k x
  | [], _, _, _, _, _, _ => by
    iintro ⟨-, -⟩
    iapply BigSepL.bigSepL_nil.2
    iempintro
  | x :: l, K, F, hK, hl, h1, h2 => by
    simp only [List.map_cons] at hl
    obtain ⟨hxl, hl'⟩ := List.nodup_cons.1 hl
    have hne : ∀ k y, l[k]? = some y → key y ≠ key x := fun k y hy e =>
      hxl (e ▸ List.mem_map_of_mem (List.mem_of_getElem? hy))
    by_cases hx : key x ∈ K
    · have hp : K.Perm (key x :: K.erase (key x)) := List.perm_cons_erase hx
      have IH := distribute key R P l (K.erase (key x)) (fun k y => F (k + 1) y) (hK.erase _) hl'
        (fun k y hy hyK => h1 (k + 1) y hy (List.mem_of_mem_erase hyK))
        (fun k y hy hyK => h2 (k + 1) y hy (fun hyK' => hyK ((hK.mem_erase_iff).2 ⟨hne k y hy, hyK'⟩)))
      iintro ⟨#HP, HK⟩
      ihave HK := (BigSepL.bigSepL_perm hp).1 $$ HK
      icases BigSepL.bigSepL_cons.1 $$ HK with ⟨Hx, HK⟩
      iapply BigSepL.bigSepL_cons.2
      isplitl [Hx]
      · iapply (h1 0 x rfl hx)
        iexact Hx
      · iapply IH
        isplitr
        · iexact HP
        · iexact HK
    · have IH := distribute key R P l K (fun k y => F (k + 1) y) hK hl'
        (fun k y hy hyK => h1 (k + 1) y hy hyK) (fun k y hy hyK => h2 (k + 1) y hy hyK)
      iintro ⟨#HP, HK⟩
      iapply BigSepL.bigSepL_cons.2
      isplitr
      · iapply (h2 0 x rfl hx)
        iexact HP
      · iapply IH
        isplitr
        · iexact HP
        · iexact HK

theorem slots_members (d : Deployment) (c : ClusterNames) :
    ([∗list] id ∈ d.ids, lease.lessorSlot (GF := GF) (c.ls id)) ⊢
      [∗list] m ∈ d.members, lease.lessorSlot (GF := GF) (c.ls (memberId (go!"http://" ++ m.peer) d.token)) := by
  rw [show d.ids = d.members.map (fun m => memberId (go!"http://" ++ m.peer) d.token) from rfl,
    BigSepL.bigSepL_map] <;> exact .rfl

/-- **Every member's `leaseMember`** (persistent; §27.2 step 3): its client address valid, serving the member at
the view, whose lessor name has its slot. -/
theorem leaseMembers_of (d : Deployment) (Hd : d.WellFormed) (c : ClusterNames) :
    clientSvcFacts (G := Gg) (cmsD d) c.view ∗ ([∗list] id ∈ d.ids, lease.lessorSlot (GF := GF) (c.ls id)) ⊢
      [∗list] a ∈ d.members.map Member.client, leaseMember (Gg := Gg) c.view a := by
  rw [BigSepL.bigSepL_map]
  iintro ⟨#Hcs, #Hsl⟩
  ihave #Hcs := clientSvc_members (G := Gg) d c.view $$ Hcs
  ihave #Hsl := slots_members (GF := GF) d c $$ Hsl
  ihave #H : [∗list] m ∈ d.members,
      (etcdAddrAt (GF := GF) m.client c.view (memberId (go!"http://" ++ m.peer) d.token) ∗
        lease.lessorSlot (GF := GF) (c.ls (memberId (go!"http://" ++ m.peer) d.token))) $$ []
  · iapply BigSepL.bigSepL_sep_eqv.2
    isplitl []
    · iexact Hcs
    · iexact Hsl
  iapply (BigSepL.bigSepL_impl (Ψ := fun (_ : Nat) (m : Member) => leaseMember (Gg := Gg) c.view m.client)) $$ H
  imodintro
  iintro %k %m %hk ⟨#Ha, #Hs⟩
  iunfold leaseMember
  isplitr
  · ipureintro
    apply Hd.addrs.2
    simp only [Deployment.addrs]
    exact List.mem_append_left _ (List.mem_flatMap.2 ⟨m, List.mem_of_getElem? hk, by simp⟩)
  iexists memberId (go!"http://" ++ m.peer) d.token
  rw [show c.view.ls = c.ls from rfl]
  isplitl []
  · iexact Ha
  · iexact Hs

/-- **A lease workload's share** (kinds 7-9), from every member's `leaseMember` at a view with the lease mode its
kind needs and injective lessor names. -/
theorem lease_arm [ρ : RemoteGS] {w : Workload} {eps ns : List GoString} (Γ : DistView)
    (hk : w.kind = W64 7 ∨ w.kind = W64 8 ∨ w.kind = W64 9)
    (h8 : w.kind = W64 8 → Γ.kv.lm = .mono) (h9 : w.kind = W64 9 → Γ.kv.lm = .revocable)
    (hinj : ∀ a b : w64, Γ.ls a = Γ.ls b → a = b) :
    ([∗list] a ∈ eps, leaseMember (Gg := Gg) Γ a) ⊢ wlShare (Gg := Gg) w eps ns := by
  rcases hk with h | h | h
  · rw [wlShare_leaseRead h]
    unfold leaseShare
    iintro #H
    iexists Γ
    isplitr
    · ipureintro; trivial
    · iexact H
  · rw [wlShare_leaseCatchup h]
    unfold leaseShare
    iintro #H
    iexists Γ
    isplitr
    · ipureintro; exact ⟨h8 h, hinj⟩
    · iexact H
  · rw [wlShare_leaseExpiry h]
    unfold leaseShare
    iintro #H
    iexists Γ
    isplitr
    · ipureintro; exact ⟨h9 h, hinj⟩
    · iexact H

theorem budUnits_one [ρ : RemoteGS] (a : GoString) : budUnits (Gg := Gg) a 1 ⊢ budUnit (Gg := Gg) a := by
  show iprop(budUnit (Gg := Gg) a ∗ budUnits (Gg := Gg) a 0) ⊢ _
  iintro ⟨H, -⟩
  iexact H

/-- **The watch (or cache) workload's start** (§24.3, §29.4): the KV half whole at a state with no change after
the boot's, the writers' slot map with one call per writer machine, and every writer machine's address set to the
writer service at the view: the orchestrator's `watchShare writersShare eps ns`, every writer address's `svcAddr`. -/
theorem watch_start (Γ : DistView) (σ₀ : KVState) (hσ : σ₀.changes = [[]]) (eps ns : List GoString)
    (hnd : ns.Nodup) :
    ⊢ regCtx (Gg := Gg) -∗ ([∗list] a ∈ ns, addrUnset (Gg := Gg) a) -∗ membersAt (Gg := Gg) eps Γ -∗
      etcdKV (GF := GF) Γ.kv σ₀ ={⊤}=∗
      ∃ ρ : RemoteGS, watchShare (Gg := Gg) (writersShare (Gg := Gg) (ρ := ρ)) eps ns ∗
        [∗list] a ∈ ns, svcAddr (Gg := Gg) (ρ := ρ) (writerSvcG (Gg := Gg) Γ) a := by
  iintro #Hreg Hs #Hm Hkv
  imod mapCtx_alloc (Gg := Gg) (I := WN × List etcdstart.wkv) ⊤ ns 1 hnd with ⟨%ρ, -, #Hmc, Hu⟩
  imod addrs_set_proto (Gg := Gg) ⊤ (fun a => reqP (Gg := Gg) (ρ := ρ) (writerSvcG (Gg := Gg) Γ) a)
      (fun _ => repP (Gg := Gg) (ρ := ρ) (writerSvcG (Gg := Gg) Γ)) ns $$ Hreg Hs with #Ha
  imodintro
  iexists ρ
  isplitl [Hkv Hu]
  · iunfold watchShare
    iexists Γ, σ₀
    isplitr
    · ipureintro; exact hσ
    isplitr
    · iexact Hm
    iframe Hkv
    iunfold writersShare
    isplitr
    · iexact Hmc
    iapply BigSepL.bigSepL_sep_eqv.2
    isplitr
    · unfold svcAddr; iexact Ha
    · iapply (BigSepL.bigSepL_mono (Φ := fun _ a => budUnits (Gg := Gg) (ρ := ρ) a 1)
        (fun _ => budUnits_one (Gg := Gg) (ρ := ρ) _)) $$ Hu
  · unfold svcAddr; iexact Ha

/-- **The shared KV's resources at a kind** (class P): putget's `kvPfxShare pg/` (kind 4), durable's
`kvPfxShare du/` (kind 10), compact's `compactShare` once the cluster compacts at retention `1` (kind 3). -/
def pRes [ρ : RemoteGS] (eps : List GoString) (Γ : DistView) (k : w64) : IProp GF :=
  if k = W64 4 then kvPfxShare (Gg := Gg) putgetPfx eps
  else if k = W64 10 then kvPfxShare (Gg := Gg) durablePfx eps
  else if k = W64 3 then iprop(⌜Γ.kv.cmp = true ∧ Γ.kv.cret = 1⌝ -∗ compactShare (Gg := Gg) eps)
  else iprop(True)

theorem pRes_4 [ρ : RemoteGS] (eps : List GoString) (Γ : DistView) :
    pRes (Gg := Gg) eps Γ (W64 4) = kvPfxShare (Gg := Gg) putgetPfx eps := by
  unfold pRes; rw [if_pos rfl]

theorem pRes_10 [ρ : RemoteGS] (eps : List GoString) (Γ : DistView) :
    pRes (Gg := Gg) eps Γ (W64 10) = kvPfxShare (Gg := Gg) durablePfx eps := by
  unfold pRes; rw [if_neg (by decide), if_pos rfl]

theorem pRes_3 [ρ : RemoteGS] (eps : List GoString) (Γ : DistView) :
    pRes (Gg := Gg) eps Γ (W64 3) = iprop(⌜Γ.kv.cmp = true ∧ Γ.kv.cret = 1⌝ -∗ compactShare (Gg := Gg) eps) := by
  unfold pRes; rw [if_neg (by decide), if_neg (by decide), if_pos rfl]

/-- **The shared KV's start** (class P; §23.4, §26.4): from the KV half at a state with no key-value and no
change, `kvPfx_alloc` over `pg/`, `du/`, `cw/` (compact's discipline `cwOk`), and the members' facts and the KV
invariant for compact: the resources of the kinds 4, 10, 3 (`pRes`). -/
theorem pfx_start [ρ : RemoteGS] (Γ : DistView) (σ₀ : KVState) (h0 : σ₀.kvs = []) (hc0 : σ₀.changes = [[]])
    (hrev : 1 ≤ σ₀.rev) (γr : ServerRaftNames) (hauth : Γ.auth = false) (eps : List GoString) :
    ⊢ membersAt (Gg := Gg) eps Γ -∗ kvInv (GF := GF) γr Γ.kv -∗ etcdKV (GF := GF) Γ.kv σ₀ ={⊤}=∗
      [∗list] k ∈ [W64 4, W64 10, W64 3], pRes (Gg := Gg) eps Γ k := by
  iintro #Hm #Hi Hkv
  imod (kvPfx_alloc (GF := GF) Γ.kv σ₀ h0 (fun cs h => by rw [hc0] at h; simpa using h)
      [go!"pg/", go!"du/", go!"cw/"] pfxs_apart pfxOk ⊤) $$ Hkv with ⟨%γh, %γs, %hl, -, H⟩
  rcases γs with _ | ⟨g1, _ | ⟨g2, _ | ⟨g3, _ | ⟨g4, γs⟩⟩⟩⟩ <;> try (simp at hl; done)
  simp only [List.zip_cons_cons, List.zip_nil_right]
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨⟨#H1, G1⟩, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨⟨#H2, G2⟩, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨⟨#H3, G3⟩, -⟩
  have hok : ∀ p, p ≠ compactPfx → ∀ c, pfxOk p c := fun p hp c => by
    unfold pfxOk; rw [if_neg hp]; trivial
  imodintro
  iapply BigSepL.bigSepL_cons.2
  isplitl [G1]
  · rw [pRes_4]
    iunfold kvPfxShare
    iexists Γ, g1
    isplitr
    · ipureintro; exact hauth
    isplitr
    · iexact Hm
    isplitr
    · iapply (kvPfx_of_H (GF := GF) Γ.kv go!"pg/" g1 _ γh σ₀ (hok go!"pg/" (by decide))) $$ H1
    · iexact G1
  iapply BigSepL.bigSepL_cons.2
  isplitl [G2]
  · rw [pRes_10]
    iunfold kvPfxShare
    iexists Γ, g2
    isplitr
    · ipureintro; exact hauth
    isplitr
    · iexact Hm
    isplitr
    · iapply (kvPfx_of_H (GF := GF) Γ.kv go!"du/" g2 _ γh σ₀ (hok go!"du/" (by decide))) $$ H2
    · iexact G2
  iapply BigSepL.bigSepL_cons.2
  isplitl [G3]
  · rw [pRes_3]
    iintro %Hc
    iunfold compactShare
    iexists Γ, γr, g3, γh, σ₀
    isplitr
    · ipureintro; exact ⟨hauth, Hc.1, Hc.2, hrev⟩
    isplitr
    · iexact Hm
    isplitr
    · iexact Hi
    isplitr
    · iExactEq H3
      unfold pfxOk
      rw [if_pos rfl]
    · iexact G3
  iapply BigSepL.bigSepL_nil.2
  iempintro

/-- **The client machines' shares of a sole writer** (class S, persistent): from the members' facts `Q` and each
of the writer's client addresses' fact `X a`, every client machine's share. -/
theorem nodes_of_sole [ρ : RemoteGS] {d : Deployment} (boot : List LogEntry) {j : Nat} {s : Workload}
    {ns : List GoString} (hj : d.workloads[j]? = some s) (hns : d.nodes[j]? = some ns)
    (hoth : ∀ (j' : Nat) (ns' : List GoString), d.nodes[j']? = some ns' → j' ≠ j → ns' = [])
    (Q : IProp GF) (X : GoString → IProp GF)
    (hX : ∀ (c : Nat) (a : GoString), a ∈ ns →
      Q ∗ X a ⊢ wlNodeShare (Gg := Gg) s (W64 c) a (rotateL (d.members.map Member.client) c)) :
    □ (Q ∗ [∗list] a ∈ ns, X a) ⊢
      [∗list] n ↦ _x ∈ d.nodeList, startShares (Gg := Gg) d boot (d.members.length + d.workloads.length + n) := by
  refine BigSepL.bigSepL_intro (fun n x hx => ?_)
  obtain ⟨w, c, a⟩ := x
  obtain ⟨hw, ha⟩ := nodeList_sole hj hns hoth hx
  subst hw
  rw [startShares_node, nodeAt_eq hx]
  obtain ⟨i, hi⟩ := List.getElem?_of_mem ha
  iintro #⟨HQ, HX⟩
  iapply (hX c a ha)
  isplitl []
  · iexact HQ
  · iapply (BigSepL.bigSepL_lookup hi) $$ HX

/-- **The members' shares as the start's** (for any `ρ`). -/
theorem members_shares [ρ : RemoteGS] (d : Deployment) (boot : List LogEntry) (c : ClusterNames) :
    ([∗list] i ↦ _m ∈ d.members, memberShareD (G := Gg) c (lmOf d) d (distPs d) (distCtxs d) boot i) ⊢
      [∗list] i ↦ _m ∈ d.members, startShares (Gg := Gg) d boot i := by
  iintro H
  iapply (BigSepL.bigSepL_impl (Ψ := fun i _ => startShares (Gg := Gg) d boot i)) $$ H
  imodintro
  iintro %k %m %hk Hm
  rw [startShares_member (List.getElem?_eq_some_iff.1 hk).1]
  iexists c
  iexact Hm

/-- **The full start** (see the file header): for a well-formed deployment with auth off at the bootstrap log
`boot` (`BootFacts`) and a receipt budget of at most `2 ^ 60`, from the registry and every address of the deployment
unset, the remote library's names `ρ` and every machine's share: the members', the orchestrators' and the client
machines' (`startShares`, indexed as `machines`: `startShares_member`/`_orch`/`_node`). -/
theorem etcd_start (d : Deployment) (Hd : d.WellFormed) (ha : d.cfg.auth = false) (boot : List LogEntry)
    (Hbf : BootFacts d boot) (Hrb : receiptBound GF ≤ 2 ^ 60) (hV : Nonempty (client.WEnv GF))
    (hAs : errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty) :
    ⊢ regCtx (Gg := Gg) -∗ ([∗list] a ∈ d.addrs, addrUnset (Gg := Gg) a) ={⊤}=∗
      ∃ ρ : RemoteGS,
        ([∗list] i ↦ _m ∈ d.members, startShares (Gg := Gg) (ρ := ρ) d boot i) ∗
        ([∗list] j ↦ _w ∈ d.workloads, startShares (Gg := Gg) (ρ := ρ) d boot (d.members.length + j)) ∗
        [∗list] n ↦ _x ∈ d.nodeList,
          startShares (Gg := Gg) (ρ := ρ) d boot (d.members.length + d.workloads.length + n) := by
  have Hbc : BootCore (distPs d) (distCtxs d) boot := Hbf
  have hbl := srvBootLogOk_of_BootLog _ _ _ Hbc.boot
  have hknd := kinds_nodup Hd
  have hnd := Hd.addrs.1
  simp only [Deployment.addrs] at hnd
  have hfnd : d.nodes.flatten.Nodup := (List.nodup_append.1 hnd).2.1
  let eps := d.members.map Member.client
  let ρ0 : RemoteGS := ⟨0, fun _ => none, fun _ _ => 0⟩
  iintro #Hreg Hs
  simp only [Deployment.addrs]
  icases BigSepL.bigSepL_append.1 $$ Hs with ⟨Hm, Hn⟩
  imod (clusterStartDC (G := Gg) d Hd boot Hbf Hrb (lmOf d) (lmOf_revocable_apart Hd) (cmpOf d).1 (cmpOf d).2
      (cmpOf_bootCfg Hd) (cmpOf_auth Hd)) $$ Hreg Hm
    with ⟨%c, %Hc, #Hcf, Hetcd, #Hcs, #Hsl, Hms⟩
  obtain ⟨hlog, hlm, hcmp, hcret, hinj⟩ := Hc
  obtain ⟨hkvs, hch, hrev⟩ := bootSt_facts c.γk hlog (distPs d) _ hbl
  simp only [ha]
  ihave #Hmem : membersAt (Gg := Gg) eps c.view $$ []
  · iapply membersAt_of_members
    rw [clusterMembersOf_eq]
    iexact Hcs
  ihave #Hlm := leaseMembers_of (Gg := Gg) d Hd c $$ [Hcs Hsl]
  · isplitl []
    · iexact Hcs
    · iexact Hsl
  ihave #Hkvi := kvInv_of_clusterFacts (G := Gg) c $$ Hcf
  -- the lease workloads' arm, in every class
  have hlease : ∀ [ρ : RemoteGS] (j : Nat) (w : Workload), d.workloads[j]? = some w →
      (w.kind = W64 7 ∨ w.kind = W64 8 ∨ w.kind = W64 9) →
      ([∗list] a ∈ eps, leaseMember (Gg := Gg) c.view a) ⊢
        startShares (Gg := Gg) d boot (d.members.length + j) := by
    intro ρ j w hj hk
    obtain ⟨ns, -, he⟩ := startShares_orch' (Gg := Gg) Hd (boot := boot) hj
    rw [he]
    exact lease_arm c.view hk
      (fun h8 => by show c.γk.lm = _; rw [hlm]; exact lmOf_catchup Hd ⟨w, List.mem_of_getElem? hj, h8⟩)
      (fun h9 => by show c.γk.lm = _; rw [hlm]; exact lmOf_expiry ⟨w, List.mem_of_getElem? hj, h9⟩)
      hinj.1
  rcases class_authOff Hd ha with ⟨hw0, hn0⟩ | ⟨-, hls, hn0⟩ |
      ⟨j, s, ns, hj, hns, hsk, hoth, hnoth, hsb, hlmn⟩ | ⟨-, hpk, hn0, hlmn⟩
  · -- E: the members only
    have hnl : d.nodeList = [] := nodeList_nil (by rw [hn0]; simp)
    imodintro
    iexists ρ0
    isplitl [Hms]
    · iapply (members_shares (ρ := ρ0) d boot c) $$ Hms
    rw [hw0, hnl]
    isplitl []
    · iapply BigSepL.bigSepL_nil.2; iempintro
    · iapply BigSepL.bigSepL_nil.2; iempintro
  · -- Ls: the lease workloads
    have hnl : d.nodeList = [] := nodeList_nil hn0
    imodintro
    iexists ρ0
    isplitl [Hms]
    · iapply (members_shares (ρ := ρ0) d boot c) $$ Hms
    rw [hnl]
    isplitl []
    · iapply (distribute (·.kind) (fun _ => iprop(True))
        (iprop([∗list] a ∈ eps, leaseMember (Gg := Gg) c.view a)) d.workloads [] _ List.nodup_nil hknd
        (fun k x _ hx => absurd hx (by simp))
        (fun k x hx _ => hlease (ρ := ρ0) k x hx (hls x (List.mem_of_getElem? hx))))
      isplitl []
      · iexact Hlm
      · iapply BigSepL.bigSepL_nil.2; iempintro
    · iapply BigSepL.bigSepL_nil.2; iempintro
  · -- S: the sole writer `s` at `j`, the others `leaseRead`s
    have hflat : d.nodes.flatten = ns := cls_flatten_single d.nodes j ns hns hnoth
    have hnsnd : ns.Nodup := hflat ▸ hfnd
    rw [hflat]
    isimp only [hlmn, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte] at Hetcd
    have hsj : ∀ (k : Nat) (x : Workload), d.workloads[k]? = some x → x.kind = s.kind → k = j ∧ x = s := by
      intro k x hx hk
      by_cases hkj : k = j
      · subst hkj
        rw [hj] at hx
        exact ⟨rfl, (Option.some.inj hx).symm⟩
      · have h7 := hoth k x hx hkj
        rw [h7] at hk
        exfalso
        rcases hsk with h | h | h <;> rw [h] at hk <;> exact absurd hk (by decide)
    -- the orchestrators: the sole writer's share to `j`, the lease shares to the others
    have hS1 : ∀ [ρ : RemoteGS] (k : Nat) (x : Workload), d.workloads[k]? = some x → x.kind ∈ [s.kind] →
        wlShare (Gg := Gg) s eps ns ⊢ startShares (Gg := Gg) d boot (d.members.length + k) := by
      intro ρ k x hx hk
      obtain ⟨rfl, rfl⟩ := hsj k x hx (List.mem_singleton.1 hk)
      obtain ⟨ns', hns', he⟩ := startShares_orch' (Gg := Gg) Hd (boot := boot) hx
      rw [hns] at hns'
      cases hns'
      rw [he]
    have hS2 : ∀ [ρ : RemoteGS] (k : Nat) (x : Workload), d.workloads[k]? = some x → x.kind ∉ [s.kind] →
        ([∗list] a ∈ eps, leaseMember (Gg := Gg) c.view a) ⊢
          startShares (Gg := Gg) d boot (d.members.length + k) := by
      intro ρ k x hx hk
      have hkj : k ≠ j := by
        rintro rfl
        rw [hj] at hx
        cases hx
        exact hk (List.mem_singleton.2 rfl)
      exact hlease k x hx (Or.inl (hoth k x hx hkj))
    rcases hsk with hk0 | hk12
    · -- kv: M1's start of the store
      ihave Hsys := kvSys_boot (Gg := Gg) c.γk hlog (distPs d) _ hbl $$ Hetcd
      imod (kv_start (Gg := Gg) c.γk ns s.ops hnsnd ⟨by omega, hsb.1, hsb.2.2.1, hsb.2.2.2.2 hk0⟩) $$ Hreg Hn Hsys
        with ⟨%ρ, Ho, #Ha⟩
      imodintro
      iexists ρ
      isplitl [Hms]
      · iapply (members_shares (ρ := ρ) d boot c) $$ Hms
      isplitl [Ho]
      · iapply (distribute (·.kind) (fun _ => wlShare (Gg := Gg) (ρ := ρ) s eps ns)
          (iprop([∗list] a ∈ eps, leaseMember (Gg := Gg) c.view a)) d.workloads [s.kind] _
          (by simp) hknd (hS1 (ρ := ρ)) (hS2 (ρ := ρ)))
        isplitl []
        · iexact Hlm
        iapply BigSepL.bigSepL_singleton.2
        rw [wlShare_kv hk0]
        iexact Ho
      · have hX : ∀ (c' : Nat) (a : GoString), a ∈ ns →
            membersAt (Gg := Gg) eps c.view ∗ remoteAddr (Gg := Gg) (kvR (GF := GF) c.γk) a ⊢
              wlNodeShare (Gg := Gg) (ρ := ρ) s (W64 c') a (rotateL eps c') := by
          intro c' a _
          rw [wlNodeShare_kv hk0]
          iintro ⟨#Hm', #Ha'⟩
          iunfold kvNodePre
          iexists c.view
          isplitr
          · ipureintro; exact ⟨rfl, rotateL_plain Hd c', hAs, hV⟩
          isplitl []
          · iapply (membersAt_sub c.view (fun a h => mem_rotateL h)) $$ Hm'
          · rw [show c.view.kv = c.γk from rfl]
            iexact Ha'
        iapply (nodes_of_sole (ρ := ρ) boot hj hns hnoth (membersAt (Gg := Gg) eps c.view)
          (fun a => remoteAddr (Gg := Gg) (kvR (GF := GF) c.γk) a) hX)
        imodintro
        isplitl []
        · iexact Hmem
        · iexact Ha
    · -- watch or cache: the KV half whole, the writers' service
      have hws := watch_start (Gg := Gg) c.view _ hch eps ns hnsnd
      rw [show c.view.kv = c.γk from rfl] at hws
      imod hws $$ Hreg Hn Hmem Hetcd with ⟨%ρ, Hw, #Ha⟩
      imodintro
      iexists ρ
      isplitl [Hms]
      · iapply (members_shares (ρ := ρ) d boot c) $$ Hms
      isplitl [Hw]
      · iapply (distribute (·.kind) (fun _ => wlShare (Gg := Gg) (ρ := ρ) s eps ns)
          (iprop([∗list] a ∈ eps, leaseMember (Gg := Gg) c.view a)) d.workloads [s.kind] _
          (by simp) hknd (hS1 (ρ := ρ)) (hS2 (ρ := ρ)))
        isplitl []
        · iexact Hlm
        iapply BigSepL.bigSepL_singleton.2
        rcases hk12 with h | h
        · rw [wlShare_watch h]
          iexact Hw
        · rw [wlShare_cache h]
          iexact Hw
      · have hX : ∀ (c' : Nat) (a : GoString), a ∈ ns →
            membersAt (Gg := Gg) eps c.view ∗ svcAddr (Gg := Gg) (ρ := ρ) (writerSvcG (Gg := Gg) c.view) a ⊢
              wlNodeShare (Gg := Gg) (ρ := ρ) s (W64 c') a (rotateL eps c') := by
          intro c' a _
          rw [wlNodeShare_writer hk12]
          iintro ⟨#Hm', #Ha'⟩
          iunfold writerNodePre
          iexists c.view
          isplitr
          · ipureintro; rfl
          isplitl []
          · iapply (membersAt_sub c.view (fun a h => mem_rotateL h)) $$ Hm'
          · iexact Ha'
        iapply (nodes_of_sole (ρ := ρ) boot hj hns hnoth (membersAt (Gg := Gg) eps c.view)
          (fun a => svcAddr (Gg := Gg) (ρ := ρ) (writerSvcG (Gg := Gg) c.view) a) hX)
        imodintro
        isplitl []
        · iexact Hmem
        · iexact Ha
  · -- P: putget, durable and compact share the KV
    isimp only [hlmn, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte] at Hetcd
    have hps := pfx_start (Gg := Gg) (ρ := ρ0) c.view _ hkvs hch (by omega) ⟨c.γ, [], W64 0⟩ rfl eps
    rw [show c.view.kv = c.γk from rfl] at hps
    imod hps $$ Hmem Hkvi Hetcd
      with HP
    have hP1 : ∀ (k : Nat) (x : Workload), d.workloads[k]? = some x → x.kind ∈ [W64 4, W64 10, W64 3] →
        pRes (Gg := Gg) (ρ := ρ0) eps c.view x.kind ⊢
          startShares (Gg := Gg) (ρ := ρ0) d boot (d.members.length + k) := by
      intro k x hx hk
      obtain ⟨ns', -, he⟩ := startShares_orch' (Gg := Gg) (ρ := ρ0) Hd (boot := boot) hx
      rw [he]
      simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at hk
      rcases hk with h | h | h
      · rw [h, pRes_4, wlShare_putget h]
      · rw [h, pRes_10, wlShare_durable h]
      · rw [h, pRes_3, wlShare_compact h]
        iintro H
        iapply H
        ipureintro
        show c.γk.cmp = true ∧ c.γk.cret = 1
        rw [hcmp, hcret, cmpOf_compact ⟨x, List.mem_of_getElem? hx, h⟩]
        exact ⟨rfl, rfl⟩
    have hP2 : ∀ (k : Nat) (x : Workload), d.workloads[k]? = some x → x.kind ∉ [W64 4, W64 10, W64 3] →
        ([∗list] a ∈ eps, leaseMember (Gg := Gg) c.view a) ⊢
          startShares (Gg := Gg) (ρ := ρ0) d boot (d.members.length + k) := by
      intro k x hx hk
      rcases hpk x (List.mem_of_getElem? hx) with h | h | h | h
      · exact absurd (by rw [h]; decide) hk
      · exact absurd (by rw [h]; decide) hk
      · exact hlease (ρ := ρ0) k x hx (Or.inl h)
      · exact absurd (by rw [h]; decide) hk
    imodintro
    iexists ρ0
    isplitl [Hms]
    · iapply (members_shares (ρ := ρ0) d boot c) $$ Hms
    rw [nodeList_nil hn0]
    isplitl [HP]
    · iapply (distribute (·.kind) (pRes (Gg := Gg) (ρ := ρ0) eps c.view)
        (iprop([∗list] a ∈ eps, leaseMember (Gg := Gg) c.view a)) d.workloads [W64 4, W64 10, W64 3] _
        (by decide) hknd hP1 hP2)
      isplitl []
      · iexact Hlm
      · iexact HP
    · iapply BigSepL.bigSepL_nil.2; iempintro

end start

end etcd_dist
end EtcdGrove
end Perennial

end
