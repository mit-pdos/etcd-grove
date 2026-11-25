/- Lean-first (no Rocq counterpart).

# `dist/kvremote`: the kv deployment's start (§11.3 step 5, P9; `notes/etcd-dist-p9.md`)

The part of M1's start (`etcd_kv_safe_nocrash`) that is the kv instance's: from the protocol library's
registry (`regCtx`, Net's `netProto_alloc`), the client machines' addresses unset and the cluster's KV at
the boot state (`(kvR γk).sysState (kvR γk).B.init`: `etcdKV γk σ₀` with `absSt σ₀` the model's start),

- `kv_start`: the slot map and each client machine's call budget (`mapCtx_alloc`, `ops · readTries`
  per address), the pending library at the model's start (`pend_alloc`: `pendCtx`, `pendLib`), every client
  machine's address set to serve the store `kvR γk`'s calls (`addrs_set_proto`, `remoteAddr`): the
  orchestrator's share `kvOrchPre ns ops` and the client machines' `remoteAddr`s;
- `membersAt_sub`: the members' address facts at the deployment's client addresses give them at any
  list of those addresses (a client machine's rotated endpoints, N7-kv's `rotateL`);
- `kv_start_deployment`: at a deployment with one workload (M1's: `KvOnly` and `Compatible`'s distinct
  kinds), the start from all of the deployment's addresses, the members' part being **`member_boot_dist`**
  (its statement `member_boot_dist.law`), a hypothesis that N5 (the member's boot, the lead's) proves: from
  the registry and the members' addresses unset, the cluster's view `Γ` (auth off), its KV at the boot
  state, each member's client address serving the member (`clientSvcFacts (clusterMembersOf d) Γ`,
  `etcdClusterStart`'s client facts) and the members' own shares `MS Γ`. `membersAt_of_members`
  turns them into `membersAt` at the members' client addresses.

No axiom, no `sorry`: `member_boot_dist` is a hypothesis of `kv_start_deployment`, discharged by N5. All of it is
at the global ghost state (`[Gg : GooseGlobalGS]`, as N5's `memberShareD`): the machines' boot shares.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.Orch
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.Node
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.DeploymentDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.ClusterStart
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.Pend

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote

open Iris Iris.BI Iris.ProofMode Net
open EtcdGrove EtcdGrove.etcd_txnlin EtcdGrove.etcd_dist
open github_com.mit_pdos.etcd_grove.examples.lib.remote

section start
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF] [GoLocalContext]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.Assumptions]
variable [π : NetProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **The members' address facts at any of their addresses** (persistent): from every client
address of the members, any list of them (a client machine's endpoints, rotated). -/
theorem membersAt_sub (Γ : DistView)
    {eps eps' : List GoString} (h : ∀ a ∈ eps', a ∈ eps) :
    membersAt (Gg := Gg) eps Γ ⊢ membersAt (Gg := Gg) eps' Γ := by
  unfold membersAt
  refine intuitionistically_of_intuitionistic.2.trans (BigSepL.bigSepL_intro fun k x hx => ?_)
  obtain ⟨j, hj⟩ := List.getElem?_of_mem (h x (List.mem_of_getElem? hx))
  exact intuitionistically_elim.trans (BigSepL.bigSepL_lookup hj)

/-- **The kv instance's start** (see the file header): from the registry, the client machines'
addresses `ns` unset and the cluster's KV at the boot state, the orchestrator's share `kvOrchPre ns ops`
(at the remote names `ρ` it allocates) and every client machine's `remoteAddr` at the store `kvR γk`. -/
theorem kv_start (γk : KVNames) (ns : List GoString) (ops : w64) (hnd : ns.Nodup)
    (hb : receiptBound GF ≤ 2 ^ 63 ∧ ns.length < 2 ^ 31 ∧ 0 ≤ sint.Z ops ∧
      (ns.length : Int) * sint.Z ops < 2 ^ 60) :
    ⊢ regCtx (Gg := Gg) -∗
      ([∗list] a ∈ ns, addrUnset (Gg := Gg) a) -∗
      (kvR (GF := GF) γk).sysState (kvR (GF := GF) γk).B.init ={⊤}=∗
      ∃ ρ : RemoteGS, kvOrchPre (ρ := ρ) ns ops ∗
        [∗list] a ∈ ns, remoteAddr (Gg := Gg) (kvR (GF := GF) γk) a := by
  iintro #Hreg Hs Hsys
  imod mapCtx_alloc (Gg := Gg) (I := VIn) ⊤ ns (sint.nat ops * readTries) hnd
    with ⟨%ρ, -, #Hm, Hu⟩
  imod pend_alloc (Gg := Gg) (kvR (GF := GF) γk) ⊤ (linkvtxnSG (GF := GF)) rfl $$ Hsys
    with ⟨%γ, #Hp, Hl⟩
  imod addrs_set_proto (Gg := Gg) ⊤
      (fun a => reqP (Gg := Gg) (kvR (GF := GF) γk).svc a)
      (fun _ => repP (Gg := Gg) (kvR (GF := GF) γk).svc) ns $$ Hreg Hs with #Ha
  imodintro
  iexists ρ
  unfold kvOrchPre
  isplitl [Hl Hu]
  · iexists γk, γ
    isplitr
    · ipureintro; exact hb
    unfold remoteAddr svcAddr
    iframe Ha Hm Hp Hl Hu
  · unfold remoteAddr svcAddr
    iexact Ha

/-- A member's id in the deployment (`Deployment.ids`'s). -/
abbrev memberIdIn (d : Deployment) (m : Member) : w64 := memberId (go!"http://" ++ m.peer) d.token

/-- **The deployment's members as the start's members** (`ClusterMember`: peer address, client address,
member id), in the members' order. -/
def clusterMembersOf (d : Deployment) : List ClusterMember :=
  d.members.map (fun m => ⟨m.peer, m.client, memberIdIn d m⟩)

/-- **The members' client address facts (`clientSvcFacts`) give `membersAt`** at their client
addresses. -/
theorem membersAt_of_members (Γ : DistView) (d : Deployment) :
    clientSvcFacts (G := Gg) (clusterMembersOf d) Γ ⊢
      membersAt (Gg := Gg) (d.members.map Member.client) Γ := by
  unfold clientSvcFacts clusterMembersOf membersAt
  rw [BigSepL.bigSepL_map, BigSepL.bigSepL_map]
  refine BigSepL.bigSepL_mono ?_
  intro k m hm
  exact exists_intro (Ψ := fun mid : w64 => etcdAddrAt (Gg := Gg) m.client Γ mid)
    (memberIdIn d m)

/-- **The members' boot, as the start needs it** (`member_boot_dist`, proved by N5, the lead's; a
hypothesis of `kv_start_deployment` until then): from the registry and the members' addresses unset, the
cluster's view `Γ` (auth off), its KV at the boot state (`kvSys Γ.kv` at the model's start: `etcdKV Γ.kv σ₀`,
`etcdClusterStart`'s client `etcdKV` in lease mode `none`), every member's client address serving it
(`etcdClusterStart`'s `clientSvcFacts`, at the view, of `clusterMembersOf d`), and the members' own shares `MS Γ`. -/
abbrev member_boot_dist.law (d : Deployment)
    (MS : DistView → IProp GF) : Prop :=
  ⊢ regCtx (Gg := Gg) -∗
    ([∗list] a ∈ d.members.flatMap (fun m => [m.peer, m.client]), addrUnset (Gg := Gg) a)
    ={⊤}=∗ ∃ Γ : DistView, ⌜Γ.auth = false⌝ ∗
      (kvR (GF := GF) Γ.kv).sysState (kvR (GF := GF) Γ.kv).B.init ∗
      clientSvcFacts (G := Gg) (clusterMembersOf d) Γ ∗
      MS Γ

/-- **The start of a deployment with one kv workload** (see the file header): from the registry and
every address of the deployment unset, over the members' boot (`member_boot_dist`): the view `Γ`, the
members' shares, the orchestrator's share at the workload's client machines and operation count, and
each client machine's part of its share (the members' address facts, its `remoteAddr` at the cluster's
store; the pure facts of `kvNodePre` and `kvNodePreL`'s level token and thread bound come from the machine's boot). -/
theorem kv_start_deployment (d : Deployment) (w : Workload)
    (ns : List GoString) (_hw : d.workloads = [w]) (hn : d.nodes = [ns]) (hnd : d.addrs.Nodup)
    (hb : receiptBound GF ≤ 2 ^ 63 ∧ ns.length < 2 ^ 31 ∧ 0 ≤ sint.Z w.ops ∧
      (ns.length : Int) * sint.Z w.ops < 2 ^ 60)
    (MS : DistView → IProp GF) (member_boot_dist : member_boot_dist.law d MS) :
    ⊢ regCtx (Gg := Gg) -∗
      ([∗list] a ∈ d.addrs, addrUnset (Gg := Gg) a) ={⊤}=∗
      ∃ (Γ : DistView) (ρ : RemoteGS), ⌜Γ.auth = false⌝ ∗ MS Γ ∗ kvOrchPre (ρ := ρ) ns w.ops ∗
        membersAt (Gg := Gg) (d.members.map Member.client) Γ ∗
        [∗list] a ∈ ns, remoteAddr (Gg := Gg) (kvR (GF := GF) Γ.kv) a := by
  have hns : ns.Nodup := by
    have := hnd
    simp only [Deployment.addrs, hn, List.flatten_cons, List.flatten_nil, List.append_nil] at this
    exact (List.nodup_append.1 this).2.1
  iintro #Hreg Hs
  simp only [Deployment.addrs, hn, List.flatten_cons, List.flatten_nil, List.append_nil]
  icases BigSepL.bigSepL_append.1 $$ Hs with ⟨Hm, Hc⟩
  imod member_boot_dist $$ Hreg Hm with ⟨%Γ, %Hauth, Hsys, #Hmem, HMS⟩
  ihave #Hmem := membersAt_of_members Γ d $$ Hmem
  imod kv_start (γk := Γ.kv) ns w.ops hns hb $$ Hreg Hc Hsys with ⟨%ρ, Ho, #Ha⟩
  imodintro
  iexists Γ, ρ
  isplitr
  · ipureintro; exact Hauth
  iframe HMS Ho Hmem Ha

end start

end github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote
end Perennial
