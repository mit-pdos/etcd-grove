/- Lean-first (no Rocq counterpart).

# `etcd/dist`: the auth class's start (#50 F7 S14, `notes/etcd-dist-f7.md`, "Handoff W-6" item 2)

`etcd_startAuth`: `etcd_start`'s conclusion (every machine's share, `startShares`) for a well-formed deployment whose
one workload is `auth` (`class_auth`: auth on, one node list of the four principals' machines). In order:
- the cluster (`clusterStartDC` at `lmOf d` and `cmpOf d`), whose auth-on arm gives the KV names' raft log tie
  (`c.γk.rlog = c.γ.log`), the client's `etcdKV` at the boot state and the auth history view at `[srvAuthSt0]`;
- at the view `Γ := c.view true` and the raft names `γR := ⟨c.γ, [], W64 0⟩`: the members' `membersAt` and
  `leaseMember`s (`leaseMembers_of` at `on = true`), the KV invariant `kvInvOn` (`kvInvOn_of_clusterFacts`), the empty
  log's lower bound, the boot state with every change empty (`bootStOn_changes`);
- the principals (as `watch_start` the writers): the remote library's slot map with one call per principal machine
  (`mapCtx_alloc`), every principal machine's address set to the principal service `principalSvcG Γ γR eps`
  (`addrs_set_proto`).
The orchestrator's share is `authShare eps ns` (`wlShare`'s kind 5), each principal machine's `authNodePre a eps`
(`wlNodeShare`'s kind 5), at the members' client addresses `eps` unrotated.

No axiom, no `sorry`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.Start

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI Iris.ProofMode Net client
open etcd_dist.view etcd_dist_client
open go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver
open github_com.mit_pdos.etcd_grove.examples.etcd.dist
open github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote
open github_com.mit_pdos.etcd_grove.examples.lib.remote

section pure
variable [GooseExts]

/-- **The boot state in the mode `on` changes nothing**: the bootstrap log's entries are conf changes
(`kvRaftOfOn_conf`), so the model is the start's log `[[], []]`, whose one later revision has no change. -/
theorem bootStOn_changes (γk : KVNames) (hlog : γk.log0 = [[], []]) (ps : List w64) (bl : List EntryM)
    (hb : srvBootLogOk ps bl) :
    ∀ cs ∈ (kvStateOf (kvModelOn γk srvAuthSt0 (bootEntries bl))).changes, cs = [] := by
  have h : kvModelOn γk srvAuthSt0 (bootEntries bl) = [[], []] := by
    obtain ⟨-, -, he⟩ := hb
    have hconf : ∀ m ∈ bootEntries bl, m.typ ≠ W32 0 := by
      intro m hm
      unfold bootEntries at hm
      obtain ⟨e, hm', rfl⟩ := List.mem_map.1 hm
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hm'
      simp only [EntryModel.ofM]
      rw [(he k _ (List.getElem?_eq_getElem hk)).2.2.1]; decide
    unfold kvModelOn
    rw [kvRaftOfOn_conf _ _ _ _ hconf]
    exact hlog
  intro cs hcs
  rw [h] at hcs
  simpa [kvStateOf] using hcs

end pure

section start
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext] [GoLocalContext] [sem : go.Semantics]
variable [go_etcd_io.etcd.client.v3.Assumptions] [go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions] [go_etcd_io.raft.v3.Assumptions]
variable [github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.Assumptions]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS .hasLC GF] [π : NetProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **The cluster's facts give its KV invariant** with auth on (`kvInvM true` is `kvInvOn`): `authShare`'s. -/
theorem kvInvOn_of_clusterFacts (c : ClusterNames) :
    clusterFactsOf (G := Gg) c true ⊢ kvInvOn (GF := GF) ⟨c.γ, [], W64 0⟩ c.γk srvAuthSt0 := by
  unfold clusterFactsOf etcdstart.clusterFacts
  rw [kvInvM_true]
  iintro ⟨-, -, -, -, -, H⟩
  iexact H

/-- **The auth class's start** (see the file header): for a well-formed deployment whose one workload is `auth`, at
the bootstrap log `boot` (`BootFacts`) and a receipt budget of at most `2 ^ 60`, from the registry and every address
of the deployment unset, the remote library's names `ρ` and every machine's share (`startShares`, as
`etcd_start`'s). -/
theorem etcd_startAuth (d : Deployment) (Hd : d.WellFormed) (h5 : d.workloads.map (·.kind) = [W64 5])
    (boot : List LogEntry) (Hbf : BootFacts d boot) (Hrb : receiptBound GF ≤ 2 ^ 60) :
    ⊢ regCtx (Gg := Gg) -∗ ([∗list] a ∈ d.addrs, addrUnset (Gg := Gg) a) ={⊤}=∗
      ∃ ρ : RemoteGS,
        ([∗list] i ↦ _m ∈ d.members, startShares (Gg := Gg) (ρ := ρ) d boot i) ∗
        ([∗list] j ↦ _w ∈ d.workloads, startShares (Gg := Gg) (ρ := ρ) d boot (d.members.length + j)) ∗
        [∗list] n ↦ _x ∈ d.nodeList,
          startShares (Gg := Gg) (ρ := ρ) d boot (d.members.length + d.workloads.length + n) := by
  have Hbc : BootCore (distPs d) (distCtxs d) boot := Hbf
  have hbl := srvBootLogOk_of_BootLog _ _ _ Hbc.boot
  obtain ⟨hon, w, ns, hw, hk, hns, hlen⟩ := class_auth Hd h5
  have hnd := Hd.addrs.1
  simp only [Deployment.addrs, hns, List.flatten_cons, List.flatten_nil, List.append_nil] at hnd
  have hnsnd : ns.Nodup := (List.nodup_append.1 hnd).2.1
  have hj : d.workloads[0]? = some w := by rw [hw]; rfl
  have hns0 : d.nodes[0]? = some ns := by rw [hns]; rfl
  have hoth : ∀ (j' : Nat) (ns' : List GoString), d.nodes[j']? = some ns' → j' ≠ 0 → ns' = [] := by
    intro j' ns' h hne
    rw [hns] at h
    cases j' with
    | zero => exact absurd rfl hne
    | succ k => simp at h
  let eps := d.members.map Member.client
  have hcs := clusterStartDC (G := Gg) d Hd boot Hbf Hrb (lmOf d) (lmOf_revocable_apart Hd) (cmpOf d).1 (cmpOf d).2
      (cmpOf_bootCfg Hd) (cmpOf_auth Hd)
  simp only [hon, ↓reduceIte] at hcs
  iintro #Hreg Hs
  simp only [Deployment.addrs]
  icases BigSepL.bigSepL_append.1 $$ Hs with ⟨Hm, Hn⟩
  rw [hns, List.flatten_cons, List.flatten_nil, List.append_nil]
  imod hcs $$ Hreg Hm with ⟨%c, %Hc, #Hcf, ⟨%hrl, Hetcd, Hview⟩, #Hcs, #Hsl, Hms⟩
  obtain ⟨hlog, -, -, -, hinj⟩ := Hc
  let Γ : DistView := c.view true
  let γR : ServerRaftNames := ⟨c.γ, [], W64 0⟩
  ihave #Hmem : membersAt (Gg := Gg) eps Γ $$ []
  · iapply membersAt_of_members
    rw [clusterMembersOf_eq]
    iexact Hcs
  ihave #Hlm := leaseMembers_of (Gg := Gg) d Hd c true $$ [Hcs Hsl]
  · isplitl []
    · iexact Hcs
    · iexact Hsl
  ihave #Hkvi := kvInvOn_of_clusterFacts (Gg := Gg) c $$ Hcf
  imod (show ⊢ |==> srvReqLogLb (GF := GF) γR [] by unfold srvReqLogLb; exact monoListLbOwn_nil _) with #HL0
  have hch := bootStOn_changes c.γk hlog (distPs d) _ hbl
  -- the principals: the slot map, one call each; every principal machine's address at the principal service
  imod mapCtx_alloc (Gg := Gg) (I := GoString) ⊤ ns 1 hnsnd with ⟨%ρ, -, #Hmc, Hu⟩
  imod addrs_set_proto (Gg := Gg) ⊤
      (fun a => reqP (Gg := Gg) (ρ := ρ) (principalSvcG (Gg := Gg) Γ γR eps) a)
      (fun _ => repP (Gg := Gg) (ρ := ρ) (principalSvcG (Gg := Gg) Γ γR eps)) ns $$ Hreg Hn with #Ha
  imodintro
  iexists ρ
  isplitl [Hms]
  · iapply (members_shares (ρ := ρ) d boot c) $$ Hms
  isplitl [Hetcd Hview Hu]
  · obtain ⟨ns', hns', he⟩ := startShares_orch' (Gg := Gg) (ρ := ρ) Hd (boot := boot) hj
    rw [hns0] at hns'
    cases hns'
    rw [hw]
    iapply BigSepL.bigSepL_singleton.2
    simp only [Nat.add_zero] at he ⊢
    rw [he, wlShare_auth hk]
    iunfold authShare
    iexists Γ, γR, kvStateOf (kvModelOn c.γk srvAuthSt0 (bootEntries (LogEntry.toEntries boot 0)))
    isplitr
    · ipureintro; exact ⟨rfl, hrl.symm, hinj.2, hch⟩
    isplitr
    · iexact Hlm
    isplitr
    · iexact Hkvi
    isplitr
    · iexact HL0
    iframe Hetcd
    iframe Hview
    iunfold principalsShare
    isplitr
    · iexact Hmc
    isplitr
    · ipureintro; rw [hlen]; rfl
    iapply BigSepL.bigSepL_sep_eqv.2
    isplitr
    · unfold svcAddr; iexact Ha
    · iapply (BigSepL.bigSepL_mono (Φ := fun _ a => budUnits (Gg := Gg) (ρ := ρ) a 1)
        (fun _ => budUnits_one (Gg := Gg) (ρ := ρ) _)) $$ Hu
  · have hX : ∀ (c' : Nat) (a : GoString), a ∈ ns →
        membersAt (Gg := Gg) eps Γ ∗ svcAddr (Gg := Gg) (ρ := ρ) (principalSvcG (Gg := Gg) Γ γR eps) a ⊢
          wlNodeShare (Gg := Gg) (ρ := ρ) w (W64 c') a eps := by
      intro c' a _
      rw [wlNodeShare_auth hk]
      iintro ⟨#Hm', #Ha'⟩
      iunfold authNodePre
      iexists Γ, γR
      isplitr
      · ipureintro; exact ⟨rfl, hinj.2⟩
      isplitl []
      · iexact Hm'
      · iexact Ha'
    iapply (nodes_of_sole (ρ := ρ) boot hj hns0 hoth (membersAt (Gg := Gg) eps Γ)
      (fun a => svcAddr (Gg := Gg) (ρ := ρ) (principalSvcG (Gg := Gg) Γ γR eps) a) hX)
    imodintro
    isplitl []
    · iexact Hmem
    · unfold svcAddr; iexact Ha

end start

end etcd_dist
end EtcdGrove
end Perennial

end
