/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/authN/Main.lean` (authN,
`notes/authN-plan.md`, 2026-11-15). Lean-first (no Rocq counterpart).

The steps: the pure facts of the members and their ids (putgetN's `Main`'s); the ghost state of the
cluster and its members with auth on (`etcdstart.allocNOn`), every member's client address's listen
right taken out of its fresh bundle; the history invariant over member `0`'s KV names, at the boot
state (auth3's `Main`'s); each member paired with its ghost names and its premises
(`memberPresOn_of`, putgetN's `memberPres_of` with auth on); the logger, the members
(`etcdstart.Members`) and `etcdstart.StartMembersAuth` at the no-snapshot settings (an error returns
`Failed`); then `run`. The transport's directory bound (`rafthttp.bootCfg` for up to `1000` members)
is a callee hypothesis, `hbcfg`, discharged at linking (as putgetN's).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.authN.Main
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.authN.run
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.authN.Dir
public import Spec.go_uber_org.zap.NewNop
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Members
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.StartMembersAuth
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.AllocNOn
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_authN

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver etcdstart

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

theorem startOf_peers (ms : List GMember) : (startOf ms).map (·.2.1) = ms.map (·.Peer') := by
  simp [startOf, Function.comp_def]

/-- **Every member's client address's listen right, out of its fresh bundle** (txnlinfaultsN's). -/
theorem freshRes_split (ms : List GMember) (γn : NetNames GF) :
    ([∗list] m ∈ startOf ms, memberFreshRes (GF := GF) m.1 ⟨some m.2.1, m.2.2⟩ γn) ⊢
      ([∗list] m ∈ ms, netAddrFree (GF := GF) m.Client') ∗
        [∗list] m ∈ ms, memberFreshRes m.Name' ⟨some m.Peer', none⟩ γn := by
  unfold startOf
  rw [BigSepL.bigSepL_map]
  refine (BigSepL.bigSepL_mono fun {_ m} _ =>
    memberFreshRes_client (GF := GF) m.Name' ⟨some m.Peer', some m.Client'⟩ γn m.Client' rfl).trans ?_
  exact BigSepL.bigSepL_sep_eqv.1

end lemmas

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.authN.Assumptions]

set_option maxHeartbeats 2000000 in
theorem Main.wp_proof
    (wp_NewNop : zap.NewNop.spec (GF := GF) (hG := hG))
    (wp_Members : etcdstart.Members.spec (GF := GF) (hG := hG))
    (wp_StartMembersAuth : etcdstart.StartMembersAuth.spec (GF := GF) (hG := hG))
    (wp_run : run.spec (GF := GF) (hG := hG))
    (hne : mvcc.api.names_nonempty.law)
    (hbcfg : ∀ (dir : w64 → List GoString) (ps : List w64), (∀ f, dir f ≠ [] ↔ f ∈ ps) →
      ps.length ≤ 1000 → rafthttp.bootCfg dir ps)
    -- (premises to axioms, 2026-11-24: until then the premise `bootMarshal`) `proto.Marshal`'s spec at a boot conf change
    (wp_MarshalBoot : proto.MarshalBootConfChange.spec (GF := GF) (hG := hG)) :
    Main.spec (GF := GF) (hG := hG) := by
  intro CS ES FS RS CRE CEC k N ids ps ctxs boot hk1 hk Hlen Hbf Htb HLv Hrb48 HrbN HwbN Haf Hbuq
    Hrf Hdbo Hms hAs
  wp_start as ⟨Hss, Htok, #Hprem⟩
  iunfold premises at Hprem
  icases Hprem with #Hbps
  -- (premises to axioms, 2026-11-24: until then the premise `bootMarshal`) `proto.Marshal`'s bytes at the
  -- bootstrap log's conf changes, from its trust-boundary spec and the log's bytes (`Hbf.wire`)
  ihave #Hpp : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto $$ []
  · iPkgInit
  ihave #Hmarsh := bootMarshal_of_spec wp_MarshalBoot _ _ _ Hbf.wire $$ Hpp
  -- the pure facts of the members and their ids (putgetN's)
  obtain ⟨Hpnd, -, -⟩ := idPfxsOf_ok ps Hbf.lowNodup Hbf.lowNz
  have Hpsnd : ps.Nodup := by
    unfold idPfxsOf at Hpnd
    exact List.Pairwise.of_map _ (fun a b h e => h (by rw [e])) Hpnd
  have Hidnd : ids.Nodup := Hbf.perm.nodup_iff.1 Hpsnd
  have Hid0 : W64 0 ∉ ids := fun h => Hbf.lowNz _ (Hbf.perm.symm.subset h) (by decide)
  have Hmlen : (members k).length = ids.length := by rw [membersOf_length, Hlen]
  have Hdok : netDirOk (etcd_putgetN.dirN (members k) ids) :=
    etcd_putgetN.dirN_ok _ ids Hidnd Hid0 (members_peers_nodup k hk) (members_peer_plain k)
  have Hbc : rafthttp.bootCfg (etcd_putgetN.dirN (members k) ids) ps :=
    hbcfg _ ps (fun f => by rw [etcd_putgetN.dirN_ne_nil _ ids Hmlen Hidnd, Hbf.perm.mem_iff])
      (by rw [Hbf.perm.length_eq, Hlen]; exact hk)
  have hblen : boot.length = k := by rw [Hbf.boot.1, Hbf.perm.length_eq, Hlen]
  obtain ⟨id0, hid0⟩ : ∃ id0, id0 ∈ ids := by
    cases ids with
    | nil => simp at Hlen; omega
    | cons a _ => exact ⟨a, by simp⟩
  ihave #Hcci : context.isClosedchanInit (GF := GF) $$ []
  · iapply context.isClosedchanInit_of_init
    iPkgInit
  ihave #Pes : isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart $$ []
  · iPkgInit
  ihave #Psrv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver $$ []
  · iPkgInit
  -- the ghost state of the cluster and its members with auth on (`allocNOn`)
  imod (allocNOn hne ids ps Hbf.perm id0 hid0 ctxs boot Hbf.toBootCore
      (etcd_putgetN.dirN (members k) ids) (startOf (members k)) Hdok.1
      (fun i h hm => by rw [startOf_peers]; exact etcd_putgetN.dirN_host _ ids i h hm)
      (by omega) (by omega))
      $$ Hmarsh Hss
    with ⟨%γ, %γk, %Φs, %γn, %gs, %Hal, #Hnet, Hbs, Hfrs, Hetcd, Hview⟩
  obtain ⟨hvs, hrule, hboot, hγn1, hγn2, hgids, hgok, hc0, hlog⟩ := Hal
  have hglen : (members k).length = gs.length := by
    rw [Hmlen, ← hgids, List.length_map]
  -- every member's client address's listen right, out of its fresh bundle (to `run`'s `Serve`s)
  icases freshRes_split (members k) γn $$ Hfrs with ⟨Hcfree, Hfrs⟩
  -- member `0`, with its names, and the history invariant over its KV names at the boot state
  obtain ⟨x0, hx0⟩ : ∃ x0, ((members k).zip gs)[0]? = some x0 :=
    ⟨_, List.getElem?_eq_getElem (by rw [List.length_zip, ← hglen, Nat.min_self, membersOf_length]; omega)⟩
  have hx0m : x0 ∈ (members k).zip gs := List.mem_of_getElem? hx0
  have hg0 : memberGOkOn γ γk x0.2 := hgok x0.2 (List.of_mem_zip hx0m).2
  have hσ₀ : etcd_auth.stateHistOk (kvStateOf (kvModelOn γk srvAuthSt0
      (bootEntries (LogEntry.toEntries boot 0)))) :=
    etcd_auth.stateHistOk_boot γk srvAuthSt0 ps _ (srvBootLogOk_of_BootLog _ _ _ Hbf.boot) hlog
  ihave Hetcd := etcdKV_member γ γk x0.2 hg0 _ $$ Hetcd
  imod (etcd_auth.akHist_alloc x0.2.ρ.rd.kv _ hσ₀) $$ Hetcd with #Hhist
  ihave Hview := authHistView_member γ γk x0.2 hg0 _ $$ Hview
  have hc0₀ : x0.2.ρ.rd.kv.c0 = W64 0 := by
    obtain ⟨-, -, -, -, h, -⟩ := hg0; rw [h, hc0]
  have hlog₀ : x0.2.ρ.rd.kv.log0 = [[], []] := by
    obtain ⟨-, -, -, -, -, -, h, -⟩ := hg0; rw [h, hlog]
  have hsc : ∀ x ∈ (members k).zip gs, sameCluster x0.2.ρ x.2.ρ :=
    fun x hx => sameCluster_of_gOkOn γ γk x0.2 x.2 hg0 (hgok x.2 (List.of_mem_zip hx).2)
  -- each member with its ghost names and its premises
  ihave Hbps' : [∗list] m; id ∈ members k; ids, bootPremiseOn N ps (LogEntry.toEntries boot 0)
      ctxs (etcd_putgetN.dirN (members k) ids) token m.Name' (urlsN (members k) m) id $$ []
  · iexact Hbps
  ihave Hpres := memberPresOn_of N token (members k) ps (LogEntry.toEntries boot 0) ctxs
    (etcd_putgetN.dirN (members k) ids) Φs γn (members k) gs ids hgids hglen $$ Hbps' Hnet Hbs Hfrs
  have hxs1 : ((members k).zip gs).map (·.1) = members k := List.map_fst_zip (by omega)
  have hutf : ∀ x ∈ (members k).zip gs, utf8Valid x.1.Name' :=
    fun x hx => members_names_utf8 k _ (List.of_mem_zip hx).1
  have hnlen : ∀ x ∈ (members k).zip gs, x.1.Name'.length ≤ 200 :=
    fun x hx => members_names_len k _ (List.of_mem_zip hx).1
  -- (fmt stage 1, 2026-11-24) the members' addresses within etcd's URL bounds
  have haf : ∀ x ∈ (members k).zip gs, etcdstart.addrFits x.1.Peer' ∧ etcdstart.addrFits x.1.Client' :=
    fun x hx => etcdstart.membersOf_addrFits _ _ _ _ x.1 (List.of_mem_zip hx).1
  have hnd : (((members k).zip gs).map (·.1.Name')).Nodup := by
    rw [show ((members k).zip gs).map (·.1.Name') = (((members k).zip gs).map (·.1)).map (·.Name')
      by rw [List.map_map]; rfl, hxs1]
    exact members_names_nodup k hk
  have hxok : ∀ x ∈ (members k).zip gs, x.2.γ.vs = ps ∧
      x.2.γ.rule = srvRule (W64 0) (LogEntry.toEntries boot 0) ∧
      x.2.γ.boot = LogEntry.toEntries boot 0 ∧ γn.N = srvNet x.2.γ ∧
      go!"http://" ++ x.1.Peer' ∈ etcd_putgetN.dirN (members k) ids x.2.id := by
    intro x hx
    obtain ⟨r, hr, -⟩ := hgok x.2 (List.of_mem_zip hx).2
    rw [hr]
    refine ⟨hvs, hrule, hboot, hγn1, ?_⟩
    have hmz : (x.1, x.2.id) ∈ (members k).zip ids := by
      rw [← hgids, List.zip_map_right]
      exact List.mem_map_of_mem (f := Prod.map id (·.id)) hx
    rw [etcd_putgetN.dirN_of_mem _ ids Hidnd _ _ hmz]
    simp
  have hzl : ((members k).zip gs).length ≤ 1000 := by
    rw [List.length_zip, ← hglen, Nat.min_self, membersOf_length]; exact hk
  have hpe : ∀ x ∈ (members k).zip gs, plainEndpoint x.1.Client' :=
    fun x hx => members_client_plain k _ (List.of_mem_zip hx).1
  ihave Hcfree : [∗list] x ∈ (members k).zip gs, netAddrFree (GF := GF) x.1.Client' $$ [Hcfree]
  · have he := BigSepL.bigSepL_map (PROP := IProp GF) (fun x : GMember × MemberG GF => x.1)
      (Φ := fun _ m => netAddrFree (GF := GF) m.Client') (l := (members k).zip gs)
    rw [hxs1] at he
    rw [← he]
    iexact Hcfree
  have hk0 : decide ((W64 (k : Int)) = W64 0) = false := by
    rw [decide_eq_false_iff_not]; intro h
    have := congrArg BitVec.toNat h; simp [W64] at this; omega
  simp only [github_com.mit_pdos.etcd_grove.examples.etcd.authN.PeerBase,
    github_com.mit_pdos.etcd_grove.examples.etcd.authN.ClientBase,
    github_com.mit_pdos.etcd_grove.examples.etcd.authN.Token]
  (try wp_auto)
  simp only [hk0]
  (try wp_auto)
  wp_apply wp_NewNop as %lg #Hlgz
  (try wp_auto)
  wp_apply (wp_Members go!"authN" (W64 k) (W64 29000) (W64 30000) (by word)) as %msl Hmsl
  have hkn : uint.nat (W64 (k : Int)) = k := by word
  imod ownSlice_persist _ _ _ $$ Hmsl with #Hmsl
  ihave #Hmsl' : msl ↦*□ members k $$ []
  · iExactEq Hmsl; rw [hkn]
  iclear Hmsl
  (try wp_auto)
  have Hcu48 : (2 : Int) ^ 48 ≤ uint.Z (W64 281474976710656) := by word
  wp_apply (wp_StartMembersAuth N token (W64 10000) (W64 281474976710656) msl lg ((members k).zip gs) ps
      (LogEntry.toEntries boot 0) ctxs
      (etcd_putgetN.dirN (members k) ids) Φs γn .none Htb Hrb48 HrbN HwbN
      (by simp [LogEntry.toEntries, hblen]; omega)
      hγn2 Hdok Hbc hnd hutf hnlen haf hxok Haf Hbuq Hdbo
      (fun _ _ _ => Hcu48)) $$ [Htok Hpres] as %ssl %serr Hsr
  · rw [hxs1]
    iframe; iframe #
  icases Hsr with ⟨Htok, (%Hserr | ⟨%Hserr, %ss, Hss, Hups⟩)⟩
  · cases serr with
    | nil => exact absurd rfl Hserr
    | ok ei => ?_
    (try wp_auto)
    iapply HΦ; ipureintro; right; left; rfl
  subst Hserr
  (try wp_auto)
  -- `run(srvs, ms, lg)`
  ihave #Hmsl : msl ↦*□ ((members k).zip gs).map (·.1) $$ []
  · rw [hxs1]; iexact Hmsl'
  wp_apply (wp_run ssl msl lg ss ((members k).zip gs) x0 γn hx0 hzl hpe Htb HLv Hrb48 Hbuq Hrf Hms hAs
      hc0₀ hlog₀ hsc) $$ [Hss Htok Hcfree Hups Hview] as %r %Hr
  · iframe; iframe #
  iapply HΦ; ipureintro; exact Hr

end proof

end etcd_authN
end EtcdGrove
end Perennial
