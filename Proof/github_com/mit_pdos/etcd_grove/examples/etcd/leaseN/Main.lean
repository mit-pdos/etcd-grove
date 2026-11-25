/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/leaseN/Main.lean` (`notes/leaseN-plan.md`,
2026-11-16). Lean-first (no Rocq counterpart).

The steps (txnlinfaultsN's `startCluster`'s start, at the lease mode `none` and the examples'
no-snapshot settings): the logger; the pure facts of the members and their ids (putgetN's); the
ghost state of the cluster and its members (`etcdstart.allocN`, every member's start bundle with
its client address), each member's client address's listen right taken out of its fresh bundle, the
members' lease mode out of their boot bundles; each member paired with its ghost names and its
premises (`memberPres_of`); the members (`etcdstart.Members`) and `etcdstart.StartMembers` (an error
returns `Main`); then `run`. The transport's directory bound (`rafthttp.bootCfg` for up to `1000`
members) is a callee hypothesis, `hbcfg`, discharged at linking.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.leaseN.Main
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.leaseN.run
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.leaseN.Dir
public import Spec.go_uber_org.zap.NewNop
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Members
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.StartMembers
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.AllocN
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_leaseN

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

/-- **Every member's client address's listen right, out of its fresh bundle** (each member's
`memberFreshRes_client`). -/
theorem freshRes_split (ms : List GMember) (γn : NetNames GF) :
    ([∗list] m ∈ startOf ms, memberFreshRes (GF := GF) m.1 ⟨some m.2.1, m.2.2⟩ γn) ⊢
      ([∗list] m ∈ ms, netAddrFree (GF := GF) m.Client') ∗
        [∗list] m ∈ ms, memberFreshRes m.Name' ⟨some m.Peer', none⟩ γn := by
  unfold startOf
  rw [BigSepL.bigSepL_map]
  refine (BigSepL.bigSepL_mono fun {_ m} _ =>
    memberFreshRes_client (GF := GF) m.Name' ⟨some m.Peer', some m.Client'⟩ γn m.Client' rfl).trans ?_
  exact BigSepL.bigSepL_sep_eqv.1

/-- **Each member with its ghost names and its premises** (putgetN's `memberPres_of`). -/
theorem memberPres_of (N : Nat) (tok : GoString) (ms0 : List GMember) (ps : List w64)
    (bootLog : List EntryM) (ctxs : List (List w8)) (dir : w64 → List GoString)
    (Φs : w64 → w64 → List w8 → GName → IProp GF) (γn : NetNames GF) (lm : lease.Mode)
    (ms : List GMember) (gs : List (MemberG GF)) (ids : List w64)
    (hids : gs.map (·.id) = ids) (hlen : ms.length = gs.length) :
    ⊢ ([∗list] m; id ∈ ms; ids,
        etcdstart.bootPremise N ps bootLog ctxs dir tok m.Name' (urlsN ms0 m) id) -∗
      (□ ∀ lid : w64, netHttpOk γn lid) -∗
      ([∗list] g ∈ gs, memberBoot g.γ ctxs g.ρ g.E Φs g.id (m := lm)) -∗
      ([∗list] m ∈ ms, memberFreshRes m.Name' ⟨some m.Peer', none⟩ γn) -∗
      [∗list] x ∈ ms.zip gs, memberPre N tok ms0 ps bootLog ctxs dir Φs γn lm x := by
  induction ms generalizing gs ids with
  | nil =>
    iintro _ _ _ _
    simp only [List.zip_nil_left]
    iempintro
  | cons m ms ih =>
    cases gs with
    | nil => simp at hlen
    | cons g gs =>
      subst hids
      simp only [List.map_cons]
      iintro Hbp #Hnet Hb Hf
      ihave Hbp := BigSepL2.bigSepL2_cons.1 $$ Hbp
      ihave Hb := BigSepL.bigSepL_cons.1 $$ Hb
      ihave Hf := BigSepL.bigSepL_cons.1 $$ Hf
      icases Hbp with ⟨Hbp1, Hbp⟩
      icases Hb with ⟨Hb1, Hb⟩
      icases Hf with ⟨Hf1, Hf⟩
      rw [List.zip_cons_cons]
      iapply BigSepL.bigSepL_cons.2
      isplitl [Hbp1 Hb1 Hf1]
      · iunfold memberPre
        iframe
        iapply Hnet
      iapply (ih gs (gs.map (·.id)) rfl (by simpa using hlen)) $$ Hbp Hnet Hb Hf

/-- **A member's KV names are at its boot bundle's lease mode** (`memberBoot`'s `lease.runCfg`). -/
theorem memberBoot_lm (ctxs : List (List w8)) (Φs : w64 → w64 → List w8 → GName → IProp GF)
    (lm : lease.Mode) (g : MemberG GF) :
    memberBoot g.γ ctxs g.ρ g.E Φs g.id (m := lm) ⊢
      ⌜g.ρ.rd.kv.lm = lm⌝ ∗ memberBoot g.γ ctxs g.ρ g.E Φs g.id (m := lm) := by
  unfold memberBoot
  iintro ⟨%Hp, H⟩
  isplitr
  · ipureintro; exact lease.runCfg_lm Hp.2.2.2.2.2.2.2.2.2
  isplitr
  · ipureintro; exact Hp
  iexact H

/-- **The members' KV names are at their boot bundles' lease mode** (`memberBoot_lm` for a list). -/
theorem memberBoots_lm (ctxs : List (List w8)) (Φs : w64 → w64 → List w8 → GName → IProp GF)
    (lm : lease.Mode) (gs : List (MemberG GF)) :
    ([∗list] g ∈ gs, memberBoot g.γ ctxs g.ρ g.E Φs g.id (m := lm)) ⊢
      ⌜∀ g ∈ gs, g.ρ.rd.kv.lm = lm⌝ ∗ [∗list] g ∈ gs, memberBoot g.γ ctxs g.ρ g.E Φs g.id (m := lm) := by
  induction gs with
  | nil =>
    iintro H
    iframe
    ipureintro; intro g hg; simp at hg
  | cons g gs ih =>
    iintro H
    ihave H := BigSepL.bigSepL_cons.1 $$ H
    icases H with ⟨H1, H⟩
    ihave ⟨%Hr, H⟩ := ih $$ H
    ihave ⟨%H1p, H1⟩ := memberBoot_lm ctxs Φs lm g $$ H1
    isplitr
    · ipureintro
      intro g' hg'
      rcases List.mem_cons.1 hg' with rfl | hg'
      · exact H1p
      · exact Hr _ hg'
    iapply BigSepL.bigSepL_cons.2
    iframe

end lemmas

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.leaseN.Assumptions]

set_option maxHeartbeats 4000000 in
/-- See the file header. -/
theorem Main.wp_proof
    (wp_NewNop : zap.NewNop.spec (GF := GF) (hG := hG))
    (wp_Members : etcdstart.Members.spec (GF := GF) (hG := hG))
    (wp_StartMembers : etcdstart.StartMembers.spec (GF := GF) (hG := hG))
    (wp_run : run.spec (GF := GF) (hG := hG))
    (hne : mvcc.api.names_nonempty.law)
    (hbcfg : ∀ (dir : w64 → List GoString) (ps : List w64), (∀ f, dir f ≠ [] ↔ f ∈ ps) →
      ps.length ≤ 1000 → rafthttp.bootCfg dir ps)
    -- (premises to axioms, 2026-11-24: until then the premise `bootMarshal`) `proto.Marshal`'s spec at a boot conf change
    (wp_MarshalBoot : proto.MarshalBootConfChange.spec (GF := GF) (hG := hG)) :
    Main.spec (GF := GF) (hG := hG) := by
  intro CS k N ids ps ctxs boot hk1 hk Hlen Hbf Htb HLv Hrb48 HrbN HwbN Haf Hbuq Hrf Hdbo
    Hlp Hms hAs
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
  ihave #Pzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Psrv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver $$ []
  · iPkgInit
  ihave #Pv3 : isPkgInit (PROP := IProp GF)
      pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc $$ []
  · iPkgInit
  -- the ghost state of the cluster and its members (`allocN`)
  imod (allocN hne ids ps Hbf.perm id0 hid0 ctxs boot Hbf.toBootCore (etcd_putgetN.dirN (members k) ids)
      (startOf (members k)) Hdok.1
      (fun i h hm => by rw [startOf_peers]; exact etcd_putgetN.dirN_host _ ids i h hm)
      (by omega) (by omega) .none lease.runCfg_none (fun h => nomatch h))
      $$ Hmarsh Hss
    with ⟨%γ, %γk, %Φs, %γn, %gs, %Hal, #Hnet, Hbs, Hfrs, Hetcd⟩
  isimp only [ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte] at Hetcd
  obtain ⟨hvs, hrule, hboot, hγn1, hγn2, hgids, hgok, hc0, hch, hlog, -, -⟩ := Hal
  have hglen : (members k).length = gs.length := by
    rw [Hmlen, ← hgids, List.length_map]
  -- every member's client address's listen right, out of its fresh bundle (to `Serve`)
  icases freshRes_split (members k) γn $$ Hfrs with ⟨Hcfree, Hfrs⟩
  -- the members' lease mode (`none`), out of their boot bundles
  ihave ⟨%Hlmg, Hbs⟩ := memberBoots_lm ctxs Φs .none gs $$ Hbs
  -- each member with its ghost names and its premises
  ihave Hbps' : [∗list] m; id ∈ members k; ids, etcdstart.bootPremise N ps (LogEntry.toEntries boot 0)
      ctxs (etcd_putgetN.dirN (members k) ids) token m.Name' (urlsN (members k) m) id $$ []
  · iexact Hbps
  ihave Hpres := memberPres_of N token (members k) ps (LogEntry.toEntries boot 0) ctxs
    (etcd_putgetN.dirN (members k) ids) Φs γn .none (members k) gs ids hgids hglen $$ Hbps' Hnet Hbs Hfrs
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
    obtain ⟨⟨r, hr⟩, -⟩ := hgok x.2 (List.of_mem_zip hx).2
    rw [hr]
    refine ⟨hvs, hrule, hboot, hγn1, ?_⟩
    have hmz : (x.1, x.2.id) ∈ (members k).zip ids := by
      rw [← hgids, List.zip_map_right]
      exact List.mem_map_of_mem (f := Prod.map id (·.id)) hx
    rw [etcd_putgetN.dirN_of_mem _ ids Hidnd _ _ hmz]
    simp
  simp only [github_com.mit_pdos.etcd_grove.examples.etcd.leaseN.PeerBase,
    github_com.mit_pdos.etcd_grove.examples.etcd.leaseN.ClientBase,
    github_com.mit_pdos.etcd_grove.examples.etcd.leaseN.Token]
  (try wp_auto)
  wp_apply wp_NewNop as %lg #Hlgz
  (try wp_auto)
  wp_apply (wp_Members go!"leaseN" (W64 k) (W64 10000) (W64 11000) (by word)) as %msl Hmsl
  have hkn : uint.nat (W64 (k : Int)) = k := by word
  imod ownSlice_persist _ _ _ $$ Hmsl with #Hmsl
  ihave #Hmsl' : msl ↦*□ members k $$ []
  · iExactEq Hmsl; rw [hkn]
  iclear Hmsl
  (try wp_auto)
  wp_apply (wp_StartMembers N token (W64 10000) (W64 281474976710656) msl lg ((members k).zip gs) ps
      (LogEntry.toEntries boot 0) ctxs
      (etcd_putgetN.dirN (members k) ids) Φs γn .none false Htb Hrb48 HrbN HwbN
      (by simp [LogEntry.toEntries, hblen]; omega)
      hγn2 Hdok Hbc hnd hutf hnlen haf hxok Haf Hbuq Hdbo) $$ [Htok Hpres] as %ssl %serr Hsr
  · rw [hxs1]
    iframe; iframe #
  icases Hsr with ⟨Htok, (%Hserr | ⟨%Hserr, %ss, Hss, Hups⟩)⟩
  · cases serr with
    | nil => exact absurd rfl Hserr
    | ok ei => ?_
    (try wp_auto)
    iapply HΦ; itrivial
  subst Hserr
  (try wp_auto)
  ihave %Hupl := BigSepL2.bigSepL2_length $$ Hups
  have hzl : ((members k).zip gs).length = k := by
    rw [List.length_zip, ← hglen, Nat.min_self, membersOf_length]
  -- `run(srvs, ms, lg)`
  ihave Hcfree : [∗list] x ∈ (members k).zip gs, netAddrFree (GF := GF) x.1.Client' $$ [Hcfree]
  · have e : ([∗list] x ∈ (members k).zip gs, netAddrFree (GF := GF) x.1.Client') =
        [∗list] m ∈ members k, netAddrFree (GF := GF) m.Client' := by
      conv => rhs; rw [← hxs1]
      rw [BigSepL.bigSepL_map]
    rw [e]; iexact Hcfree
  wp_apply (wp_run ssl msl lg ss ((members k).zip gs) γn
      (fun x hx => members_client_plain k _ (List.of_mem_zip hx).1)
      (fun x hx => Hlmg x.2 (List.of_mem_zip hx).2)
      Htb HLv Hrb48 Hbuq Hrf Hlp Hms hAs) $$ [Hss Htok Hcfree Hups] as %r -
  · rw [hxs1]; iframe; iframe #
  (try wp_auto)
  iapply HΦ; itrivial

end proof

end etcd_leaseN
end EtcdGrove
end Perennial
