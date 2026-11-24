/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/putgetN/Main.lean` (the clusterN Scope,
2026-11-15, its stage S4). Lean-first (no Rocq counterpart).

The steps: the logger; the members (`etcdstart.Members`), read-only from then on; the ghost state of
the cluster and its members (`etcdstart.allocN`), member `0`'s client address's listen right taken
out of its fresh bundle; each member paired with its ghost names and its premises
(`etcdstart.memberPre`); `etcdstart.StartMembers` (an error returns `Main`); then putget3's steps on
member `0`: `etcdstart.Serve` at its client address, `etcdstart.NewClient`, the `Put`, the `Get` and
the check. The transport's directory bound (`rafthttp.bootCfg` for up to `1000` members) is a
callee hypothesis, `hbcfg`, discharged at linking.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.putgetN.Main
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.putgetN.Dir
public import Spec.go_uber_org.zap.NewNop
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Members
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.StartMembers
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Serve
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.NewClient
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.AllocN
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Served
public import Perennial.Spec.context.Background
public import Proof.go_etcd_io.etcd.client.v3.ServeFromStart
public import Proof.go_etcd_io.etcd.client.v3.ClientPutGet
public import Proof.go_etcd_io.etcd.client.v3.InvServerKV
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo
public import Proof.go_etcd_io.etcd.client.v3.TimeoutCtx
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.ServedLinked

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_putgetN

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver etcdstart

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.putgetN.Assumptions]

theorem startOf_peers (ms : List GMember) : (startOf ms).map (·.2.1) = ms.map (·.Peer') := by
  cases ms with
  | nil => rfl
  | cons m r => simp [startOf, Function.comp_def]

/-- **Each member with its ghost names and its premises** (`StartMembers`' precondition): its
`bootstrap` contract, its `memberBoot`, the network's HTTP side and its fresh bundle, paired. -/
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

set_option maxHeartbeats 2000000 in
theorem Main.wp_proof
    (wp_NewNop : zap.NewNop.spec (GF := GF) (hG := hG))
    (wp_Members : etcdstart.Members.spec (GF := GF) (hG := hG))
    (wp_StartMembers : etcdstart.StartMembers.spec (GF := GF) (hG := hG))
    (wp_Serve : etcdstart.Serve.spec (GF := GF) (hG := hG))
    (wp_NewClient : etcdstart.NewClient.spec (GF := GF) (hG := hG))
    (wp_Background : context.Background.spec (GF := GF) (hG := hG))
    (hWT : context.WithTimeoutBackground.spec (GF := GF) (hG := hG))
    (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG))
    (hne : mvcc.api.names_nonempty.law)
    (hbcfg : ∀ (dir : w64 → List GoString) (ps : List w64), (∀ f, dir f ≠ [] ↔ f ∈ ps) →
      ps.length ≤ 1000 → rafthttp.bootCfg dir ps) :
    Main.spec (GF := GF) (hG := hG) := by
  intro CS CRE CEC k N ids ps ctxs boot hk1 hk Hlen Hbf Htb HLv Hrb48 HrbN HwbN Haf Hbuq Hrf Hdbo
    Hms hAs
  wp_start as ⟨Hss, Htok, #Hprem⟩
  iunfold premises at Hprem
  icases Hprem with ⟨#Hbps, #Hmarsh, #Hcom⟩
  -- the pure facts of the members and their ids
  obtain ⟨Hpnd, -, -⟩ := idPfxsOf_ok ps Hbf.lowNodup Hbf.lowNz
  have Hpsnd : ps.Nodup := by
    unfold idPfxsOf at Hpnd
    exact List.Pairwise.of_map _ (fun a b h e => h (by rw [e])) Hpnd
  have Hidnd : ids.Nodup := Hbf.perm.nodup_iff.1 Hpsnd
  have Hid0 : W64 0 ∉ ids := fun h => Hbf.lowNz _ (Hbf.perm.symm.subset h) (by decide)
  have Hmlen : (members k).length = ids.length := by rw [membersOf_length, Hlen]
  have Hdok : netDirOk (dirN (members k) ids) :=
    dirN_ok _ ids Hidnd Hid0 (members_peers_nodup k hk) (members_peer_plain k)
  have Hbc : rafthttp.bootCfg (dirN (members k) ids) ps :=
    hbcfg _ ps (fun f => by rw [dirN_ne_nil _ ids Hmlen Hidnd, Hbf.perm.mem_iff])
      (by rw [Hbf.perm.length_eq, Hlen]; exact hk)
  have hblen : boot.length = k := by rw [Hbf.boot.1, Hbf.perm.length_eq, Hlen]
  obtain ⟨id0, hid0⟩ : ∃ id0, id0 ∈ ids := by
    cases ids with
    | nil => simp at Hlen; omega
    | cons a _ => exact ⟨a, by simp⟩
  -- `context`'s `closedchan`, from its package's fact
  ihave #Hcci : context.isClosedchanInit (GF := GF) $$ []
  · iapply context.isClosedchanInit_of_init
    iPkgInit
  ihave #Pzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Pes : isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart $$ []
  · iPkgInit
  ihave #Psrv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver $$ []
  · iPkgInit
  ihave #Pv3 : isPkgInit (PROP := IProp GF)
      pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc $$ []
  · iPkgInit
  ihave #Pcli : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #Ppb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
  · iPkgInit
  -- the ghost state of the cluster and its members (`allocN`)
  imod (allocN hne ids ps Hbf.perm id0 hid0 ctxs boot Hbf.toBootCore (dirN (members k) ids)
      (startOf (members k)) Hdok.1
      (fun i h hm => by rw [startOf_peers]; exact dirN_host _ ids i h hm)
      (by omega) (by omega) .none lease.runCfg_none (fun h => nomatch h))
      $$ Hmarsh Hss
    with ⟨%γ, %γk, %Φs, %γn, %gs, %Hal, #Hnet, Hbs, Hfrs, Hetcd⟩
  isimp only [ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte] at Hetcd
  obtain ⟨hvs, hrule, hboot, hγn1, hγn2, hgids, hgok, hc0, hch, hlog, -, -⟩ := Hal
  have hglen : (members k).length = gs.length := by
    rw [Hmlen, ← hgids, List.length_map]
  -- member `0`'s client address's listen right, out of its fresh bundle (to `Serve`)
  obtain ⟨m0, mr, hms⟩ : ∃ m0 mr, members k = m0 :: mr := by
    cases h : members k with
    | nil => rw [h] at Hmlen; simp at Hmlen; omega
    | cons a r => exact ⟨a, r, rfl⟩
  isimp only [hms, startOf] at Hfrs
  ihave Hfrs := BigSepL.bigSepL_cons.1 $$ Hfrs
  icases Hfrs with ⟨Hfr0, Hfrs⟩
  icases etcdstart.memberFreshRes_client _ _ _ _ rfl $$ Hfr0 with ⟨Hac, Hfr0⟩
  ihave Hfrs : [∗list] m ∈ members k, memberFreshRes m.Name' ⟨some m.Peer', none⟩ γn $$ [Hfr0 Hfrs]
  · rw [hms, BigSepL.bigSepL_map]; iapply BigSepL.bigSepL_cons.2; iframe
  -- each member with its ghost names and its premises
  ihave Hbps' : [∗list] m; id ∈ members k; ids, etcdstart.bootPremise N ps (LogEntry.toEntries boot 0)
      ctxs (dirN (members k) ids) token m.Name' (urlsN (members k) m) id $$ []
  · iexact Hbps
  ihave Hpres := memberPres_of N token (members k) ps (LogEntry.toEntries boot 0) ctxs
    (dirN (members k) ids) Φs γn .none (members k) gs ids hgids hglen $$ Hbps' Hnet Hbs Hfrs
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
      go!"http://" ++ x.1.Peer' ∈ dirN (members k) ids x.2.id := by
    intro x hx
    obtain ⟨⟨r, hr⟩, -⟩ := hgok x.2 (List.of_mem_zip hx).2
    rw [hr]
    refine ⟨hvs, hrule, hboot, hγn1, ?_⟩
    have hmz : (x.1, x.2.id) ∈ (members k).zip ids := by
      rw [← hgids, List.zip_map_right]
      exact List.mem_map_of_mem (f := Prod.map id (·.id)) hx
    rw [dirN_of_mem _ ids Hidnd _ _ hmz]
    simp
  simp only [github_com.mit_pdos.etcd_grove.examples.etcd.putgetN.PeerBase,
    github_com.mit_pdos.etcd_grove.examples.etcd.putgetN.ClientBase,
    github_com.mit_pdos.etcd_grove.examples.etcd.putgetN.Token]
  (try wp_auto)
  wp_apply wp_NewNop as %lg #Hlgz
  (try wp_auto)
  wp_apply (wp_Members go!"putgetN" (W64 k) (W64 24000) (W64 25000) (by word)) as %msl Hmsl
  have hkn : uint.nat (W64 (k : Int)) = k := by word
  imod ownSlice_persist _ _ _ $$ Hmsl with #Hmsl
  ihave #Hmsl' : msl ↦*□ members k $$ []
  · iExactEq Hmsl; rw [hkn]
  iclear Hmsl
  (try wp_auto)
  wp_apply (wp_StartMembers N token (W64 10000) (W64 281474976710656) msl lg ((members k).zip gs) ps
      (LogEntry.toEntries boot 0) ctxs
      (dirN (members k) ids) Φs γn .none false Htb Hrb48 HrbN HwbN (by simp [LogEntry.toEntries, hblen]; omega)
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
  have hk0 : decide ((W64 (k : Int)) = W64 0) = false := by
    rw [decide_eq_false_iff_not]; intro h
    have := congrArg BitVec.toNat h; simp [W64] at this; omega
  simp only [hk0]
  (try wp_auto)
  -- member `0`'s server and its client address
  ihave %Hssl := ownSlice_len $$ Hss
  ihave %Hupl := BigSepL2.bigSepL2_length $$ Hups
  have hzl : ((members k).zip gs).length = k := by rw [List.length_zip, hglen, Nat.min_self, ← hglen, membersOf_length]
  obtain ⟨s0, sr, hss⟩ : ∃ s0 sr, ss = s0 :: sr := by
    cases ss with
    | nil => simp at Hupl; omega
    | cons a r => exact ⟨a, r, rfl⟩
  obtain ⟨g0, gr, hgs⟩ : ∃ g0 gr, gs = g0 :: gr := by
    cases gs with
    | nil => rw [hms] at hglen; simp at hglen
    | cons a r => exact ⟨a, r, rfl⟩
  subst hss hgs
  have Hb0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z ssl.len := by
    obtain ⟨h1, h2⟩ := Hssl
    simp only [List.length_cons] at h1
    constructor <;> word
  simp only [Hb0, _root_.and_self, ↓reduceIte]
  wp_apply wp_load_slice_index _ (sint.Z (W64 0)) _ _ s0 Hb0.1 $$ [Hss] as Hss
  · iframe Hss; ipureintro; rfl
  (try wp_auto)
  have hmsl0 : (members k)[(sint.Z (W64 0)).toNat]? = some m0 := by rw [hms]; rfl
  icases ownSlice_elem_acc _ _ _ _ _ Hb0.1 hmsl0 $$ Hmsl' with ⟨#Hm0, -⟩
  ihave %Hmsll := ownSlice_len $$ Hmsl'
  have Hbm : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z msl.len := by
    obtain ⟨h1, h2⟩ := Hmsll
    rw [membersOf_length] at h1
    constructor <;> word
  simp only [Hbm, _root_.and_self, ↓reduceIte]
  ihave Hm0' := Hm0
  iStructNamedSuffix Hm0' "_m"
  (try wp_auto)
  -- member `0`'s `memberUp`, the thread token given back
  ihave Hups : [∗list] s; x ∈ s0 :: sr; (m0, g0) :: mr.zip gr,
      iprop(threadTok -∗ memberUp s x.2.ρ x.2.E lg γn x.2.id) $$ [Hups]
  · rw [hms, List.zip_cons_cons] at *; iexact Hups
  ihave Hups := BigSepL2.bigSepL2_cons.1 $$ Hups
  icases Hups with ⟨Hup0, -⟩
  ihave Hup0 : memberUp s0 g0.ρ g0.E lg γn g0.id $$ [Hup0 Htok]
  · iapply Hup0; iexact Htok
  have hm0 : m0 = memberAt go!"putgetN" (W64 24000) (W64 25000) (W64 ((0 : Nat) : Int)) := by
    have := membersOf_getElem go!"putgetN" k (W64 24000) (W64 25000) 0 (by omega)
    have hms' : membersOf go!"putgetN" k (W64 24000) (W64 25000) = m0 :: mr := hms
    rw [hms'] at this; simpa using this
  obtain ⟨⟨r0, hr0⟩, hst0, hc00, hch0, hlog0, hs0⟩ := hgok g0 (by simp)
  icases etcdstart.memberUp_served _ _ _ _ _ _ _ $$ Hup0 with ⟨%E, %cfg, %γw, %HEc, #Hreq, #Hrd,
    #Hsf, Hgo, Hlg3, Hbemu, #Hwb, Hstk, -, -⟩
  obtain ⟨HEa, HEo, HElg, HEtr, HEw⟩ := HEc
  -- `Serve(srvs[0], ms[0].Client)`, with etcd's KV calls registered at the address
  iclear Hm0 Hm0' Name_m Peer_m __m Hbps Hss Hmarsh
  haveI := Hms
  ihave ⟨%HsvOff, #HreqM, #HrdM, #Hlb⟩ := etcdstart.serveViews_off s0 E { g0.ρ with wait := γw }
    g0.ρ.rd $$ []
  · iframe #
  ihave #HzlgC : zapLoggerOk cfg.Logger' $$ []
  · rw [HElg]; iexact Hlgz
  wp_apply (wp_Serve s0 m0.Client' E { g0.ρ with wait := γw } g0.ρ.rd cfg
      (fun cid mid _ => etcdstart.etcdKVAt m0.Client' E { g0.ρ with wait := γw } g0.ρ.rd cid mid))
    $$ [Hac Hlg3 Hbemu Hgo Hstk] as %serr Hs
  · iframe; iframe #
    isplitr
    · ipureintro; exact ⟨HEtr, HEw, Hms, Hbuq, HsvOff.2, Htb⟩
    iintro %gs' %lis %cid %mid %R Hg
    rw [HsvOff.1]
    ihave Hg := etcdstart.grpcUpM_false _ _ _ _ _ _ _ _ _ _ $$ Hg
    iapply (etcdstart.kv_served s0 E { g0.ρ with wait := γw } g0.ρ.rd gs' lis m0.Client' cid mid R
      Hrb48 Hrf rfl HLv)
    iframe; iframe #
  icases Hs with (%Hserr | ⟨%Hserr, %cid, %mid, %R, #Hkv⟩)
  · cases serr with
    | nil => exact absurd rfl Hserr
    | ok ei => ?_
    wp_auto
    iapply HΦ; itrivial
  subst Hserr
  wp_auto
  ihave #Hregs := etcdstart.etcdKVAt_regs m0.Client' E { g0.ρ with wait := γw } g0.ρ.rd cid mid
    rfl $$ Hkv
  -- `NewClient(ms[0].Client, lg)` (etcd's default client configuration)
  simp only [Hbm, _root_.and_self, ↓reduceIte]
  (try wp_auto)
  wp_apply (wp_NewClient m0.Client' lg
      (EtcdGrove.client.srvWEnv R (etcdstart.srvWOf R.E g0.ρ.rd false) g0.ρ.rd m0.Client' [] null
        null [] null default)
      (by rw [hm0]; exact loopback_plainEndpoint _) (by omega)) as %cl %cerr Hcl
  · iframe #
  icases Hcl with (⟨%Hcerr, #Hnc, -⟩ | %Hcfail)
  rotate_left
  · obtain ⟨Hcerr, -⟩ := Hcfail
    cases cerr with
    | nil => exact absurd rfl Hcerr
    | ok ei => ?_
    wp_auto
    iapply HΦ; itrivial
  subst Hcerr
  wp_auto
  -- `pctx, pcancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)`
  wp_apply wp_Background
  (try wp_auto)
  wp_apply (client.wp_WithTimeout_bg hWT wp_ErrAny hAs _) $$ []
    as %pctx %pcd %pcancel ⟨#Hpcancel, #Hpctx, #Hpce, -⟩
  (try wp_auto)
  -- the client's invariant at member `0`'s KV names (the cluster's), the floor, no options
  ihave Hetcd : etcdKV g0.ρ.rd.kv (kvStateOf (kvModel g0.ρ.rd.kv (bootEntries (LogEntry.toEntries boot 0))))
    $$ [Hetcd]
  · rw [etcdKV_congr γk g0.ρ.rd.kv hst0.symm,
      show kvModelSt γk (bootEntries (LogEntry.toEntries boot 0)) =
        kvModelSt g0.ρ.rd.kv (bootEntries (LogEntry.toEntries boot 0)) by
        unfold kvModelSt kvLeases kvModel; rw [hc00, hch0, hlog0],
      kvModelSt_boot _ (fun _ _ => True) _ _ (srvBootLogOk_of_BootLog _ _ _ Hbf.boot)]
    iexact Hetcd
  imod (client.putGetInv_alloc_log g0.ρ.rd (kvModel g0.ρ.rd.kv
      (bootEntries (LogEntry.toEntries boot 0))) go!"k" go!"v" ⊤)
    $$ Hetcd with ⟨%γf, #Hinv⟩
  imod v3rpc.kvLogLb_nil (GF := GF) E.γs with #HF0
  ihave #Hnil : optsAt (GF := GF) slice.nil [] $$ []
  · iunfold optsAt
    iexists ([] : List GoFunc)
    isplitl
    · iapply ownSlice_nil
    isplitl
    · ipureintro; rfl
    imodintro
    iintro %i %f %g %Hf %Hg
    simp at Hf
  -- `cli.Put(ctx, "k", "v")`
  wp_apply (client.client_Put_own cl m0.Client' _ E g0.ρ.rd γf cid mid
      pctx pcd go!"k" go!"v" slice.nil []
      (opSizeOk_opPutModel (K := 1) (E := 0) (V := 1) (optsKeep_nil _ _ _) (by decide) (by decide)
        (by decide))) as %presp %perr Hput
  · iframe #
  (try wp_auto)
  wp_apply Hpcancel
  icases Hput with (⟨%Hperr, -, #Hflag⟩ | %Hpfail)
  rotate_left
  · obtain ⟨Hperr, -⟩ := Hpfail
    cases perr with
    | nil => exact absurd rfl Hperr
    | ok ei => ?_
    wp_auto
    iapply HΦ; itrivial
  subst Hperr
  (try wp_auto)
  -- `gctx, gcancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)`
  wp_apply wp_Background
  (try wp_auto)
  wp_apply (client.wp_WithTimeout_bg hWT wp_ErrAny hAs _) $$ []
    as %gctx %gcd %gcancel ⟨#Hgcancel, #Hgctx, #Hgce, -⟩
  (try wp_auto)
  -- `cli.Get(gctx, "k")`
  imod monoNatLbOwn_0 (GF := GF) g0.ρ.rd.committed with #Hc0
  wp_apply (client.client_Get_own cl m0.Client' _ E g0.ρ.rd γf (W64 0) cid mid
      gctx gcd go!"k" go!"v" slice.nil []
      (opSizeOk_opGetModel (K := 1) (E := 0) (V := 0) (optsKeep_nil _ _ _) (by decide) (by decide)))
    as %gresp %gerr Hget
  · iframe #
    iunfold committedAtLeast; ileft
    iExactEq Hc0; rfl
  (try wp_auto)
  wp_apply Hgcancel
  icases Hget with (⟨%Hgerr, %m, #Hm, %Hv⟩ | %Hgfail)
  rotate_left
  · obtain ⟨Hgerr, -⟩ := Hgfail
    cases gerr with
    | nil => exact absurd rfl Hgerr
    | ok ei => ?_
    wp_auto
    iapply HΦ; itrivial
  subst Hgerr
  (try wp_auto)
  iunfold rangeRespMsg at Hm
  icases Hm with ⟨%Hnn, %h, %sl, %kvps, #Hh, #Hhf, #Hkvf, #Hsl, #Hkvs, #Hmore, #Hcount⟩
  -- the reply's first key-value holds `v`
  obtain ⟨kv0, Hkv0, Hval0⟩ : ∃ kv0, m.kvs[0]? = some kv0 ∧ kv0.value = go!"v" := by
    cases h : m.kvs with
    | nil => simp [h] at Hv
    | cons x xs => simp [h] at Hv; exact ⟨x, rfl, Hv⟩
  iunfold txn.kvsIs at Hkvs
  icases Hkvs with ⟨%Hlen', #Hall⟩
  obtain ⟨p0, Hp0⟩ : ∃ p0, kvps[0]? = some p0 := by
    have : 0 < kvps.length := by
      rw [Hlen']
      cases h : m.kvs with
      | nil => simp [h] at Hkv0
      | cons x xs => simp
    exact ⟨kvps[0], List.getElem?_eq_getElem this⟩
  ihave #Hkv := Hall $$ %0 %p0 %kv0 %Hp0 %Hkv0
  iunfold txn.kvIs at Hkv
  icases Hkv with ⟨%kSl, %vSl, -, -, -, -, -, #HvF, #HvS, -⟩
  ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
  have Hne : decide (sl.len = W64 0) = false := by
    rw [decide_eq_false_iff_not]
    intro h
    have hl := Hsll.1
    rw [h] at hl
    have : 0 < kvps.length := List.length_pos_of_mem (List.mem_of_getElem? Hp0)
    rw [hl] at this
    exact absurd this (by decide)
  wp_auto
  simp only [Hne]
  wp_auto
  have Hbnd : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z sl.len := by
    have := Hsll.1
    have : 0 < kvps.length := List.length_pos_of_mem (List.mem_of_getElem? Hp0)
    constructor <;> word
  simp only [Hbnd, _root_.and_self, ↓reduceIte]
  wp_apply wp_load_slice_index _ (sint.Z (W64 0)) _ DFrac.discard p0 Hbnd.1 $$ [Hsl] as -
  · iframe Hsl; ipureintro; exact Hp0
  wp_apply wp_bytes_to_string vSl kv0.value DFrac.discard $$ [HvS] as -
  · iframe #
  rw [Hval0]
  wp_auto
  iapply HΦ; itrivial

end proof

end etcd_putgetN
end EtcdGrove
end Perennial
