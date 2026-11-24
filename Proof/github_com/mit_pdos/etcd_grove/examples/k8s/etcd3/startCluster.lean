/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/k8s/etcd3/startCluster.lean` (stage A of
`notes/k8s-7f6-scope.md`). Lean-first (no Rocq counterpart). txnlinfaultsN's
`startCluster.wp_proof` (`etcd/txnlinfaultsN/startCluster.lean`), at these members, with the second
loop (`k` clients) replaced by one `kubernetes.New` of the `k` bridges (as the 3-member
`MainCluster`'s was), over the bridge addresses' slice the first loop filled.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.startCluster
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.bridgeAddr
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.holdToken
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.DirN
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.StartLemmas
public import Spec.go_etcd_io.etcd.client.v3.kubernetes.New
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Members
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.StartMembers
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Serve
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.cluster3.StartBridge
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.AllocN
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Served
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.WatchServed
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.WatchServedLinked

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver etcdstart
open k8s_etcd3N

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

set_option maxHeartbeats 4000000 in
theorem startCluster.wp_proof
    (wp_Members : etcdstart.Members.spec (GF := GF) (hG := hG))
    (wp_StartMembers : etcdstart.StartMembers.spec (GF := GF) (hG := hG))
    (wp_Serve : etcdstart.Serve.spec (GF := GF) (hG := hG))
    (wp_kNew : kubernetes.New.spec (GF := GF) (hG := hG))
    (wp_StartBridge : cluster3.StartBridge.spec (GF := GF) (hG := hG))
    (wp_bridgeAddr : bridgeAddr.spec (GF := GF) (hG := hG))
    (wp_holdToken : holdToken.spec (GF := GF) (hG := hG))
    (hne : mvcc.api.names_nonempty.law)
    (Hp : mvcc.api.persistent.law (GF := GF)) (Hr : mvcc.api.mvccState_reachable.law (GF := GF))
    (hbcfg : ∀ (dir : w64 → List GoString) (ps : List w64), (∀ f, dir f ≠ [] ↔ f ∈ ps) →
      ps.length ≤ 1000 → rafthttp.bootCfg dir ps) :
    startCluster.spec (GF := GF) (hG := hG) := by
  intro CS k N ids ps ctxs boot lg ThB RcB RcN hk1 hk Hlen Hbf HLv HwbN Haf Hbuq Hrf Hdbo Hms
  have Htb := ThreadBoundLe.le (GF := GF) (2 ^ 28)
  have Hrb48 := ReceiptBoundLe.le (GF := GF) (2 ^ 48)
  have HrbN := ReceiptBoundLe.le (GF := GF) (N + 1)
  wp_start as ⟨#Hlgz, Hss, Hbfree, Htok, #Hprem⟩
  iunfold premises at Hprem
  icases Hprem with ⟨#Hbps, #Hmarsh, #Hcom⟩
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
  ihave #Pc3 : isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.cluster3 $$ []
  · iPkgInit
  ihave #Psrv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver $$ []
  · iPkgInit
  ihave #Pv3 : isPkgInit (PROP := IProp GF)
      pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc $$ []
  · iPkgInit
  ihave #Ppb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
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
  -- each member's raft read names its boot names' (for `memberOf`)
  ihave ⟨%Hraft, Hbs⟩ := memberBoots_raft ctxs Φs false .none gs $$ Hbs
  -- each member with its ghost names and its premises
  ihave Hbps' : [∗list] m; id ∈ members k; ids, etcdstart.bootPremise N ps (LogEntry.toEntries boot 0)
      ctxs (etcd_putgetN.dirN (members k) ids) k8s_etcd3N.token m.Name' (urlsN (members k) m) id $$ []
  · iexact Hbps
  ihave Hpres := memberPres_of N k8s_etcd3N.token (members k) ps (LogEntry.toEntries boot 0) ctxs
    (etcd_putgetN.dirN (members k) ids) Φs γn .none (members k) gs ids hgids hglen $$ Hbps' Hnet Hbs Hfrs
  have hxs1 : ((members k).zip gs).map (·.1) = members k := List.map_fst_zip (by omega)
  have hutf : ∀ x ∈ (members k).zip gs, utf8Valid x.1.Name' :=
    fun x hx => members_names_utf8 k _ (List.of_mem_zip hx).1
  have hnlen : ∀ x ∈ (members k).zip gs, x.1.Name'.length ≤ 200 :=
    fun x hx => members_names_len k _ (List.of_mem_zip hx).1
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
  simp only [github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.PeerBase,
    github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ClientBase,
    github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Token,
    github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.SnapCount,
    github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.SnapCatchUp]
  (try wp_auto)
  wp_apply (wp_Members go!"k8setcd3N" (W64 k) (W64 20000) (W64 21000) (by word)) as %msl Hmsl
  have hkn : uint.nat (W64 (k : Int)) = k := by word
  imod ownSlice_persist _ _ _ $$ Hmsl with #Hmsl
  ihave #Hmsl' : msl ↦*□ members k $$ []
  · iExactEq Hmsl; rw [hkn]
  iclear Hmsl
  (try wp_auto)
  wp_apply (wp_StartMembers N k8s_etcd3N.token (W64 1) (W64 1) msl lg ((members k).zip gs) ps
      (LogEntry.toEntries boot 0) ctxs
      (etcd_putgetN.dirN (members k) ids) Φs γn .none false Htb Hrb48 HrbN HwbN
      (by simp [LogEntry.toEntries, hblen]; omega)
      hγn2 Hdok Hbc hnd hutf hnlen hxok Haf Hbuq Hdbo) $$ [Htok Hpres] as %ssl %serr Hsr
  · rw [hxs1]
    iframe; iframe #
  icases Hsr with ⟨Htok, (%Hserr | ⟨%Hserr, %ss, Hss, Hups⟩)⟩
  · cases serr with
    | nil => exact absurd rfl Hserr
    | ok ei => ?_
    (try wp_auto)
    iapply HΦ; ileft; itrivial
  subst Hserr
  (try wp_auto)
  imod ownSlice_persist _ _ _ $$ Hss with #Hss
  ihave %Hssl := ownSlice_len $$ Hss
  ihave %Hupl := BigSepL2.bigSepL2_length $$ Hups
  have hzl : ((members k).zip gs).length = k := by
    rw [List.length_zip, ← hglen, Nat.min_self, membersOf_length]
  have hssk : ss.length = k := by rw [Hupl, hzl]
  -- the first member's read names: the history's (`memberOf`) for every member
  obtain ⟨g0, hg0⟩ : ∃ g0, g0 ∈ gs :=
    List.exists_mem_of_ne_nil gs (by
      intro h; have := hglen; rw [h, List.length_nil, membersOf_length] at this; omega)
  -- `brs := make([]bridge.Bridge, k)`, `baddrs := make([]string, k)`
  wp_apply (wp_slice_make2 (V := GoInterface) (W64 k)) as %brsl ⟨Hbrsl, -⟩
  · ipureintro; word
  (try wp_auto)
  wp_apply (wp_slice_make2 (V := GoString) (W64 k)) as %basl ⟨Hbasl, -⟩
  · ipureintro; word
  (try wp_auto)
  -- the first loop: each member served behind its bridge
  ihave HI : (∃ (j : w64) (bs : List GoInterface) (svs : List (client.SrvAt GF))
      (ws : List (Loc × v3rpc.WSrv GF)),
      "i" ∷ i_ptr ↦ j ∗
      "Hbrsl" ∷ brsl ↦* (bs ++ List.replicate (k - bs.length) (zero_val GoInterface)) ∗
      "Hbasl" ∷ basl ↦* (bridges (uint.nat j) ++ List.replicate (k - uint.nat j) (zero_val GoString)) ∗
      "Hups" ∷ ([∗list] s; x ∈ ss.drop (uint.nat j); ((members k).zip gs).drop (uint.nat j),
        (threadTok -∗ memberUp s x.2.ρ x.2.E lg γn x.2.id .none)) ∗
      "Hcfree" ∷ ([∗list] m ∈ (members k).drop (uint.nat j), netAddrFree (GF := GF) m.Client') ∗
      "Hbfree" ∷ ([∗list] b ∈ (bridges k).drop (uint.nat j), netAddrFree (GF := GF) b) ∗
      "Hctl" ∷ ([∗list] s ∈ ss.take (uint.nat j), ∃ id : w64, etcdstart.srvPeerCtl γn s id) ∗
      "Hobs" ∷ ([∗list] br ∈ bs, ∃ addr : GoString, bridge.ownBridge br addr false) ∗
      "#Hregs" ∷ ([∗list] sv ∈ svs, client.kvRegsAt sv) ∗
      "#Hws" ∷ ([∗list] sv; w ∈ svs; ws, etcdstart.watchRegAt sv.addr w.1 sv.E sv.γr w.2 ∗
        isServerRead w.1 sv.E sv.γr) ∗
      "%Hj" ∷ ⌜uint.nat j ≤ k ∧ bs.length = uint.nat j ∧ svs.map client.SrvAt.addr = bridges (uint.nat j) ∧
        (∀ sv ∈ svs, kvSame sv.γr.kv γk ∧ noRefusalAt sv.addr) ∧
        (∀ sv ∈ svs, v3rpc.memberOf g0.ρ.rd.raft g0.ρ.rd.kv sv.γr)⌝ : IProp GF)
      $$ [i Hbrsl Hbasl Hups Hcfree Hbfree]
  · iexists W64 0, [], [], []
    have h00 : uint.nat (W64 0) = 0 := rfl
    simp only [h00, List.drop_zero, List.take_zero, List.length_nil, Nat.sub_zero, List.nil_append]
    iframe
    isplitl [Hbrsl]
    · iExactEq Hbrsl; rw [show sint.nat (W64 (k : Int)) = k by word]
    isplitl [Hbasl]
    · iExactEq Hbasl; rw [show sint.nat (W64 (k : Int)) = k by word]; simp [bridges]
    isplitl
    · iapply BigSepL.bigSepL_nil.2; itrivial
    isplitl
    · iapply BigSepL.bigSepL_nil.2; itrivial
    isplitl
    · iapply BigSepL.bigSepL_nil.2; itrivial
    isplitl
    · iapply BigSepL2.bigSepL2_nil.2; itrivial
    ipureintro
    refine ⟨by omega, ?_⟩; simp [bridges]
  wp_for HI
  wp_if_destruct
  · -- one more member: `go holdToken()`, `Serve`, its bridge
    have hj : uint.nat j < k := by rw [← hkn]; word
    list_elem ss (uint.nat j) as sj
    list_elem ((members k).zip gs) (uint.nat j) as xj
    have hmj : (members k)[uint.nat j]? = some xj.1 := by
      have := List.getElem?_zip_eq_some.1 Hxj_lookup
      exact this.1
    have hgj : gs[uint.nat j]? = some xj.2 := (List.getElem?_zip_eq_some.1 Hxj_lookup).2
    have hxjm : xj.1 = memberAt go!"k8setcd3N" (W64 20000) (W64 21000) (W64 ((uint.nat j : Nat) : Int)) := by
      have := membersOf_getElem go!"k8setcd3N" k (W64 20000) (W64 21000) (uint.nat j) hj
      rw [hmj] at this; exact Option.some.inj this
    -- `go holdToken()`: the forked goroutine never returns, its thread token stays here
    wp_apply wp_fork_tok_self as Htok'
    · wp_apply wp_holdToken as Hf
      iexfalso; iexact Hf
    (try wp_auto)
    -- the member's `memberUp`, the token given back
    isimp only [drop_cons_of_getElem? ss _ sj Hsj_lookup,
      drop_cons_of_getElem? ((members k).zip gs) _ xj Hxj_lookup] at Hups
    ihave Hups := BigSepL2.bigSepL2_cons.1 $$ Hups
    icases Hups with ⟨Hupj, Hups⟩
    ihave Hupj : memberUp sj xj.2.ρ xj.2.E lg γn xj.2.id .none $$ [Hupj Htok']
    · iapply Hupj; iexact Htok'
    isimp only [drop_cons_of_getElem? (members k) _ xj.1 hmj] at Hcfree
    ihave Hcfree := BigSepL.bigSepL_cons.1 $$ Hcfree
    icases Hcfree with ⟨Hcj, Hcfree⟩
    obtain ⟨⟨r, hr⟩, -, -, -, -, hstj⟩ := hgok xj.2 (List.mem_of_getElem? hgj)
    icases etcdstart.memberUp_served _ _ _ _ _ _ _ $$ Hupj with ⟨%E, %cfg, %γw, %HEc, #Hreq, #Hrd,
      #Hsf, Hgo, Hlg3, Hbemu, #Hwb, Hstk, Hctlj, -⟩
    obtain ⟨HEa, HEo, HElg, HEtr, HEw⟩ := HEc
    -- `srvs[i]`, `ms[i].Client`
    have Hbs : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z ssl.len := by
      obtain ⟨h1, h2⟩ := Hssl
      constructor <;> word
    simp only [Hbs, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index _ (sint.Z j) _ _ sj Hbs.1 $$ [Hss] as -
    · iframe #; ipureintro
      rw [show (sint.Z j).toNat = uint.nat j by word]; exact Hsj_lookup
    (try wp_auto)
    ihave %Hmsll := ownSlice_len $$ Hmsl'
    have Hbm : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z msl.len := by
      obtain ⟨h1, h2⟩ := Hmsll
      rw [membersOf_length] at h1
      constructor <;> word
    simp only [Hbm, _root_.and_self, ↓reduceIte]
    have hmsj : (members k)[(sint.Z j).toNat]? = some xj.1 := by
      rw [show (sint.Z j).toNat = uint.nat j by word]; exact hmj
    icases ownSlice_elem_acc _ _ _ _ _ Hbm.1 hmsj $$ Hmsl' with ⟨#Hmj, -⟩
    ihave Hmj' := Hmj
    iStructNamedSuffix Hmj' "_m"
    (try wp_auto)
    -- `Serve(srvs[i], ms[i].Client)`: etcd's KV calls registered at the client address, the address
    -- refusal-free
    haveI := Hms
    ihave ⟨%HsvOff, #HreqM, #HrdM, #Hlb⟩ := etcdstart.serveViews_off sj E { xj.2.ρ with wait := γw }
      xj.2.ρ.rd $$ []
    · iframe #
    ihave #HzlgC : zapLoggerOk cfg.Logger' $$ []
    · rw [HElg]; iexact Hlgz
    wp_apply (wp_Serve sj xj.1.Client' E { xj.2.ρ with wait := γw } xj.2.ρ.rd cfg
        (fun cid mid R => iprop(etcdstart.etcdKVAt xj.1.Client' E { xj.2.ρ with wait := γw } xj.2.ρ.rd
          cid mid ∗ etcdstart.watchRegAt xj.1.Client' sj E xj.2.ρ.rd R ∗ ⌜noRefusalAt xj.1.Client'⌝)))
      $$ [Hcj Hlg3 Hbemu Hgo Hstk] as %serr Hsv
    · iframe; iframe #
      isplitr
      · ipureintro; exact ⟨HEtr, HEw, Hms, Hbuq, HsvOff.2, Htb⟩
      iintro %gs' %lis %cid %mid %R Hg
      rw [HsvOff.1]
      ihave Hg := etcdstart.grpcUpM_false _ _ _ _ _ _ _ _ _ _ $$ Hg
      imod (etcdstart.kvWatch_served Hp Hr sj E { xj.2.ρ with wait := γw } xj.2.ρ.rd cfg gs' lis
        xj.1.Client' cid mid R Hrb48 Hrf rfl HLv Hms
        (by rw [sync.rwmutex.actualMaxReaders_unseal]; omega)) $$ [Hg Hstk] with ⟨Htk, #Hkv, #Hksa, #Hwr⟩
      · iframe; iframe #
      -- (D29) the member never refuses: the server now at its address is etcd's, authentication off
      ihave %Hnr := EtcdGrove.etcd_noRefusal_at xj.1.Client' sj E { xj.2.ρ with wait := γw } HEo $$ [Hksa]
      · iframe #
      imodintro
      iframe Htk
      iframe #
      ipureintro
      exact Hnr
    icases Hsv with (%Hserr | ⟨%Hserr, %cid, %mid, %R, #Hkv, #Hwr, %Hnr⟩)
    · cases serr with
      | nil => exact absurd rfl Hserr
      | ok ei => ?_
      (try wp_auto)
      wp_for_post
      iapply HΦ; ileft; itrivial
    subst Hserr
    (try wp_auto)
    -- `ba := bridgeAddr(i)`
    wp_apply wp_bridgeAddr as %ba %Hba
    subst Hba
    (try wp_auto)
    -- `cluster3.StartBridge(ba, ms[i].Client)`
    have hbj : (bridges k)[uint.nat j]? = some (bridgeAt j) := by
      rw [bridges_getElem k (uint.nat j) hj]; congr 1; congr 1; word
    isimp only [drop_cons_of_getElem? (bridges k) _ _ hbj] at Hbfree
    ihave Hbfree := BigSepL.bigSepL_cons.1 $$ Hbfree
    icases Hbfree with ⟨Hbj, Hbfree⟩
    simp only [Hbm, _root_.and_self, ↓reduceIte]
    (try wp_auto)
    wp_apply (wp_StartBridge (bridgeAt j) xj.1.Client') $$ [Hbj] as %br %berr Hbr
    · iframe
    icases Hbr with (⟨%Hberr, Hob, #Hfw⟩ | %Hberr)
    rotate_left
    · cases berr with
      | nil => exact absurd rfl Hberr
      | ok ei => ?_
      (try wp_auto)
      wp_for_post
      iapply HΦ; ileft; itrivial
    subst Hberr
    (try wp_auto)
    -- `brs[i] = br`, `baddrs[i] = ba`
    ihave %Hbrl := ownSlice_len $$ Hbrsl
    ihave %Hbal := ownSlice_len $$ Hbasl
    have hbsl : (bs ++ List.replicate (k - bs.length) (zero_val GoInterface)).length = k := by
      simp; omega
    have hbal : (bridges (uint.nat j) ++ List.replicate (k - uint.nat j) (zero_val GoString)).length = k := by
      simp [bridges_length]; omega
    rw [hbsl] at Hbrl
    rw [hbal] at Hbal
    have Hb2 : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z brsl.len := by
      obtain ⟨h1, h2⟩ := Hbrl; constructor <;> word
    have Hb3 : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z basl.len := by
      obtain ⟨h1, h2⟩ := Hbal; constructor <;> word
    simp only [Hb2, _root_.and_self, ↓reduceIte]
    wp_apply (wp_store_slice_index brsl (sint.Z j) _ br) $$ [Hbrsl] as Hbrsl
    · iframe Hbrsl; ipureintro; rw [hbsl]; constructor <;> word
    (try wp_auto)
    simp only [Hb3, _root_.and_self, ↓reduceIte]
    wp_apply (wp_store_slice_index basl (sint.Z j) _ (bridgeAt j)) $$ [Hbasl] as Hbasl
    · iframe Hbasl; ipureintro; rw [hbal]; constructor <;> word
    (try wp_auto)
    -- the member as the clients reach it: at its bridge's address
    ihave #Hrg : client.kvRegsAt (⟨bridgeAt j, E, xj.2.ρ.rd, cid, mid⟩ : client.SrvAt GF) $$ []
    · iapply kvRegs_forwards
      iframe #
      iapply etcdstart.etcdKVAt_regs xj.1.Client' E { xj.2.ρ with wait := γw } xj.2.ρ.rd cid mid rfl
      iexact Hkv
    ihave %Hnrb : ⌜noRefusalAt (bridgeAt j)⌝ $$ []
    · iunfold cluster3.forwards at Hfw; icases Hfw with ⟨-, %Hf⟩; ipureintro; exact Hf Hnr
    ihave Hobs : [∗list] br' ∈ bs ++ [br], ∃ addr : GoString, bridge.ownBridge br' addr false
      $$ [Hobs Hob]
    · iapply BigSepL.bigSepL_snoc.2
      iframe Hobs
      iexists xj.1.Client'; iexact Hob
    ihave Hctl : [∗list] s ∈ ss.take (uint.nat j + 1), ∃ id : w64, etcdstart.srvPeerCtl γn s id
      $$ [Hctl Hctlj]
    · rw [List.take_add_one, Hsj_lookup, Option.toList_some]
      iapply BigSepL.bigSepL_snoc.2
      iframe Hctl
      iexists xj.2.id; iexact Hctlj
    ihave #Hregs' : [∗list] sv ∈ svs ++ [⟨bridgeAt j, E, xj.2.ρ.rd, cid, mid⟩], client.kvRegsAt sv
      $$ []
    · iapply BigSepL.bigSepL_snoc.2
      iframe #
    iclear Hregs
    ihave #Hws' : [∗list] sv; w ∈ svs ++ [⟨bridgeAt j, E, xj.2.ρ.rd, cid, mid⟩]; ws ++ [(sj, R)],
        etcdstart.watchRegAt sv.addr w.1 sv.E sv.γr w.2 ∗ isServerRead w.1 sv.E sv.γr $$ []
    · iapply BigSepL2.bigSepL2_snoc.2
      iframe #
      iapply watchRegAt_forwards
      iframe #
    iclear Hws
    wp_for_post
    iframe
    iexists j + W64 1, bs ++ [br], svs ++ [⟨bridgeAt j, E, xj.2.ρ.rd, cid, mid⟩], ws ++ [(sj, R)]
    have hj1 : uint.nat (j + W64 1) = uint.nat j + 1 := by word
    have hjz : (sint.Z j).toNat = uint.nat j := by word
    have hjb : (sint.Z j).toNat = bs.length := by rw [hjz, Hj.2.1]
    rw [hj1]
    iframe
    isplitl [Hbrsl]
    · iExactEq Hbrsl
      rw [hjb, set_replicate_snoc _ _ _ _ (by omega)]
      simp only [List.length_append, List.length_singleton]
    isplitl [Hbasl]
    · iExactEq Hbasl
      have hset := set_replicate_snoc (bridges (uint.nat j)) k (zero_val GoString) (bridgeAt j)
        (by rw [bridges_length]; omega)
      rw [bridges_length] at hset
      rw [hjz, hset, bridges_succ, show bridgeAt (W64 ((uint.nat j : Nat) : Int)) = bridgeAt j by
        congr 1; word]
    isplitr
    · iexact Hregs'
    isplitr
    · iexact Hws'
    ipureintro
    have hmemj : xj.2 ∈ gs := List.mem_of_getElem? hgj
    refine ⟨by omega, by simp [Hj.2.1], ?_, ?_, ?_⟩
    · rw [List.map_append, Hj.2.2.1, bridges_succ]
      simp only [List.map_cons, List.map_nil]
      congr 2; congr 1; word
    · intro sv hsv
      rcases List.mem_append.1 hsv with h | h
      · exact Hj.2.2.2.1 sv h
      · simp only [List.mem_singleton] at h
        subst h
        exact ⟨hstj, Hnrb⟩
    · intro sv hsv
      rcases List.mem_append.1 hsv with h | h
      · exact Hj.2.2.2.2 sv h
      · simp only [List.mem_singleton] at h
        subst h
        exact memberOf_of_gOk γ γk xj.2 g0 (hgok xj.2 hmemj) (hgok g0 hg0) (Hraft xj.2 hmemj)
          (Hraft g0 hg0)
  · -- every member served: the second loop, `k` clients of every bridge
    have hjk : uint.nat j = k := by
      have : ¬ (uint.nat j < k) := by rw [← hkn]; word
      omega
    have hbsk : bs.length = k := by rw [Hj.2.1, hjk]
    have hsvk : svs.map client.SrvAt.addr = bridges k := by rw [Hj.2.2.1, hjk]
    have hsv := Hj.2.2.2.1
    have hmo := Hj.2.2.2.2
    -- the client's watch environment: the members' (`watchEnvL`)
    ihave %Hwsl := BigSepL2.bigSepL2_length $$ Hws
    have hsvl : svs.length = k := by
      have := congrArg List.length hsvk; simpa [bridges_length] using this
    obtain ⟨sv0, -⟩ := List.exists_mem_of_ne_nil svs (by
      intro h; have := hsvl; rw [h, List.length_nil] at this; omega)
    obtain ⟨w0, -⟩ := List.exists_mem_of_ne_nil ws (by
      intro h; have := Hwsl; rw [h, List.length_nil] at this; omega)
    obtain ⟨m0, -⟩ : ∃ m0 : etcdstart.WMem GF,
      m0 = (sv0.addr, w0.2, etcdstart.srvWOf sv0.E sv0.γr false) := ⟨_, rfl⟩
    obtain ⟨V, hV⟩ : ∃ V : client.WEnv GF, V = etcdstart.watchEnvL m0 (wmemsOf svs ws) g0.ρ.rd wpfx :=
      ⟨_, rfl⟩
    ihave Hbasl : basl ↦* bridges k $$ [Hbasl]
    · iExactEq Hbasl; simp only [hjk, Nat.sub_self, List.replicate_zero, List.append_nil]
    ihave Hbrsl : brsl ↦* bs $$ [Hbrsl]
    · iExactEq Hbrsl; simp only [hbsk, Nat.sub_self, List.replicate_zero, List.append_nil]
    ihave Hctl : [∗list] s ∈ ss, ∃ id : w64, etcdstart.srvPeerCtl γn s id $$ [Hctl]
    · iExactEq Hctl; rw [hjk, List.take_of_length_le (by omega)]
    iclear Hups Hcfree Hbfree
    imod ownSlice_persist _ _ _ $$ Hbasl with #Hbasl
    imod ownSlice_persist _ _ _ $$ Hbrsl with #Hbrsl
    (try wp_auto)
    haveI : ThreadBoundLe GF (2 ^ 31) := ⟨by omega⟩
    have Hpl := bridges_plain k hk1
    -- `kubernetes.New(Config{Endpoints: baddrs, DialTimeout, keepalive, Logger: lg})`
    ihave #Pkc : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.kubernetes $$ []
    · iPkgInit
    wp_apply (wp_kNew _ (bridges k) V (fun _ => iprop(True))) $$ []
      as %kc %cerr Hcl
    · iframe #
      iunfold clientCfgOk
      simp only
      iframe #
      isplitr
      · isplitr
        · iapply ownSlice_nil
        ipureintro
        refine ⟨Hpl, ?_⟩
        simp
      iapply clientAuthPre_anon; rfl
    icases Hcl with (⟨%Hcerr, %cl, #Hkc, #Hnc, -⟩ | %Hcfail)
    rotate_left
    · cases cerr with
      | nil => exact absurd rfl Hcfail
      | ok ei => ?_
      (try wp_auto)
      iapply HΦ; ileft; itrivial
    subst Hcerr
    (try wp_auto)
    iapply HΦ
    iright
    iframe
    isplitr
    · ipureintro; rfl
    iunfold clusterUp
    iexists γk, γn, ss, bs, cl, V, svs, ws, g0.ρ.rd, m0
    iframe; iframe #
    obtain ⟨-, -, -, -, hlog0, hks0⟩ := hgok g0 hg0
    ipureintro
    exact ⟨⟨hssk, hsvk, hlog, hsv⟩, hks0, by rw [hlog0, hlog], hmo, hV⟩

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
