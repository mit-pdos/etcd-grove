/-
The proof of `Spec/github_com/mit_pdos/etcd_grove/examples/k8s/compactor/Main.lean` (K4 of
`notes/k8s-compactor-plan.md`). Lean-first.

As `examples/k8s/etcd3`'s `Main` to the served member (the one-member premises in the shared start's
form, `bootPremise_of`; the ghost state `NewServer` takes, `alloc1_false` in compaction mode at
retention `0`; `StartCompactingServer`; `Serve`, the member refusal-free and its KV calls registered,
with the watch server's facts at the address as `compactwatch`'s `Main` serves them, `wk_served_nd`:
no revision writes a key twice, `noDupKeys_of_one`), with the example's invariant allocated at the
member's start state (no key; `cinv_alloc`). Then the writer's client and its readiness check, the
writer (`go writer(wcli)`), and the API servers, each with a client of its own (its KV handle,
`isKv_of_newClient`, and its watcher, `isNewClient_watcher`: the compactor's watch loop runs, Q1 (b)),
forked under a wait group (`sync.join`) that `Main` waits for; the client address claimed for the
cluster from the registry's authority (`epOf_alloc`, Q1 (c), C3), for the API servers sharing the
process's compactor.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.Main
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.ready
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.writer
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.apiserver
public import Spec.go_uber_org.zap.NewNop
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.StartCompactingServer
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Serve
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.NewClient
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Alloc
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Served
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.OneMember
public import Proof.go_etcd_io.etcd.client.v3.KvOfNew
public import Proof.go_etcd_io.etcd.client.v3.InvServerKV
public import Perennial.Proof.sync.Results
public import Spec.context.ErrAny
public import Proof.go_etcd_io.etcd.client.v3.KMClient
public import Proof.go_etcd_io.etcd.client.v3.InvClientNewResult
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.watch.Served
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.NoDup

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_compactor

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.compactor.Assumptions]

/-- The API servers' loop's counters: one more round, one more `Add`. -/
theorem loop_step (n : w64) (k : w32)
    (hk : sint.Z k ≤ sint.Z n ∧ 0 ≤ sint.Z n ∧ sint.Z n ≤ 5 ∧ 0 ≤ sint.Z k)
    (h3 : sint.Z n < sint.Z (W64 5)) :
    sint.Z (k + W32 1) ≤ sint.Z (n + W64 1) ∧ 0 ≤ sint.Z (n + W64 1) ∧ sint.Z (n + W64 1) ≤ 5 ∧
      0 ≤ sint.Z (k + W32 1) := by
  obtain ⟨h1, h2, h4, h5⟩ := hk
  word

set_option maxHeartbeats 1600000 in
theorem Main.wp_proof
    (wp_NewNop : zap.NewNop.spec (GF := GF) (hG := hG))
    (wp_StartCompactingServer : etcdstart.StartCompactingServer.spec (GF := GF) (hG := hG))
    (wp_Serve : etcdstart.Serve.spec (GF := GF) (hG := hG))
    (wp_NewClient : etcdstart.NewClient.spec (GF := GF) (hG := hG))
    (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG))
    (wp_ready : ready.spec (GF := GF) (hG := hG))
    (wp_writer : writer.spec (GF := GF) (hG := hG))
    (wp_apiserver : apiserver.spec (GF := GF) (hG := hG)) :
    Main.spec (GF := GF) (hG := hG) := by
  intro CS CRE CEC N id ctxs boot Hbf Htb Hrb48 HrbN HwbN Hck Haf Hbuq Hrf Hdbo Hms hAs
  wp_start as ⟨Haddr, Htok, #Hprem, Hwdf, Hreg⟩
  iunfold etcdstart.premises at Hprem
  icases Hprem with ⟨#Hboot, #Hmarsh, #Hzap, #Hsetlg, #Htd, #Hns, #Hnrl⟩
  -- `Main`'s premises in the shared start's form
  ihave #Hb := etcdstart.bootPremise_of N [id] (LogEntry.toEntries boot 0) ctxs
      (etcdstart.dir1 peerAddr id) memberName memberName
      (etcdstart.urls1 memberName peerAddr clientAddr) id (etcdstart.cfgOk memberName memberName)
      (etcdstart.urls1 memberName peerAddr clientAddr) (fun _ h => h) (fun _ h => h) $$ Hboot
  ihave #Hcom : etcdstart.commonPremises (GF := GF) $$ []
  · iunfold etcdstart.commonPremises; iframe #
  -- `io.EOF` (the server's and the watch client's)
  ihave #Heof : v3rpc.eofVar (GF := GF) $$ []
  · iapply v3rpc.eofVar_of_init
    iPkgInit
  ihave #Heo : client.eofOk (GF := GF) $$ []
  · iapply (client.eofOk_of_init hAs)
    iPkgInit
  ihave #Hcci : context.isClosedchanInit (GF := GF) $$ []
  · iapply context.isClosedchanInit_of_init
    iPkgInit
  ihave #Pzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Psrv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver $$ []
  · iPkgInit
  ihave #Pv3 : isPkgInit (PROP := IProp GF)
      pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc $$ []
  · iPkgInit
  ihave #Pcli : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave #Psync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #Ppb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_NewNop as %lg %Hlg
  (try wp_auto)
  -- the ghost state `NewServer` takes, in compaction mode at retention `0`
  have hblen0 : boot.length = 1 := by rw [Hbf.boot.1]; rfl
  imod (etcdstart.alloc1_false id ctxs boot Hbf.idLow Hbf.boot Hbf.cc Hbf.urls (etcdstart.dir1 peerAddr id)
      (dirOne_member id _) (by omega) (by omega) (cmp := true) (cret := 0)) $$ Hmarsh
    with ⟨%γ, %ρ, %E₀, %Φs, %γn, %Hal, Hmb, #Hnet, Hetcd⟩
  obtain ⟨hvs, hrule, hboot, hγn1, hγn2, hlog, hkc, hkr⟩ := Hal
  have hblen : (LogEntry.toEntries boot 0).length ≤ 2 ^ 60 := by
    simp [LogEntry.toEntries, hblen0]
  have Hdirok : netDirOk (etcdstart.dir1 peerAddr id) :=
    dirOne_ok id _ (by intro h; apply Hbf.idLow; rw [h]; decide) (by decide)
  wp_apply (wp_StartCompactingServer N memberName peerAddr clientAddr (W64 0) lg
      (LogEntry.toEntries boot 0) ctxs (etcdstart.dir1 peerAddr id) id γ ρ E₀ Φs γn .none Htb Hrb48 HrbN
      HwbN hvs hrule hboot hblen hγn1 hγn2 Hdirok
      (by simp [etcdstart.dir1, dirOne]) (rafthttp.bootCfg_dirOne id _) (by decide) Hlg (by decide)
      (by rw [hkr]; decide) Hck Haf Hbuq Hdbo)
      $$ [Htok Hmb Hwdf]
    as %srv %err Hr
  · iframe; iframe #
  icases Hr with (⟨%Herr, -⟩ | ⟨%Herr, Hup⟩)
  · cases err with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    wp_auto
    iapply HΦ; itrivial
  subst Herr
  wp_auto
  iunfold etcdstart.memberUp at Hup
  icases Hup with ⟨%E, %cfg, %γw, %HEc, #Hreq, #Hrd, Hgo, Hlg3, Hrslots, #Hwb, #Hsf,
    Hbemu, Hlts, Hlgs, Hrds, Hsts, Hbms, -, HWR, -⟩
  obtain ⟨HEa, HEo, HElg, HEtr, HEw⟩ := HEc
  -- the example's invariant, at the member's start state (no key)
  have hboot0 : kvModelSt ρ.rd.kv (bootEntries (LogEntry.toEntries boot 0)) = kvStateOf [[], []] := by
    rw [kvModelSt_boot _ (fun _ _ => True) _ (LogEntry.toEntries boot 0)
      (srvBootLogOk_of_BootLog _ _ _ Hbf.boot),
      etcdstart.kvModel_boot _ _ _ (srvBootLogOk_of_BootLog _ _ _ Hbf.boot), hlog]
  rw [hboot0] at *
  imod (cinv_alloc ρ.rd.kv ⊤) $$ Hetcd with ⟨%γc, #Hinv⟩
  -- `Serve(s, clientAddr)`, with the ghost step `wk_served_nd` (the KV specs and the watch server's
  -- facts at the address; watches across a compaction: no revision writes a key twice, from the
  -- invariant, `noDupKeys_of_one`), the member refusal-free (D29) first
  haveI := Hms
  ihave ⟨%HsvOff, #HreqM, #HrdM, #Hlb⟩ := etcdstart.serveViews_off srv E { ρ with wait := γw } ρ.rd
    $$ []
  · iframe #
  wp_apply (wp_Serve srv clientAddr E { ρ with wait := γw } ρ.rd cfg
      (fun cid mid R => iprop(⌜R.E = E ∧ noRefusalAt clientAddr⌝ ∗
        client.kvRegsAt (⟨clientAddr, E, ρ.rd, cid, mid⟩ : client.SrvAt GF) ∗
        watchAddrFacts (EtcdGrove.client.srvWEnv R clientAddr [] null null go!"k" null ρ.rd.kv))))
    $$ [Haddr Hlg3 Hbemu Hgo HWR Hlts Hlgs Hrds Hsts Hrslots Hbms] as %serr Hs
  · iframe; iframe #
    isplitr
    · ipureintro; exact ⟨by rw [HElg]; exact Hlg, HEtr, HEw, Hms, Hbuq, HsvOff.2⟩
    iintro %gs %lis %cid %mid %R Hg
    rw [HsvOff.1]
    ihave Hg := etcdstart.grpcUpM_false _ _ _ _ _ _ _ _ _ _ $$ Hg
    iunfold etcdstart.grpcUp at Hg
    icases Hg with ⟨%C, %q, %p, %pw, %il, %im, %iu, %ims, %is, %svcs, %regs, %sregs, %HC,
      #Hgc, Hgsn, #Hq, #Hkvs, #Hws, #Hil, #Him, #Hiu, #Hims, #His, -, -, -, HWRs, Hlis, -⟩
    obtain ⟨HCA, HCE, Hregs1, Hregs2, hRs, hRE, hRw, hRγ⟩ := HC
    subst hRE
    icases replicate_take2 _ _ (by omega) $$ Hlts with ⟨-, -, Hlts⟩
    icases replicate_take2 _ _ (by omega) $$ Hrds with ⟨Hrd1, -, Hrds⟩
    ihave Hslots := client.etcdGrpcSlots_of_started srv R.E ρ.rd 1 (64 - 2) 64
        (Int.toNat sync.rwmutex.actualMaxReaders) 64 (by omega) (by omega)
        (by have := sync.actualMaxReaders_ge_2; omega) (by omega)
        $$ [Hlts Hlgs Hrds Hsts Hrslots Hbms]
    · iframe
    ihave Hwslots := client.watchRunSlots_of R 1 64 1 (by omega) (by omega) $$ [HWRs Hrd1]
    · rw [hRw, hRγ]
      iframe HWRs
      isplitl [Hrd1]
      · simp only [List.replicate]
        iapply BigSepL.bigSepL_cons.2
        iframe Hrd1
        iapply BigSepL.bigSepL_nil.2; itrivial
      ipureintro
      rw [sync.rwmutex.actualMaxReaders_unseal]
      omega
    ihave #Hinvs := srvKVInvs_of_read srv R.E ρ.rd $$ Hrd
    ihave #H00 := etcd_watch.cert0_of_server pw R $$ Hws
    ihave #Hkf : client.srvKVFacts (EtcdGrove.client.srvWEnv R clientAddr [] null null go!"k" null ρ.rd.kv) $$ []
    · iapply client.srvKVFacts_of_off _ ρ.rd (kvSame_refl _) hlog (by omega)
      iframe Hinvs
      iapply mvcc.idxCert_sealed; iexact H00
    -- the store's fact for watches: no revision writes a key twice (each has one change)
    ihave #HwnD : mvcc.watchNoDup R.E.γ $$ []
    · iunfold mvcc.watchNoDup; iright
      iapply (noDupKeys_of_one (EtcdGrove.client.srvWEnv R clientAddr [] null null go!"k" null ρ.rd.kv) ρ.rd.kv rfl)
      iframe Hkf
      iapply oneChangeAu $$ Hinv
    ihave #Hkva := client.kvServerAt_of_is p srv C.A cid mid C.n $$ Hkvs
    rw [HCA]
    ihave ⟨Hgsn, Hlis, %Hnr⟩ := (EtcdGrove.etcd_noRefusal clientAddr gs q p srv lis R.E
        { ρ with wait := γw } [il, im, iu] [ims, is] svcs regs sregs Hregs1 HEo) $$
      [Hgsn Hlis]
    · iframe Hgsn Hlis; iframe #
    imod (etcd_watch.wk_served_nd (EtcdGrove.client.srvWEnv R clientAddr [] null null go!"k" null ρ.rd.kv) clientAddr
        gs q p pw srv lis R.E { ρ with wait := γw } ρ.rd cid mid C.n il im iu ims is svcs regs sregs
        1 1 Hregs1 rfl rfl (by simp) rfl Hms.watch_impl Hregs2 rfl rfl Hrf)
      $$ [Hgsn Hlis Hslots Hwslots] with ⟨Hserv, #HKV, #HWF⟩
    · iframe; iframe #
      iintro !>
      imodintro
      iunfold idCred
      ipureintro; exact Hrb48
    imodintro
    iframe Hserv HKV HWF
    ipureintro; exact ⟨rfl, Hnr⟩
  icases Hs with (%Hserr | ⟨%Hserr, %cid, %mid, %R, ⟨%HRQ, #Hreg1, #HWF⟩⟩)
  · cases serr with
    | nil => exact absurd rfl Hserr
    | ok ei => ?_
    wp_auto
    iapply HΦ; itrivial
  subst Hserr
  obtain ⟨HRE, Hnr⟩ := HRQ
  wp_auto
  -- the one member: its registrations, its start, refusal-free
  let x : client.SrvAt GF := ⟨clientAddr, E, ρ.rd, cid, mid⟩
  imod (client.srvStart_alloc (GF := GF) [x]) with #Hst
  ihave #Hregs : ([∗list] y ∈ [x], client.kvRegsAt y) $$ []
  · iapply BigSepL.bigSepL_cons.2; iframe Hreg1; iapply BigSepL.bigSepL_nil.2; itrivial
  have hrb : receiptBound GF ≤ 2 ^ 62 := by omega
  have hsame : ∀ y ∈ [x], kvSame y.γr.kv ρ.rd.kv := fun y hy => by
    simp only [List.mem_singleton] at hy; subst hy; exact kvSame_refl _
  have htb : threadBound GF ≤ 2 ^ 31 := by omega
  let V : client.WEnv GF := EtcdGrove.client.srvWEnv R clientAddr [] null null go!"k" null ρ.rd.kv
  -- `wcli, err := NewClient(clientAddr, lg)`
  wp_apply (wp_NewClient clientAddr lg V Hlg (by unfold plainEndpoint; decide) htb)
    as %wcl %werr Hwc
  icases Hwc with (⟨%Hwerr, #Hwnc, -⟩ | %Hwfail)
  rotate_left
  · obtain ⟨Hwerr, -⟩ := Hwfail
    cases werr with
    | nil => exact absurd rfl Hwerr
    | ok ei => ?_
    wp_auto
    iapply HΦ; itrivial
  subst Hwerr
  wp_auto
  -- `ready(wcli)`
  wp_apply (wp_ready wcl [x] V) $$ [] as %b -
  · iframe #
    iExactEq Hwnc; rfl
  cases b
  · (try wp_auto)
    iapply HΦ; itrivial
  (try wp_auto)
  -- the cluster's KV invariant (the read-side law, `apiserver`'s)
  ihave #Hinvs := srvKVInvs_of_read srv E ρ.rd $$ Hrd
  iunfold srvKVInvs at Hinvs
  icases Hinvs with ⟨#Hkvi, -⟩
  -- a client of the member: refusal-free, its KV handle
  ihave #Hone1 : client.clientWriteOnce (GF := GF) wcl [clientAddr] $$ []
  · iunfold client.clientWriteOnce; ipureintro
    intro a ha; simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at ha
    subst ha; exact Hnr
  imod (client.isKv_of_newClient wcl [x] [clientAddr] V ρ.rd.kv rfl hsame hrb)
    $$ [Hwnc Hone1 Hregs] with ⟨%wapi, #Hwkvf, #Hwkv⟩
  · iframe #
  ihave #Hwko : k8s.clientKvOk (GF := GF) wcl ρ.rd.kv $$ []
  · iunfold k8s.clientKvOk; iexists wapi, false; iframe #
  -- `go writer(wcli)`
  wp_apply wp_fork $$ []
  · (try wp_auto)
    wp_apply (wp_writer wcl ρ.rd.kv γc) $$ []
    · iframe #
    (try wp_auto)
    (try itrivial)
  (try wp_auto)
  -- the wait group, in the join idiom
  imod (sync.init_WaitGroup (sync.join.wgjN.@"wg") wg_ptr) $$ wg with ⟨%γwg, #Hwg, Hctr, Hwaiters⟩
  imod (sync.join.init _ γwg) $$ [Hctr Hwaiters] with Hadd
  · iframe #; iframe
  -- the client address, claimed for the cluster (the API servers sharing the process's compactor)
  imod (k8s.epOf_alloc (∅ : GMap GoString GName) clientAddr ρ.rd.kv (fun _ => iprop(True)) rfl)
    $$ Hreg with ⟨%γa, -, #Hep⟩
  ihave #Heps : [∗list] ep ∈ [clientAddr], k8s.epOf (GF := GF) ep ρ.rd.kv (fun _ => iprop(True))
    $$ []
  · iapply BigSepL.bigSepL_singleton.2; iexact Hep
  ihave IH : (∃ (n : w64) (k : w32), "i" ∷ i_ptr ↦ n ∗
      "Hadd" ∷ sync.join.ownAdder wg_ptr k iprop(True) ∗
      "%Hk" ∷ ⌜sint.Z k ≤ sint.Z n ∧ 0 ≤ sint.Z n ∧ sint.Z n ≤ 5 ∧ 0 ≤ sint.Z k⌝ : IProp GF)
    $$ [i Hadd]
  · iexists _, (W32 0); iframe; ipureintro; decide
  wp_for IH
  wp_if_destruct
  · -- `cli, err := NewClient(clientAddr, lg)`
    wp_apply (wp_NewClient clientAddr lg V Hlg (by unfold plainEndpoint; decide) htb)
      as %cl %cerr Hc
    icases Hc with (⟨%Hcerr, #Hnc, -⟩ | %Hcfail)
    rotate_left
    · obtain ⟨Hcerr, -⟩ := Hcfail
      cases cerr with
      | nil => exact absurd rfl Hcerr
      | ok ei => ?_
      (try wp_auto)
      wp_for_post
      (try wp_auto)
      wp_apply (sync.join.WaitGroup.wp_Wait iprop(True) k wg_ptr) $$ [Hadd] as -
      · iframe #; iframe
      (try wp_auto)
      iapply HΦ; itrivial
    subst Hcerr
    (try wp_auto)
    ihave #Hone2 : client.clientWriteOnce (GF := GF) cl [clientAddr] $$ []
    · iunfold client.clientWriteOnce; ipureintro
      intro a ha; simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at ha
      subst ha; exact Hnr
    imod (client.isKv_of_newClient cl [x] [clientAddr] V ρ.rd.kv rfl hsame hrb)
      $$ [Hnc Hone2 Hregs] with ⟨%capi, #Hckvf, #Hckv⟩
    · iframe #
    ihave #Hcko : k8s.clientKvOk (GF := GF) cl ρ.rd.kv $$ []
    · iunfold k8s.clientKvOk; iexists capi, false; iframe #
    -- its watcher handle, with the watch server's facts (D19f)
    ihave ⟨%w, %conn, %wc, %lgw, %ics, #HWf, #Hcw⟩ := EtcdGrove.isNewClient_watcher wp_ErrAny hAs cl
      [clientAddr] V rfl rfl rfl $$ [Pcli Ppb Pctx Hnc HWF]
    · iframe #
    ihave #Hcwo : k8s.clientWatchOk (GF := GF) cl ρ.rd.kv $$ []
    · iunfold k8s.clientWatchOk; iexists w, _; iframe #; ipureintro; rfl
    -- `wg.Add(1)`
    wp_apply (sync.join.WaitGroup.wp_Add iprop(True) wg_ptr iprop(True) k) $$ [Hadd]
      as ⟨Hadd, Hdone⟩
    · iframe #; iframe
      ipureintro; omega
    ihave Hadd := sync.join.ownAdder_wand iprop(True) _ _ _ $$ [] Hadd
    · iintro _; itrivial
    (try wp_auto)
    -- `go func() { apiserver(cli, shared); wg.Done() }()`
    wp_apply wp_fork $$ [Hdone cli shared]
    · (try wp_auto)
      wp_apply (wp_apiserver cl [x] V ρ.rd.raft ρ.rd.kv γc _ hsame hkc hkr) $$ []
      · iframe #
        rw [show List.map client.SrvAt.addr [x] = [clientAddr] from rfl]
        iframe #
      (try wp_auto)
      wp_apply sync.join.WaitGroup.wp_Done iprop(True) _ $$ [Hdone]
      · iframe #; iframe
      (try wp_auto)
      (try itrivial)
    (try wp_auto)
    wp_for_post
    iframe
    iexists _, (k + W32 1)
    iframe
    ipureintro
    exact loop_step n k Hk Hif
  · (try wp_auto)
    wp_apply (sync.join.WaitGroup.wp_Wait iprop(True) k wg_ptr) $$ [Hadd] as -
    · iframe #; iframe
    (try wp_auto)
    iapply HΦ; itrivial

end proof

end k8s_compactor
end EtcdGrove
end Perennial
