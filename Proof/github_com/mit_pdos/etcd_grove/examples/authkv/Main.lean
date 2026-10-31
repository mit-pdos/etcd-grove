/-
`Main()` (`examples/authkv/authkv.go`; the auth plan's E2b): **proved** (2026-10-31), over its
callees' specs. Lean-first (no Rocq counterpart).

The steps: the logger; the member's ghost state with auth on (`ak_alloc`) and the history invariant
(`akHist_alloc`); `startServer` (`memberUpOn`); `Serve` with auth on (`Serve.specOn`) with the
ghost steps `ak_served_kv` and `ak_served_watch` (`MainServe.lean`: the KV methods with auth on,
the Auth service's admin methods and `Authenticate`; the watch server's facts at the clients'
watcher environment `akV R`); `NewClient` (no user name, no token); `SetUp` (its puts under the
history invariant, `akHist_setupAu`; the TLS fallback off and the auth store's cost from
`memberUpOn`); the user clients (`newUserClient` for root, u and v, over the registration of
`Authenticate`: `authTokReg_of`); the workloads: the auth state fixed after the set-up
(`akAuthFixed_alloc` from `SetUp`'s post), the principals' loop (`c` the client of `u`, of `v`, or
the set-up's, its tokens `akTokP`), each `Work(c, who)` in a goroutine under a wait group, and
`wg.Wait()`; root's last write in a timeout context (`client_Put_on`), admitted by the history from
any state (`akHist_endAu`), its reply's revision `Collect`'s bound; root's watch of every key from
revision 1 (`watcher.Watch` with the history's read update `akHist_readAu`, no auth bound), its
`Collect` at the per-event fact `rootEvOk` (`root_resp`, `RootWatch.lean`) and `CheckHistory`
(`histOk_of_collected`); u's watch of `[a, b)` from revision 1 up to `LastIn` of root's events, its
`Collect` at `permittedK u` of each key (`u_resp`: the watch's events are of its range, the range u
may read; no auth fact is needed, a refused watch having no events), and the loop of `Permitted`
checks, which never panics; every error's return of `Failed`, a watch that ends early
`WatchEnded`.

What the result still rests on (`etc/tcb-collections/authkv.txt`): `startServer`, linked as pending
(`Results.lean`'s `authkv_Main` takes its premises); `Work`'s nested-transaction part
(`then_commit_nested_refused`, T4); and the server's apply thread and raft node loop.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.authkv.Main
public import Spec.github_com.mit_pdos.etcd_grove.examples.authkv.SetUp
public import Spec.github_com.mit_pdos.etcd_grove.examples.authkv.newUserClient
public import Spec.github_com.mit_pdos.etcd_grove.examples.authkv.Work
public import Spec.github_com.mit_pdos.etcd_grove.examples.authkv.Principals
public import Spec.github_com.mit_pdos.etcd_grove.examples.authkv.CheckHistory
public import Spec.github_com.mit_pdos.etcd_grove.examples.authkv.LastIn
public import Spec.github_com.mit_pdos.etcd_grove.examples.authkv.startServer
public import Spec.github_com.mit_pdos.etcd_grove.examples.common.Serve
public import Spec.github_com.mit_pdos.etcd_grove.examples.common.NewClient
public import Spec.go_uber_org.zap.NewNop
public import Spec.context.ErrAny
public import Proof.go_etcd_io.etcd.client.v3.ErrorsNewOk
public import Proof.github_com.mit_pdos.etcd_grove.examples.authkv.WorkEnv
public import Perennial.Proof.sync.WaitGroupJoin
public import Perennial.Proof.sync.Link
public import Proof.github_com.mit_pdos.etcd_grove.examples.authkv.MainAlloc
public import Proof.github_com.mit_pdos.etcd_grove.examples.authkv.MainServe
public import Proof.github_com.mit_pdos.etcd_grove.examples.authkv.Hist
public import Proof.go_etcd_io.etcd.client.v3.ServeFromStart
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo
public import Proof.go_etcd_io.etcd.client.v3.TimeoutCtx
public import Proof.github_com.mit_pdos.etcd_grove.examples.authkv.ClientOn
public import Spec.context.WithTimeoutBackground
public import Spec.github_com.mit_pdos.etcd_grove.examples.common.Collect
public import Spec.go_etcd_io.etcd.client.v3.watcher__Watch
public import Spec.go_etcd_io.etcd.client.v3.WithPrefix
public import Spec.go_etcd_io.etcd.client.v3.WithRev
public import Spec.go_etcd_io.etcd.client.v3.WithRange
public import Spec.github_com.mit_pdos.etcd_grove.examples.authkv.Permitted
public import Proof.github_com.mit_pdos.etcd_grove.examples.authkv.RootWatch
public import Proof.github_com.mit_pdos.etcd_grove.examples.authkv.WorkCalls

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authkv

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.authkv.Assumptions]

set_option maxHeartbeats 1600000 in
theorem Main.wp_proof
    (wp_NewNop : zap.NewNop.spec (GF := GF) (hG := hG))
    (wp_startServer : startServer.spec (GF := GF) (hG := hG))
    (wp_ServeOn : common.Serve.specOn (GF := GF) (hG := hG))
    (wp_NewClient : common.NewClient.spec (GF := GF) (hG := hG))
    (wp_BcryptCost : auth.authStore.BcryptCost.spec (GF := GF) (hG := hG))
    (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG))
    (wp_SetUp : SetUp.spec (GF := GF) (hG := hG))
    (wp_newUserClient : newUserClient.spec (GF := GF) (hG := hG))
    (wp_Work : Work.spec (GF := GF) (hG := hG))
    (wp_Principals : Principals.spec (GF := GF) (hG := hG))
    (wp_CheckHistory : CheckHistory.spec (GF := GF) (hG := hG))
    (wp_LastIn : LastIn.spec (GF := GF) (hG := hG))
    (wp_WithTimeout : context.WithTimeoutBackground.spec (GF := GF) (hG := hG))
    (wp_Collect : common.Collect.spec (GF := GF) (hG := hG))
    (wp_Watch : watcher.Watch.spec (GF := GF) (hG := hG))
    (wp_WithPrefix : WithPrefix.spec (GF := GF) (hG := hG))
    (wp_WithRev : WithRev.spec (GF := GF) (hG := hG))
    (wp_WithRange : WithRange.spec (GF := GF) (hG := hG))
    (wp_Permitted : Permitted.spec (GF := GF) (hG := hG)) :
    Main.spec (GF := GF) (hG := hG) := by
  intro CS ES FS RS CRE CEC N id ctxs boot Hbf Htb Hrb48 HrbN Hck Haf Hbuq Hdbo Hms hAs
  have Htb31 : threadBound GF ≤ 2 ^ 31 := by omega
  wp_start as ⟨Haddr, Htok, #Hprem⟩
  iunfold premises at Hprem
  icases Hprem with ⟨#Hboot, #Hmarsh, #Hzap, #Hsetlg, #Htd, #Hns, #Htk, #Hnrl⟩
  ihave #Hcci : context.isClosedchanInit (GF := GF) $$ []
  · iapply context.isClosedchanInit_of_init
    iPkgInit
  ihave #Psrv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver $$ []
  · iPkgInit
  ihave #Pv3 : isPkgInit (PROP := IProp GF)
      pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc $$ []
  · iPkgInit
  ihave #Ppb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
  · iPkgInit
  -- `io.EOF` (the watch client's), from its package's fact
  ihave #Heo : client.eofOk (GF := GF) $$ []
  · iapply (client.eofOk_of_init hAs)
    iPkgInit
  (try wp_auto)
  wp_apply wp_NewNop as %lg %Hlg
  (try wp_auto)
  -- the member's ghost state with auth on, the client's half of the KV state, its view of the
  -- auth history (`ak_alloc`), and the history invariant over the former (`akHist_alloc`)
  have hblen0 : boot.length = 1 := by rw [Hbf.boot.1]; rfl
  imod (ak_alloc id ctxs boot Hbf.idLow Hbf.boot Hbf.cc (by omega) (by omega)) $$ Hmarsh
    with ⟨%γ, %ρ, %E₀, %Φs, %γn, %σ₀, %Hal, Hmb, #Hnet, Hetcd, Hview⟩
  obtain ⟨hvs, hrule, hboot, hγn1, hγn2, hσ₀, hc0, hlog⟩ := Hal
  ihave ⟨%Hcmp0, Hmb⟩ := common.memberBootOn_cmp γ ctxs ρ E₀ Φs id false $$ Hmb
  imod (akHist_alloc ρ.rd.kv σ₀ hσ₀) $$ Hetcd with #Hhist
  have hblen : (LogEntry.toEntries boot 0).length ≤ 2 ^ 60 := by
    simp [LogEntry.toEntries, hblen0]
  ihave #Hcom : common.commonPremises (GF := GF) $$ []
  · iunfold common.commonPremises; iframe #
  have Hdirok : netDirOk (akDir id) :=
    dirOne_ok id _ (by intro h; apply Hbf.idLow; rw [h]; decide) (by decide)
  -- `startServer(lg)`: the member with auth on
  wp_apply (wp_startServer N lg (LogEntry.toEntries boot 0) ctxs (akDir id) id γ ρ E₀ Φs γn Htb31
      Hrb48 HrbN hvs hrule hboot hblen hγn1 hγn2 Hdirok (by simp [akDir, dirOne]) Hlg Hck Haf
      Hbuq Hdbo)
    $$ [Htok Hmb] as %srv %err Hr
  · iframe; iframe #
  icases Hr with (⟨%Herr, -⟩ | ⟨%Herr, %γa, Hup⟩)
  · cases err with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ipureintro; right; left; rfl
  subst Herr
  wp_auto
  iunfold common.memberUpOn at Hup
  icases Hup with ⟨%E, %cfg, %γw, %HE, #Hreq, #Hrd, #Hlb, Hgo, Hlg3, Hrslots, #Hwb, #Hsf, Hwpi,
    Hbemu, Hlts, Hlgs, Hrds, Hsts, Hbms, -, HWR, #Htls, #HBF⟩
  obtain ⟨HEa, HEo, HElg, HEtr, HEw⟩ := HE
  have Hoff : E.γ.cm = false := envAgree_off E E₀ HEa Hcmp0
  -- `Serve(s, clientAddr)`, with the ghost steps `ak_served_kv` (the KV methods with auth on, the
  -- Auth service's admin methods and `Authenticate` at the address) and `ak_served_watch` (the
  -- watch server's facts there, for the clients' watcher environment `akV R`)
  haveI := Hms
  let akV : v3rpc.WSrv GF → client.WEnv GF := fun R =>
    client.srvWEnv R go!"127.0.0.1:23916" [] null null go!"a" null ρ.rd.kv.st
  wp_apply (wp_ServeOn srv go!"127.0.0.1:23916" E { ρ with wait := γw } ρ.rd cfg γa
      (fun cid mid R => iprop(⌜R.E = E ∧ R.s = srv⌝ ∗
        akKVOn go!"127.0.0.1:23916" srv E { ρ with wait := γw } cid mid ∗
        setupAuthServed go!"127.0.0.1:23916" srv E { ρ with wait := γw } ∗
        isGrpcRpc go!"127.0.0.1:23916" authnMethod (client.etcdAuthenticateSpec γa) ∗
        watchAddrFacts (akV R) ∗ auth.modeTag R.γ.tag E.authMode))
      HEo (by rw [HElg]; exact Hlg) HEtr HEw Hms Hbuq)
    $$ [Haddr Hlg3 Hbemu Hgo Hwpi HWR Hlts Hlgs Hrds Hsts Hrslots Hbms] as %serr Hs
  · iframe; iframe #
    iintro %gs %lis %cid %mid %R Hg
    iunfold common.grpcUpOn at Hg
    icases Hg with ⟨%C, %q, %p, %pw, %pa, %il, %im, %iu, %ims, %is, %svcs, %regs, %sregs, %d',
      %HC, #Hgc, Hgsn, #Hq, #Hkvs, #Hpa, #Hws, #Hil, #Him, #Hiu, #Hims, #His, -, -, -, -, HWRs,
      Hlis⟩
    obtain ⟨HCA, HCE, Hregs1, HregsA, Hregs2, hRs, hRE, hRw, hRγ⟩ := HC
    icases replicate_take2 _ _ (by omega) $$ Hlts with ⟨-, -, Hlts⟩
    icases replicate_take2 _ _ (by omega) $$ Hrds with ⟨Hrd1, -, Hrds⟩
    ihave Hslots := client.etcdGrpcSlots_of_started srv E ρ.rd 1 (64 - 2) 64
        (Int.toNat sync.rwmutex.actualMaxReaders) 64 (by omega) (by omega)
        (by have := sync.actualMaxReaders_ge_2; omega) (by omega)
        $$ [Hlts Hlgs Hrds Hsts Hrslots Hbms]
    · iframe
    -- one watch run slot: two of the watchable store's readers, one of the request path's (the
    -- runs share a pool, `grpc.serveStream`)
    ihave Hwslots := client.watchRunSlots_of R 1 64 1 (by omega) (by omega) $$ [HWRs Hrd1]
    · rw [hRw, hRγ, hRE]
      iframe HWRs
      isplitl [Hrd1]
      · simp only [List.replicate]
        iapply BigSepL.bigSepL_cons.2
        iframe Hrd1
        iapply BigSepL.bigSepL_nil.2; itrivial
      ipureintro
      rw [sync.rwmutex.actualMaxReaders_unseal]
      omega
    ihave #Hkva := client.kvServerAt_of_is p srv C.A cid mid C.n $$ Hkvs
    rw [HCA]
    imod (ak_served_kv go!"127.0.0.1:23916" gs q p pa srv lis E { ρ with wait := γw } cid mid C.n
        il im iu ims is svcs regs sregs 1 γa HEo Hregs1 HregsA wp_BcryptCost)
      $$ [Hgsn Hlis Hslots] with ⟨Hserv, Hss, #HKV, #HSA, #HAu⟩
    · iframe; iframe #
      iintro !>
      imodintro
      iunfold idCred
      ipureintro; exact Hrb48
    imod (ak_served_watch (akV R) go!"127.0.0.1:23916" pw srv E ρ.rd ims is sregs 1 rfl hRE
        (by simp) rfl hlog (by omega) Hms.watch_impl Hregs2 rfl rfl (by rw [hRE]; exact Hoff))
      $$ [Hss Hwslots] with ⟨#HWF, #Htag⟩
    · iframe; iframe #
    imodintro
    iframe Hserv HKV HSA HAu HWF Htag
    ipureintro; exact ⟨hRE, hRs⟩
  icases Hs with (%Hserr | ⟨%Hserr, %cid, %mid, %R, ⟨%HRQ, #HKV, #HSA, #HAu, #HWF, #Htag⟩⟩)
  · cases serr with
    | nil => exact absurd rfl Hserr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ipureintro; right; left; rfl
  subst Hserr
  wp_auto
  -- `NewClient(clientAddr, lg)`: the client with no user name
  wp_apply (wp_NewClient go!"127.0.0.1:23916" lg
      (akV R) Hlg
      (by unfold plainEndpoint; decide) Htb31) as %cl %cerr Hcl
  icases Hcl with (⟨%Hcerr, #Hnc, #Hctk⟩ | %Hcfail)
  rotate_left
  · obtain ⟨Hcerr, -⟩ := Hcfail
    cases cerr with
    | nil => exact absurd rfl Hcerr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ipureintro; right; left; rfl
  subst Hcerr
  wp_auto
  -- `SetUp(cli)`: the set-up's puts under the history invariant (`akHist_setupAu`)
  ihave #Hsau : iprop(□ ∀ k : GoString, ⌜k ∈ setupKeys⌝ -∗
      kvOpAu1 ρ.rd.kv (.put (client.putKeyOp k go!"setup")) (fun _ => iprop(True))) $$ []
  · iintro !> %k %hk
    ihave #H := akHist_setupAu ρ.rd.kv k hk $$ Hhist
    iexact H
  ihave #Hput : isGrpcRpcMd go!"127.0.0.1:23916" go!"/etcdserverpb.KV/Put"
      (client.etcdPutSpecOn srv E { ρ with wait := γw } cid mid) $$ []
  · iunfold akKVOn at HKV
    icases HKV with ⟨#H, -, -, -⟩
    iexact H
  wp_apply (wp_SetUp cl go!"127.0.0.1:23916"
      (akV R) srv E
      { ρ with wait := γw } cid mid γa HEo
      (by show uint.Z ρ.rd.kv.c0 ≤ uint.Z ρ.rd.raft.ai0; rw [hc0]; word) hAs)
    $$ [Hview] as %ok Hok
  · iframe; iframe #
  cases ok
  · wp_auto
    iapply HΦ; ipureintro; right; left; rfl
  -- `newUserClient` for root, u and v: clients that authenticate as their user at the member's
  -- `Authenticate` (`authTokReg_of`), sending the tokens issued to it
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #Hall : client.ctxErrClientAll (GF := GF) $$ []
  · ihave #Hw := client.ctxErrClientAllW_of wp_ErrAny hAs $$ Pctx
    iunfold client.ctxErrClientAllW at Hw
    iunfold client.ctxErrClientAll
    iexact Hw
  wp_auto
  wp_apply (wp_newUserClient go!"root" go!"root-pw" lg (akV R) (fun t => auth.tokIssued γa t go!"root")
      Hlg (by omega) (by unfold strsSizeOk; decide)) as %rcl %rerr Hrc
  · iframe #
    iapply (client.authTokReg_of _ _ _ γa)
    iexact HAu
  icases Hrc with (⟨%Hrerr, #Hrnc, #Hrtk⟩ | %Hrfail)
  rotate_left
  · obtain ⟨Hrerr, -⟩ := Hrfail
    cases rerr with
    | nil => exact absurd rfl Hrerr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ipureintro; right; left; rfl
  subst Hrerr
  wp_auto
  wp_apply (wp_newUserClient go!"u" go!"u-pw" lg (akV R) (fun t => auth.tokIssued γa t go!"u") Hlg
      (by omega) (by unfold strsSizeOk; decide)) as %ucl %uerr Huc
  · iframe #
    iapply (client.authTokReg_of _ _ _ γa)
    iexact HAu
  icases Huc with (⟨%Huerr, #Hunc, #Hutk⟩ | %Hufail)
  rotate_left
  · obtain ⟨Huerr, -⟩ := Hufail
    cases uerr with
    | nil => exact absurd rfl Huerr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ipureintro; right; left; rfl
  subst Huerr
  wp_auto
  wp_apply (wp_newUserClient go!"v" go!"v-pw" lg (akV R) (fun t => auth.tokIssued γa t go!"v") Hlg
      (by omega) (by unfold strsSizeOk; decide)) as %vcl %verr Hvc
  · iframe #
    iapply (client.authTokReg_of _ _ _ γa)
    iexact HAu
  icases Hvc with (⟨%Hverr, #Hvnc, #Hvtk⟩ | %Hvfail)
  rotate_left
  · obtain ⟨Hverr, -⟩ := Hvfail
    cases verr with
    | nil => exact absurd rfl Hverr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ipureintro; right; left; rfl
  subst Hverr
  wp_auto
  -- the auth state fixed after the set-up (S6, `akAuthFixed_alloc`), from `SetUp`'s post
  rw [ite_eq_left rfl]
  icases Hok with ⟨%γz, %hs, %Lset, %kpub, %rset, #Hfz, #Hllb, %Hadm, #Hpub, #Hsst⟩
  ihave #Hfix := akAuthFixed_alloc srv E γa { ρ with wait := γw } γz hs Lset kpub rset HEo
    $$ [Hrd Hfz Hllb Hpub Hsst]
  · iframe #; ipureintro; exact Hadm
  -- the workloads: `for _, who := range Principals() { ...; wg.Add(1); go func() { Work(c, who);
  -- wg.Done() }() }`, then `wg.Wait()`
  wp_apply wp_Principals as %psl Hpsl
  imod ownSlice_persist _ _ _ $$ Hpsl with #Hpsl
  (try wp_auto)
  ihave %Hpl := ownSlice_len $$ Hpsl
  ipersist cli
  ipersist ucli
  ipersist vcli
  imod sync.init_WaitGroup (sync.join.wgjN.@"wg") wg_ptr $$ wg with ⟨%γwg, Hwg⟩
  imod sync.join.init wg_ptr γwg $$ Hwg with Hwg
  ihave IH : (∃ (k : w64) (na : w32),
      "i" ∷ i_ptr ↦ k ∗ "Hwg" ∷ sync.join.ownAdder wg_ptr na iprop(True) ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ 4 ∧ sint.Z na = sint.Z k⌝ : IProp GF)
    $$ [i Hwg]
  · iexists W64 0, W32 0
    iframe
    ipureintro
    exact ⟨by decide, by decide, by decide⟩
  -- `Work`'s facts shared by every principal
  obtain ⟨hRE', hRs'⟩ := HRQ
  ihave #Htag' : auth.modeTag R.γ.tag (.on γa) $$ []
  · rw [← HEo]; iexact Htag
  have hplen : sint.Z psl.len = 4 := by
    have h := Hpl.1; simp only [principals, List.length] at h; word
  wp_for IH
  wp_if_destruct
  · -- the principal `who := principals[k]`
    have Hlt : sint.nat k < principals.length := by simp only [principals, List.length]; word
    obtain ⟨who, Hl⟩ : ∃ w, principals[sint.nat k]? = some w :=
      ⟨_, List.getElem?_eq_getElem Hlt⟩
    have hwho : who ∈ principals := List.mem_of_getElem? Hl
    have Hbnd : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z psl.len := ⟨Hk.1, by word⟩
    rw [ite_eq_left Hbnd]
    icases ownSlice_elem_acc (sint.Z k) who psl DFrac.discard principals Hk.1 Hl $$ Hpsl
      with ⟨#Hle, -⟩
    (try wp_auto)
    -- `c` is `ucli` for u, `vcli` for v, `cli` (no user name) for anon and bad
    wp_if_destruct
    rotate_left
    wp_if_destruct
    all_goals
      (try wp_auto)
      wp_apply (sync.join.WaitGroup.wp_Add_of sync.WaitGroup.wp_Add iprop(True) wg_ptr iprop(True)
          na) $$ [Hwg] as ⟨Hwg, Hdone⟩
      · iframe; ipureintro; word
      wp_apply wp_fork $$ [Hdone who c]
      · (try wp_auto)
        wp_apply (wp_Work _ _ (akV R) srv E { ρ with wait := γw } cid mid γa Lset kpub hwho HEo
            ⟨rfl, rfl, rfl, hRs', hRE', rfl⟩ hAs)
        · iframe #
          first
          | (rw [akTokP, ite_eq_left (Or.inl rfl)]; iexact Hutk)
          | (rw [akTokP, ite_eq_left (Or.inr rfl)]; iexact Hvtk)
          | (rw [akTokP, ite_eq_right (fun h => h.elim ‹_› ‹_›)]; iexact Hctk)
        (try wp_auto)
        wp_apply (sync.join.WaitGroup.wp_Done_of sync.WaitGroup.wp_Done iprop(True) wg_ptr)
          $$ [Hdone]
        · iframe
        itrivial
      wp_for_post
      iframe
      iexists (k + W64 1), (na + W32 1)
      iframe
      isplitl [Hwg]
      · iapply sync.join.ownAdder_wand $$ [] Hwg
        iintro -; itrivial
      ipureintro
      refine ⟨by word, by word, by word⟩
  -- the workloads are done: `wg.Wait()`
  wp_apply (sync.join.WaitGroup.wp_Wait_of sync.WaitGroup.wp_Wait _ na wg_ptr) $$ [$Hwg] as -
  (try wp_auto)
  -- root's last write, `root.Put(ctx, "z/end", "end")` in a timeout context: admitted by the
  -- history from any state (`akHist_endAu`)
  ihave #Hend := akHist_endAu ρ.rd.kv go!"end" $$ Hhist
  imod mvcc.idxCert_nil (GF := GF) E.γ.idx with #HF0
  ihave #Hnil := optsAt_nil (GF := GF)
  ihave #Hrtk0 := Hrtk
  iunfold clientTokAt at Hrtk0
  icases Hrtk0 with ⟨%rapi, %rconn, #Hrkvf, #Hrobj, -, -, -⟩
  wp_apply context.wp_Background
  (try wp_auto)
  wp_apply (client.wp_WithTimeout_bg wp_WithTimeout wp_ErrAny hAs _)
    as %ectx %ecd %ecancel ⟨#Hecancel, #Hectx, #Hece, -⟩
  (try wp_auto)
  wp_apply (client_Put_on rcl rapi rconn go!"127.0.0.1:23916" srv E { ρ with wait := γw } cid mid
      ectx ecd endKey go!"end" slice.nil (fun _ => iprop(True)) []
      (opSizeOk_opPutModel (K := 2 ^ 28) (E := 0) (V := 2 ^ 28) (optsKeep_nil _ _ _) (by decide)
        (by decide) (by decide))) $$ [] as %eresp %eerr Hend'
  · iframe #
  (try wp_auto)
  wp_apply Hecancel
  icases Hend' with (⟨%Heerr, %em, Hemsg, Herep, -⟩ | ⟨%Heerr, -⟩)
  rotate_left
  · cases eerr with
    | nil => exact absurd rfl Heerr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ipureintro; right; left; rfl
  subst Heerr
  (try wp_auto)
  -- root's watch of every key from revision 1 (`hctx, hcancel := context.WithCancel(...)`;
  -- `root.Watcher.Watch(hctx, "", WithPrefix(), WithRev(1))`), with the history's read update
  -- (`akHist_readAu`), no auth bound (`n = 0`): its responses are reads of states the invariant
  -- holds at
  wp_apply context.wp_Background
  wp_apply context.wp_WithCancel_Background iprop(True) $$ [$Pctx $Hcci]
    as %hctx %γhctx %hcancel ⟨#Hhcancel, #Hhctx, -⟩
  (try wp_auto)
  wp_apply wp_WithPrefix as %f1 #Hf1
  wp_apply wp_WithRev (W64 1) as %f2 #Hf2
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %hosl ⟨Hhosl, -⟩
  ipersist Hhosl
  ihave #Hhopts := optsAt_two (GF := GF) _
      ([f1, zero_val GoFunc].set (sint.nat (W64 (0 + 1))) f2) f1 f2 withPrefixM (withRevM (W64 1))
      rfl $$ [Hhosl Hf1 Hf2]
  · iframe #
  ihave #Pcl : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave ⟨%rw, %rwconn, %rwwc, %rwlg, %rwics, #Hrwf, #Hrcw, -⟩ :=
    client.watcher_of_clientTokAt wp_ErrAny hAs rcl _ (akV R)
      (fun t => auth.tokIssued γa t go!"root") rfl rfl rfl $$ [Pcl Pctx Ppb Hrnc HWF Hrtk]
  · iframe #
  (try wp_auto)
  ihave #Hrau := akHist_readAu ρ.rd.kv $$ Hhist
  iunfold kvReadAu at Hrau
  iunfold kvAu at Hrau
  wp_apply (wp_Watch rw { akV R with conn := rwconn, ics := rwics, wc := rwwc, lg := rwlg } ρ.rd.kv
      hctx ({ Values := ∅, Deadline := none, Done_gn := γhctx, PDone := iprop(True) } :
        context.ContextDesc (IProp GF))
      _ _ [withPrefixM, withRevM (W64 1)] (W64 1) (fun σ => iprop(⌜stateHistOk σ⌝)) 0) $$ []
    as %hch %γh ⟨#Hhsp, Hhcons, Hhcur⟩
  · iframe #
    isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro; exact ⟨watch_all_ok.1, watch_all_ok.2, by decide⟩
    iintro !> %h
    exact absurd h.2 (Nat.lt_irrefl 0)
  ihave #Hhch := common.isRespChan_of_state hch γh _ (fun σ => iprop(⌜stateHistOk σ⌝)) _ $$ Hhsp
  (try wp_auto)
  -- `evs, ok := common.Collect(hch, end.Header.Revision)`: every event admitted (`root_resp`)
  iunfold putRespMsg at Hemsg
  icases Hemsg with ⟨%Hnn, %eh, %epk, #Hehd, #Hehf, -⟩
  iunfold hdrFull at Hehf
  icases Hehf with ⟨%Hhn, -, -, #Herevf, -, -⟩
  (try wp_auto)
  have h10 : (W64 1 - W64 1 : w64) = W64 0 := by decide
  ihave Hhcons : etcdWatchConsumer γh 0 (W64 0) $$ [Hhcons Hhcur]
  · unfold etcdWatchConsumer
    iexists []
    rw [← h10]
    iframe Hhcons Hhcur
    ipureintro; rfl
  wp_apply (wp_Collect (common.stateOk _ (fun σ => iprop(⌜stateHistOk σ⌝))) (fun _ _ => True)
      (fun _ e => iprop(⌜rootEvOk e⌝)) iprop(True) hch γh _ trivial (fun _ _ _ _ => inferInstance)
      (fun c c' v r => common.stateOk_closeErr _ _ c c' v r)
      (fun n c c' v r hne hI => root_resp _ n c c' v r hne hI))
    $$ [Hhcons] as %esl %eok Hcol
  · iframe; iframe #
    iintro !>; itrivial
  (try wp_auto)
  wp_apply Hhcancel $$ [] as -
  · itrivial
  (try wp_auto)
  cases eok
  · -- the watch ended before root's last write
    (try wp_auto)
    iapply HΦ; ipureintro; right; right; rfl
  ihave ⟨%evs, Hes, -, #Hevs⟩ := Hcol $$ %rfl
  ihave %Hhist' := histOk_of_collected evs $$ Hevs
  (try wp_auto)
  -- `CheckHistory(evs, "z/end")`
  wp_apply (wp_CheckHistory esl evs (DFrac.own 1) endKey Hhist') $$ [Hes] as Hes
  · iframe; try iframe #
  (try wp_auto)
  -- u's watch of `[lo, hi)` from revision 1 (`uctx, ucancel := context.WithCancel(...)`;
  -- `ucli.Watcher.Watch(uctx, lo, WithRange(hi), WithRev(1))`): its events are of `[a, b)`, the
  -- range u may read (`u_resp`)
  wp_apply context.wp_Background
  wp_apply context.wp_WithCancel_Background iprop(True) $$ [$Pctx $Hcci]
    as %uctx %γuctx %ucancel ⟨#Hucancel, #Huctx, -⟩
  (try wp_auto)
  wp_apply wp_WithRange hi as %g1 #Hg1
  wp_apply wp_WithRev (W64 1) as %g2 #Hg2
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %uosl ⟨Huosl, -⟩
  ipersist Huosl
  ihave #Huopts := optsAt_two (GF := GF) _
      ([g1, zero_val GoFunc].set (sint.nat (W64 (0 + 1))) g2) g1 g2 (withRangeM hi) (withRevM (W64 1))
      rfl $$ [Huosl Hg1 Hg2]
  · iframe #
  ihave ⟨%uw, %uwconn, %uwwc, %uwlg, %uwics, #Huwf, #Hucw, -⟩ :=
    client.watcher_of_clientTokAt wp_ErrAny hAs ucl _ (akV R)
      (fun t => auth.tokIssued γa t go!"u") rfl rfl rfl $$ [Pcl Pctx Ppb Hunc HWF Hutk]
  · iframe #
  (try wp_auto)
  wp_apply (wp_Watch uw { akV R with conn := uwconn, ics := uwics, wc := uwwc, lg := uwlg }
      ρ.rd.kv uctx ({ Values := ∅, Deadline := none, Done_gn := γuctx, PDone := iprop(True) } :
        context.ContextDesc (IProp GF))
      _ _ [withRangeM hi, withRevM (W64 1)] (W64 1) (fun σ => iprop(⌜stateHistOk σ⌝)) 0) $$ []
    as %uch %γu ⟨#Husp, Hucons, Hucur⟩
  · iframe #
    isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro; exact ⟨watch_ab_ok.1.1, watch_ab_ok.1.2, by decide⟩
    iintro !> %h
    exact absurd h.2 (Nat.lt_irrefl 0)
  rw [OpFull.watchNorm_of_ne (opWatchModel lo [withRangeM hi, withRevM (W64 1)])
    (by rw [watch_ab_ok.2.1]; decide)]
  ihave #Huch := common.isRespChan_of_state uch γu _ (fun σ => iprop(⌜stateHistOk σ⌝)) _ $$ Husp
  (try wp_auto)
  -- `uevs, ok := common.Collect(uch, LastIn(evs))`
  wp_apply (wp_LastIn esl evs (DFrac.own 1)) $$ [Hes] as Hes
  · iframe; try iframe #
  ihave Hucons : etcdWatchConsumer γu 0 (W64 0) $$ [Hucons Hucur]
  · unfold etcdWatchConsumer
    iexists []
    rw [← h10]
    iframe Hucons Hucur
    ipureintro; rfl
  wp_apply (wp_Collect (common.stateOk _ (fun σ => iprop(⌜stateHistOk σ⌝))) (fun _ _ => True)
      (fun _ e => iprop(⌜permittedK go!"u" e.Key'⌝)) iprop(True) uch γu _ trivial
      (fun _ _ _ _ => inferInstance)
      (fun c c' v r => common.stateOk_closeErr _ _ c c' v r)
      (fun n c c' v r hne hI => u_resp _ ⟨watch_ab_ok.2.1, watch_ab_ok.2.2⟩ _ n c c' v r hne hI))
    $$ [Hucons] as %usl %uok Hucol
  · iframe; iframe #
    iintro !>; itrivial
  (try wp_auto)
  wp_apply Hucancel $$ [] as -
  · itrivial
  (try wp_auto)
  cases uok
  · -- the watch ended before the history's last event in `[lo, hi)`
    (try wp_auto)
    iapply HΦ; ipureintro; right; right; rfl
  ihave ⟨%uevs, Hues, -, #Huevs⟩ := Hucol $$ %rfl
  (try wp_auto)
  -- `for _, e := range uevs { if !Permitted("u", e.Key) { panic(...) } }; return Ok`: every
  -- event's key is u's (`Huevs`)
  ihave %Huel := ownSlice_len $$ Hues
  ihave HU : (∃ (j : w64) (e0 : common.wev),
      "i" ∷ i_ptr ↦ j ∗ "e" ∷ e_ptr ↦ e0 ∗ "Hues" ∷ usl ↦* uevs ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z usl.len⌝ : IProp GF) $$ [i e Hues]
  · iexists W64 0, _
    iframe
    ipureintro; constructor <;> word
  wp_for HU
  wp_if_destruct
  · have Hlt : sint.Z j < sint.Z usl.len :=
      Classical.byContradiction fun h => by simp [h] at Hif
    have Hb' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z usl.len := ⟨Hj.1, Hlt⟩
    simp only [Hb', _root_.and_self, ↓reduceIte]
    list_elem uevs (sint.nat j) as x
    wp_apply wp_load_slice_index usl (sint.Z j) uevs (DFrac.own 1) x Hj.1 $$ [Hues] as Hues
    · iframe; ipureintro; exact Hx_lookup
    ihave %Hux := Huevs $$ %(sint.nat j) %x %Hx_lookup
    (try wp_auto)
    wp_apply wp_Permitted
    rw [decide_eq_true Hux]
    (try wp_auto)
    wp_for_post
    iframe
    iexists j + W64 1, x
    iframe
    ipureintro; constructor <;> word
  · (try wp_auto)
    iapply HΦ; ipureintro; left; rfl

end proof

end authkv
end EtcdGrove
end Perennial
