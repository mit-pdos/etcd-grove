/-
`Main()` (`examples/authkv/authkv.go`; the auth plan's E2b): **proved up to root's last write**
(`root.Put(ctx, "z/end", "end")`), the rest a `sorry` (2026-10-30). Lean-first (no Rocq counterpart).

Proved: the logger; the member's ghost state with auth on (`ak_alloc`) and the history invariant
(`akHist_alloc`); `startServer` (`memberUpOn`); `Serve` with auth on (`Serve.specOn`) with the
ghost step `ak_served_kv` (`MainServe.lean`: the KV methods with auth on, the Auth service's admin
methods and `Authenticate`); `NewClient` (no user name, no token); `SetUp` (its puts under the
history invariant, `akHist_setupAu`; the TLS fallback off and the auth store's cost from
`memberUpOn`), and every error's return of `Failed`. `ak_served_watch` gives the watch server's
facts (`watchAddrFacts`) at the clients' watcher environment `akV R`, for the workloads and the
watches. Then the user clients (`newUserClient` for root, u and v, over the registration of
`Authenticate` that `ak_served_kv` gives: `authTokReg_of`). Then the workloads: the auth state
fixed after the set-up (`akAuthFixed_alloc` from `SetUp`'s post), the principals' loop
(`Principals`; `c` the client of `u`, of `v`, or the set-up's, with its tokens as `akTokP`), each
`Work(c, who)` in a goroutine under a wait group, and `wg.Wait()`. Then root's last write, in a
timeout context (`client.wp_WithTimeout_bg`; the token does not matter, so no metadata fact), through
root's client (`client_Put_on`), its update admitted by the history from any state
(`akHist_endAu`); the reply (`putRespMsg`, `putReplied`) is kept for the watch's revision. Not yet:
the two watches (`notes/authkv-main-plan.md`, "Main: what blocks it").

What the proof needs, as the auth plan put it (`notes/decisions.md`, "E2b", "E2e" and "E2f of the auth plan"):
- **the server in the mode `on γa`** (E2e's next step, E2g): `NewServer.spec` generic in the auth
  mode, the store from `auth.newAuthStore_boot` (D22's part the named premise
  `auth.authSchemaBoot`, the provider's `auth.tokenProviderBoot`), `srvAuthBound` from
  `srvAuthBound_of_authInv`, the apply thread admitting auth requests with the authority
  `authOwn`;
- **`SetUp`'s premises** (the auth-mode merge's 5b): `clientTokAt cl [ep] (fun _ => False)` (G1's
  `NewClient`), `setupAuthServed` (`etcd_kv_auth_served_on`), `□ (srvTLSId s -∗ False)` (the
  started member's `ClientCertAuthEnabled` is the config's `false`: `memberUpOn` does not yet
  export it), the client's view `authHistView ρ.kv [srvAuthSt0]` and `c0 ≤ ai0` (the boot,
  `server_cluster_alloc_on`); its post, the history frozen at `setupSt r`, then gives `setupSt` at
  every later position (`authHistFrozen_prefix`);
- **the client's auth contract** over the contexts' metadata (`ClientAuth.lean`): C1
  (`userAttemptOk`) and C2/C4 (`deliversOutgoing`) in the client's attempt contract
  (`grpcInvokerOk` says nothing of metadata today), C3 the spec
  `metadata.AppendToOutgoingContext.spec` (a trust-boundary axiom; `reqCtx` proved over it), and
  that `reqCtx`'s timeout context has no outgoing token (Perennial's context model does not
  describe values at other keys); the bad principal is then unbound (`badCtx_unbound`);
- **the workload** (`Work`): each call's reply at the server's verdict -- an error for a refused
  principal (A1, A4), the persistent-update case of the client's write results for the bad
  principal's resent writes (E2d) -- and the checks, proved (`refused`, `checkKVs`,
  `checkTxnReads`, `CheckHistory`, `Writer`, `LastIn`, `keyOf`: E2f).
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
    (wp_WithTimeout : context.WithTimeoutBackground.spec (GF := GF) (hG := hG)) :
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
        (by simp) rfl hlog (by omega) Hms.watch_impl Hregs2 rfl rfl)
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
  wp_apply (wp_newUserClient go!"root" _ lg (akV R) (fun t => auth.tokIssued γa t go!"root") Hlg
      (by omega)) as %rcl %rerr Hrc
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
  wp_apply (wp_newUserClient go!"u" _ lg (akV R) (fun t => auth.tokIssued γa t go!"u") Hlg
      (by omega)) as %ucl %uerr Huc
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
  wp_apply (wp_newUserClient go!"v" _ lg (akV R) (fun t => auth.tokIssued γa t go!"v") Hlg
      (by omega)) as %vcl %verr Hvc
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
  iunfold clientTokAt at Hrtk
  icases Hrtk with ⟨%rapi, %rconn, #Hrkvf, #Hrobj, -, -, -⟩
  wp_apply context.wp_Background
  (try wp_auto)
  wp_apply (client.wp_WithTimeout_bg wp_WithTimeout wp_ErrAny hAs _)
    as %ectx %ecd %ecancel ⟨#Hecancel, #Hectx, #Hece, -⟩
  (try wp_auto)
  wp_apply (client_Put_on rcl rapi rconn go!"127.0.0.1:23916" srv E { ρ with wait := γw } cid mid
      ectx ecd endKey go!"end" slice.nil (fun _ => iprop(True)) []) $$ [] as %eresp %eerr Hend'
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
  -- the rest (`notes/authkv-main-plan.md`, "Main: what blocks it"): the two watches
  sorry

end proof

end authkv
end EtcdGrove
end Perennial
