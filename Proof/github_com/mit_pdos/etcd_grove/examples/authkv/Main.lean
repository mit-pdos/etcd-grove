/-
`Main()` (`examples/authkv/authkv.go`; the auth plan's E2b): **proved up to `SetUp`**, the rest a
`sorry` (2026-10-30). Lean-first (no Rocq counterpart).

Proved: the logger; the member's ghost state with auth on (`ak_alloc`) and the history invariant
(`akHist_alloc`); `startServer` (`memberUpOn`); `Serve` with auth on (`Serve.specOn`) with the ghost
step `ak_served_kv` (`MainServe.lean`: the KV methods with auth on, the Auth service's admin methods
and `Authenticate`); `NewClient` (no user name, no token); `SetUp` (its puts under the history
invariant, `akHist_setupAu`; the TLS fallback off and the auth store's cost from `memberUpOn`), and
every error's return of `Failed`. Not yet: the user clients (`newUserClient`, over `Authenticate`'s
registration `ak_served_kv` gives), the workloads (`watchAddrFacts` with auth on, from G2's
mode-generic `srvKVFacts`), root's last write and the two watches. `notes/authkv-main-plan.md`,
"Main: what blocks it".

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
public import Proof.github_com.mit_pdos.etcd_grove.examples.authkv.MainAlloc
public import Proof.github_com.mit_pdos.etcd_grove.examples.authkv.MainServe
public import Proof.github_com.mit_pdos.etcd_grove.examples.authkv.Hist
public import Proof.go_etcd_io.etcd.client.v3.ServeFromStart
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

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
    (wp_SetUp : SetUp.spec (GF := GF) (hG := hG))
    (wp_newUserClient : newUserClient.spec (GF := GF) (hG := hG))
    (wp_Work : Work.spec (GF := GF) (hG := hG))
    (wp_Principals : Principals.spec (GF := GF) (hG := hG))
    (wp_CheckHistory : CheckHistory.spec (GF := GF) (hG := hG))
    (wp_LastIn : LastIn.spec (GF := GF) (hG := hG)) :
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
  (try wp_auto)
  wp_apply wp_NewNop as %lg %Hlg
  (try wp_auto)
  -- the member's ghost state with auth on, the client's half of the KV state, its view of the
  -- auth history (`ak_alloc`), and the history invariant over the former (`akHist_alloc`)
  have hblen0 : boot.length = 1 := by rw [Hbf.boot.1]; rfl
  imod (ak_alloc id ctxs boot Hbf.idLow Hbf.boot Hbf.cc (by omega) (by omega)) $$ Hmarsh
    with ⟨%γ, %ρ, %E₀, %Φs, %γn, %σ₀, %Hal, Hmb, #Hnet, Hetcd, Hview⟩
  obtain ⟨hvs, hrule, hboot, hγn1, hγn2, hσ₀, hc0⟩ := Hal
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
  -- `Serve(s, clientAddr)`, with the ghost step `ak_served_kv`: the KV methods with auth on, the
  -- Auth service's admin methods and `Authenticate` at the address
  haveI := Hms
  wp_apply (wp_ServeOn srv go!"127.0.0.1:23916" E { ρ with wait := γw } ρ.rd cfg γa
      (fun cid mid _ => iprop(akKVOn go!"127.0.0.1:23916" srv E { ρ with wait := γw } cid mid ∗
        setupAuthServed go!"127.0.0.1:23916" srv E { ρ with wait := γw } ∗
        isGrpcRpc go!"127.0.0.1:23916" authnMethod (client.etcdAuthenticateSpec γa)))
      HEo (by rw [HElg]; exact Hlg) HEtr HEw Hms Hbuq)
    $$ [Haddr Hlg3 Hbemu Hgo Hwpi HWR Hlts Hlgs Hrds Hsts Hrslots Hbms] as %serr Hs
  · iframe; iframe #
    iintro %gs %lis %cid %mid %R Hg
    iunfold common.grpcUpOn at Hg
    icases Hg with ⟨%C, %q, %p, %pw, %pa, %il, %im, %iu, %ims, %is, %svcs, %regs, %sregs, %d',
      %HC, #Hgc, Hgsn, #Hq, #Hkvs, #Hpa, #Hws, #Hil, #Him, #Hiu, #Hims, #His, -, -, -, -, -,
      Hlis⟩
    obtain ⟨HCA, HCE, Hregs1, HregsA, Hregs2, hRs, hRE, hRw, hRγ⟩ := HC
    icases replicate_take2 _ _ (by omega) $$ Hlts with ⟨-, -, Hlts⟩
    icases replicate_take2 _ _ (by omega) $$ Hrds with ⟨-, -, Hrds⟩
    ihave Hslots := client.etcdGrpcSlots_of_started srv E ρ.rd 1 (64 - 2) 64
        (Int.toNat sync.rwmutex.actualMaxReaders) 64 (by omega) (by omega)
        (by have := sync.actualMaxReaders_ge_2; omega) (by omega)
        $$ [Hlts Hlgs Hrds Hsts Hrslots Hbms]
    · iframe
    ihave #Hkva := client.kvServerAt_of_is p srv C.A cid mid C.n $$ Hkvs
    rw [HCA]
    imod (ak_served_kv go!"127.0.0.1:23916" gs q p pa srv lis E { ρ with wait := γw } cid mid C.n
        il im iu ims is svcs regs sregs 1 γa HEo Hregs1 HregsA wp_BcryptCost)
      $$ [Hgsn Hlis Hslots] with ⟨Hserv, -, #HKV, #HSA, #HAu⟩
    · iframe; iframe #
      iintro !>
      imodintro
      iunfold idCred
      ipureintro; exact Hrb48
    imodintro
    iframe Hserv HKV HSA HAu
  icases Hs with (%Hserr | ⟨%Hserr, %cid, %mid, %R, #HKV, #HSA, #HAu⟩)
  · cases serr with
    | nil => exact absurd rfl Hserr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ipureintro; right; left; rfl
  subst Hserr
  wp_auto
  -- `NewClient(clientAddr, lg)`: the client with no user name
  wp_apply (wp_NewClient go!"127.0.0.1:23916" lg
      (EtcdGrove.client.srvWEnv R go!"127.0.0.1:23916" [] null null [] null ρ.rd.kv.st) Hlg
      (by unfold plainEndpoint; decide) Htb31) as %cl %cerr Hcl
  icases Hcl with (⟨%Hcerr, #Hnc, Hctk⟩ | %Hcfail)
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
  iunfold akKVOn at HKV
  icases HKV with ⟨#Hput, -, -, -⟩
  wp_apply (wp_SetUp cl go!"127.0.0.1:23916"
      (EtcdGrove.client.srvWEnv R go!"127.0.0.1:23916" [] null null [] null ρ.rd.kv.st) srv E
      { ρ with wait := γw } cid mid γa HEo
      (by show uint.Z ρ.rd.kv.c0 ≤ uint.Z ρ.rd.raft.ai0; rw [hc0]; word) hAs)
    $$ [Hctk Hview] as %ok Hok
  · iframe; iframe #
  cases ok
  · wp_auto
    iapply HΦ; ipureintro; right; left; rfl
  -- the rest (`notes/authkv-main-plan.md`, "Main: what blocks it"): the user clients, the
  -- workloads (the watch facts with auth on), root's last write and the two watches
  sorry

end proof

end authkv
end EtcdGrove
end Perennial
