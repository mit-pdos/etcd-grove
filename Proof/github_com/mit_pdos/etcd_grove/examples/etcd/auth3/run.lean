/-
`run(s1, s2, s3, a1, a2, a3, lg)` (`examples/etcd/auth3/auth3.go`; the auth3 Scope's A2, 2026-11-14):
**proved**, over its callees' specs. Lean-first (no Rocq counterpart). authkv's `Run.wp_proof`
(`auth/Run.lean`) across three members:

- each member served by `serve_member` (`Run`'s `Serve` step with the ghost steps `ak_served_kv` and
  `ak_served_watch`, the `GoAttach` resources `grpcUpOn` holds handed back, so that the one thread
  token goes on to the next member);
- the set-up through member 1 (`SetUp`), its facts carried to each member's names
  (`etcdstart.sameCluster`, `*_same`);
- root's barrier read at each member (`barrier`), giving `akAuthFixed` at that member's names;
- each workload at its member's names (`Work`): u at member 2, v at member 3, anon at member 1, bad
  at member 2;
- root's last write, history watch and `CheckHistory` through member 1, u's watch through member 2,
  as in `Run`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.WatchSrv
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.auth.SetUp
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.auth.Work
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.auth.Principals
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.auth.CheckHistory
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.auth.LastIn
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Serve
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.NewClient
public import Spec.context.ErrAny
public import Proof.go_etcd_io.etcd.client.v3.ErrorsNewOk
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.auth.WorkEnv
public import Perennial.Proof.sync.WaitGroupJoin
public import Perennial.Proof.sync.Link
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.auth.MainServe
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.auth.Hist
public import Proof.go_etcd_io.etcd.client.v3.ServeFromStart
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo
public import Proof.go_etcd_io.etcd.client.v3.TimeoutCtx
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.auth.ClientOn
public import Spec.context.WithTimeoutBackground
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Collect
public import Spec.go_etcd_io.etcd.client.v3.watcher__Watch
public import Spec.go_etcd_io.etcd.client.v3.WithPrefix
public import Spec.go_etcd_io.etcd.client.v3.WithRev
public import Spec.go_etcd_io.etcd.client.v3.WithRange
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.auth.Permitted
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.auth.RootWatch
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.auth.WorkCalls
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Served

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.auth3.run
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.auth3.newUserClient
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.auth3.barrier
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.auth3.AuthFixed

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_auth3

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver etcd_auth

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **A member's clients' watch environment** (`Run`'s `akV`): one server, at its model and watch
facts with auth on, at the client address `addr`. -/
abbrev akV (addr : GoString) (ρ : ReqNames) (R : v3rpc.WSrv GF) : client.WEnv GF :=
  ⟨R, addr, [], null, null, go!"a", null, v3rpc.etcdModelOfServer R.E ρ.rd true,
    client.srvWL (etcdstart.srvWOf R.E ρ.rd true), fun _ => (addr, R), 1, ρ.rd.kv,
    etcdstart.srvWOf R.E ρ.rd true, fun _ => etcdstart.srvWOf R.E ρ.rd true⟩

end defs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.auth3.Assumptions]

/-- **A member served** (`Run`'s `Serve` step): `etcdstart.Serve(s, addr)` with the ghost steps
`ak_served_kv` and `ak_served_watch`; on success, the member's served facts at its environment and
the thread token (from the `GoAttach` resources `grpcUpOn` holds). -/
theorem serve_member [go_etcd_io.etcd.cache.v3.Assumptions]
    (wp_Serve : etcdstart.Serve.spec (GF := GF) (hG := hG))
    (wp_BcryptCost : auth.authStore.BcryptCost.spec (GF := GF) (hG := hG))
    (hP : mvcc.api.persistent.law (GF := GF))
    (hR : mvcc.api.mvccState_reachable.law (GF := GF))
    (s lg : Loc) (addr : GoString) (ρ : ReqNames) (E₀ : apply.AEnv GF) (γn : NetNames GF)
    (id : w64) (γa : auth.AuthNames)
    (Htb : threadBound GF ≤ 2 ^ 28) (HLv : srvLevels (GF := GF)) (Hrb48 : receiptBound GF ≤ 2 ^ 48)
    (Hbuq : apply.backendUnderQuota) (Hrf : grpcRepliesFit) (Hms : v3rpc.ServerMethodSets)
    (hlog : ρ.rd.kv.log0 = [[], []]) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗ client.eofOk ∗
        zapLoggerOk lg ∗ netAddrFree addr ∗ etcdstart.memberUpOn s ρ E₀ lg γn id γa }}
      (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Serve)) (Val #s))
        (Val #addr))
    {{ (err : GoInterface), RET #err; ⌜err ≠ GoInterface.nil⌝ ∨
        (⌜err = GoInterface.nil⌝ ∗ threadTok ∗
          ∃ (E : apply.AEnv GF) (γw : GName) (cid mid : w64) (R : v3rpc.WSrv GF),
            ⌜E.authMode = .on γa ∧ R.E = E ∧ R.s = s⌝ ∗ isServerReadM true s E ρ.rd ∗
            □ (srvTLSId s -∗ False) ∗ akKVOn addr s E { ρ with wait := γw } cid mid ∗
            setupAuthServed addr s E { ρ with wait := γw } ∗
            isGrpcRpc addr authnMethod (client.etcdAuthenticateSpec γa) ∗
            watchAddrFacts (akV addr ρ R) ∗ auth.modeTag R.tag (.on γa)) }} := by
  iintro %Φ ⟨#Pst, #Psrv, #Pv3, #Ppb, #Heo, #Hlgz, Haddr, Hup⟩ HΦ
  icases etcdstart.memberUpOn_served _ _ _ _ _ _ _ $$ Hup with ⟨%E, %cfg, %γw, %HE, #Hreq, #Hrd0,
    #Hlb, #Hsf, Hgo, Hlg3, Hbemu, #Hwb, Hstk, -, #Htls, #HBF, -⟩
  obtain ⟨HEa, HEo, HElg, HEtr, HEw⟩ := HE
  have hon : E.authOn = true := by unfold apply.AEnv.authOn; rw [HEo]; rfl
  ihave #HzlgC : zapLoggerOk cfg.Logger' $$ []
  · rw [HElg]; iexact Hlgz
  haveI := Hms
  wp_apply (wp_Serve s addr E { ρ with wait := γw } ρ.rd cfg
      (fun cid mid R => iprop(⌜R.E = E ∧ R.s = s⌝ ∗
        akKVOn addr s E { ρ with wait := γw } cid mid ∗
        setupAuthServed addr s E { ρ with wait := γw } ∗
        isGrpcRpc addr authnMethod (client.etcdAuthenticateSpec γa) ∗
        watchAddrFacts (akV addr ρ R) ∗ auth.modeTag R.tag E.authMode ∗ srvGoRes s)))
    $$ [Haddr Hlg3 Hbemu Hgo Hstk] as %serr Hs
  · iframe; iframe #
    isplitr
    · ipureintro; exact ⟨HEtr, HEw, Hms, Hbuq, by rw [HEo]; simp, Htb⟩
    iintro %gs %lis %cid %mid %R Hg
    rw [hon]
    ihave Hg := etcdstart.grpcUpM_true _ _ _ _ _ _ _ _ _ _ $$ Hg
    iunfold etcdstart.grpcUpOn at Hg
    icases Hg with ⟨%C, %q, %p, %pw, %pa, %il, %im, %iu, %ims, %is, %svcs, %regs, %sregs,
      %HC, #Hgc, Hgsn, #Hq, #Hkvs, #Hpa, #Hws, #Hil, #Him, #Hiu, #Hims, #His, -, -, Hgr,
      Hlis, Hleft, -⟩
    obtain ⟨HCA, HCE, Hregs1, HregsA, Hregs2, hRs, hRE, hRw, hRγ, Hnd⟩ := HC
    imod (etcdstart.kvServeStocks_pools s E ρ.rd ⊤) $$ Hstk with ⟨#Hrp, #Hrb⟩
    ihave #Hkva := client.kvServerAt_of_is p s C.A cid mid C.n $$ Hkvs
    rw [HCA]
    -- (R9) the watch path's server facts, with auth on
    ihave %hkv := etcdstart.kv_wsIface_of_cfg s E cfg C $$ [Hsf Hgc]
    · iframe #
    haveI := v3rpc.srvWOk_persistent hP (etcdstart.srvWOf R.E ρ.rd true) R.wsl v3rpc.wsN
    ihave #HWok : v3rpc.srvWOk (etcdstart.srvWOf R.E ρ.rd true) R.wsl v3rpc.wsN $$ []
    · rw [hRw, hRE]
      iapply (etcdstart.srvWOk_of_readOn hP hR s E ρ.rd C.wsl hkv (by omega))
      rw [← hon]; iexact Hrd0
    -- (phase 7's switch, SW1) the `Watch` stream's run contract, which the start registers
    ihave #Hwr := v3rpc.etcd_watch_served_chain pw R (etcdstart.srvWOf R.E ρ.rd true) ims is ρ.rd rfl
      (by rw [sync.rwmutex.actualMaxReaders_unseal]; omega) HLv Hms.watch_impl $$ []
    · rw [hRs, hRE]
      iframe #
    imod (ak_served_kv addr gs q p pa s lis E { ρ with wait := γw } cid mid C.n
        il im iu ims is svcs regs sregs [v3rpc.watchMethod pw R (etcdstart.srvWOf R.E ρ.rd true)]
        γa HEo Hregs1 HregsA
        (by intro m hm; simp only [List.mem_singleton] at hm; subst hm; exact Hregs2) (by simp)
        wp_BcryptCost Hrf Hnd HLv)
      $$ [Hgsn Hlis Hleft] with ⟨Hserv, #Hss, #HKV, #HSA, #HAu, -⟩
    · iframe; iframe #
      iintro !>
      imodintro
      iunfold idCred
      ipureintro; exact Hrb48
    imod (ak_served_watch hP (akV addr ρ R) addr pw s E ρ.rd rfl hRE hRs
        (by simp [akV]) (kvSame_refl _) hlog (by omega) rfl rfl rfl rfl)
      $$ [] with ⟨#HWF, #Htag⟩
    · iframe; iframe #
    imodintro
    iframe HKV HSA HAu HWF Htag Hgr
    isplitl [Hserv]
    · iexists _; iexact Hserv
    ipureintro; exact ⟨hRE, hRs⟩
  iapply HΦ
  icases Hs with (%Hserr | ⟨%Hserr, %cid, %mid, %R, ⟨%HRQ, #HKV, #HSA, #HAu, #HWF, #Htag, Hgr⟩⟩)
  · ileft; ipureintro; exact Hserr
  iright
  iunfold srvGoRes at Hgr
  icases Hgr with ⟨-, Htok⟩
  iframe Htok
  isplitl []
  · ipureintro; exact Hserr
  iexists E, γw, cid, mid, R
  rw [← hon]
  iframe HKV HSA HAu HWF Hrd0 Htls
  isplitl []
  · ipureintro; exact ⟨HEo, HRQ⟩
  rw [← HEo]; iexact Htag


set_option maxHeartbeats 3200000 in
theorem run.wp_proof
    (wp_Serve : etcdstart.Serve.spec (GF := GF) (hG := hG))
    (wp_NewClient : etcdstart.NewClient.spec (GF := GF) (hG := hG))
    (wp_BcryptCost : auth.authStore.BcryptCost.spec (GF := GF) (hG := hG))
    (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG))
    (wp_SetUp : etcd_auth.SetUp.spec (GF := GF) (hG := hG))
    (wp_newUserClient : newUserClient.spec (GF := GF) (hG := hG))
    (wp_barrier : barrier.spec (GF := GF) (hG := hG))
    (wp_Work : etcd_auth.Work.spec (GF := GF) (hG := hG))
    (wp_Principals : etcd_auth.Principals.spec (GF := GF) (hG := hG))
    (wp_CheckHistory : etcd_auth.CheckHistory.spec (GF := GF) (hG := hG))
    (wp_LastIn : etcd_auth.LastIn.spec (GF := GF) (hG := hG))
    (wp_WithTimeout : context.WithTimeoutBackground.spec (GF := GF) (hG := hG))
    (wp_Collect : etcdstart.Collect.spec (GF := GF) (hG := hG))
    (wp_Watch : watcher.Watch.spec (GF := GF) (hG := hG))
    (wp_WithPrefix : WithPrefix.spec (GF := GF) (hG := hG))
    (wp_WithRev : WithRev.spec (GF := GF) (hG := hG))
    (wp_WithRange : WithRange.spec (GF := GF) (hG := hG))
    (wp_Permitted : etcd_auth.Permitted.spec (GF := GF) (hG := hG))
    (hP : mvcc.api.persistent.law (GF := GF))
    (hR : mvcc.api.mvccState_reachable.law (GF := GF)) :
    run.spec (GF := GF) (hG := hG) := by
  intro CS ES FS RS CRE CEC s₁ s₂ s₃ lg a₁ a₂ a₃ ρ₁ ρ₂ ρ₃ E₁₀ E₂₀ E₃₀ γn id₁ id₂ id₃ γa₁ γa₂ γa₃
    Hpe₁ Hpe₂ Hpe₃ Htb HLv Hrb48 Hbuq Hrf Hms hAs hc0 hlog hs₂ hs₃
  have Htb31 : threadBound GF ≤ 2 ^ 31 := by omega
  wp_start as ⟨#Hlgz, Ha₁, Ha₂, Ha₃, Hup₁, Hup₂, Hup₃, #Hhist, Hview⟩
  ihave %Hlg := zapLoggerOk_ne_null lg $$ Hlgz
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
  ihave #Pst : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart $$ []
  · iPkgInit
  ihave #Heo : client.eofOk (GF := GF) $$ []
  · iapply (client.eofOk_of_init hAs)
    iPkgInit
  have hlog₂ : ρ₂.rd.kv.log0 = [[], []] := by rw [hs₂.2.2.2.1, hlog]
  have hlog₃ : ρ₃.rd.kv.log0 = [[], []] := by rw [hs₃.2.2.2.1, hlog]
  (try wp_auto)
  -- `Serve(s1, a1)`, `Serve(s2, a2)`, `Serve(s3, a3)`: the thread token from member to member
  wp_apply (serve_member wp_Serve wp_BcryptCost hP hR s₁ lg a₁ ρ₁ E₁₀ γn id₁ γa₁ Htb HLv Hrb48
      Hbuq Hrf Hms hlog) $$ [Ha₁ Hup₁] as %serr₁ Hs₁
  · iframe; iframe #
  icases Hs₁ with (%Hserr | ⟨%Hserr, Htok, %E₁, %γw₁, %cid₁, %mid₁, %R₁, %HR₁, #Hrd₁, #Htls₁,
    #HKV₁, #HSA₁, #HAu₁, #HWF₁, #Htag₁⟩)
  · cases serr₁ with
    | nil => exact absurd rfl Hserr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ipureintro; right; left; rfl
  subst Hserr
  wp_auto
  ihave Hup₂ := Hup₂ $$ Htok
  wp_apply (serve_member wp_Serve wp_BcryptCost hP hR s₂ lg a₂ ρ₂ E₂₀ γn id₂ γa₂ Htb HLv Hrb48
      Hbuq Hrf Hms hlog₂) $$ [Ha₂ Hup₂] as %serr₂ Hs₂
  · iframe; iframe #
  icases Hs₂ with (%Hserr | ⟨%Hserr, Htok, %E₂, %γw₂, %cid₂, %mid₂, %R₂, %HR₂, #Hrd₂, #Htls₂,
    #HKV₂, -, #HAu₂, #HWF₂, #Htag₂⟩)
  · cases serr₂ with
    | nil => exact absurd rfl Hserr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ipureintro; right; left; rfl
  subst Hserr
  wp_auto
  ihave Hup₃ := Hup₃ $$ Htok
  wp_apply (serve_member wp_Serve wp_BcryptCost hP hR s₃ lg a₃ ρ₃ E₃₀ γn id₃ γa₃ Htb HLv Hrb48
      Hbuq Hrf Hms hlog₃) $$ [Ha₃ Hup₃] as %serr₃ Hs₃
  · iframe; iframe #
  icases Hs₃ with (%Hserr | ⟨%Hserr, -, %E₃, %γw₃, %cid₃, %mid₃, %R₃, %HR₃, #Hrd₃, #Htls₃,
    #HKV₃, -, #HAu₃, #HWF₃, #Htag₃⟩)
  · cases serr₃ with
    | nil => exact absurd rfl Hserr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ipureintro; right; left; rfl
  subst Hserr
  wp_auto
  -- `NewClient(a1, lg)`: the client with no user name, at member 1
  wp_apply (wp_NewClient a₁ lg (akV a₁ ρ₁ R₁) Hpe₁ Htb31) as %cl %cerr Hcl
  · iframe #
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
  -- `SetUp(cli)` through member 1
  ihave #Hsau : iprop(□ ∀ k : GoString, ⌜k ∈ setupKeys⌝ -∗
      kvOpAu1 ρ₁.rd.kv (.put (client.putKeyOp k go!"setup")) (fun _ => iprop(True))) $$ []
  · iintro !> %k %hk
    ihave #H := akHist_setupAu ρ₁.rd.kv k hk $$ Hhist
    iexact H
  ihave #Hput : isGrpcRpcMd a₁ go!"/etcdserverpb.KV/Put"
      (client.etcdPutSpecOn (srvTLSId s₁) E₁ { ρ₁ with wait := γw₁ } cid₁ mid₁) $$ []
  · iunfold akKVOn at HKV₁
    icases HKV₁ with ⟨#H, -, -, -⟩
    iexact H
  wp_apply (wp_SetUp cl a₁ (akV a₁ ρ₁ R₁) s₁ E₁ { ρ₁ with wait := γw₁ } cid₁ mid₁ γa₁ HR₁.1
      (by show uint.Z ρ₁.rd.kv.c0 ≤ uint.Z ρ₁.rd.raft.ai0; rw [hc0]; word) hAs)
    $$ [Hview] as %ok Hok
  · iframe; iframe #
  cases ok
  · wp_auto
    iapply HΦ; ipureintro; right; left; rfl
  rw [ite_eq_left rfl]
  icases Hok with ⟨%γz, %hs, %Lset, %kpub, %rset, #Hfz, #Hllb, %Hadm, -, -, %Lc, #HLc,
    %HLcst⟩
  -- the set-up's facts at members 2 and 3's names
  ihave #Hfz₂ := authHistFrozen_same { ρ₁ with wait := γw₁ } { ρ₂ with wait := γw₂ } hs₂ γz hs $$ Hfz
  ihave #Hfz₃ := authHistFrozen_same { ρ₁ with wait := γw₁ } { ρ₃ with wait := γw₃ } hs₃ γz hs $$ Hfz
  ihave #Hllb₂ := srvReqLogLb_same { ρ₁ with wait := γw₁ } { ρ₂ with wait := γw₂ } hs₂ Lset $$ Hllb
  ihave #Hllb₃ := srvReqLogLb_same { ρ₁ with wait := γw₁ } { ρ₃ with wait := γw₃ } hs₃ Lset $$ Hllb
  ihave #HLc₂ := srvRLogLb_same { ρ₁ with wait := γw₁ } { ρ₂ with wait := γw₂ } hs₂ Lc $$ HLc
  ihave #HLc₃ := srvRLogLb_same { ρ₁ with wait := γw₁ } { ρ₃ with wait := γw₃ } hs₃ Lc $$ HLc
  have Hadm₂ := Hadm
  rw [← admStates_same { ρ₁ with wait := γw₁ } { ρ₂ with wait := γw₂ } hs₂,
    ← srvAuthAtLog_same { ρ₁ with wait := γw₁ } { ρ₂ with wait := γw₂ } hs₂] at Hadm₂
  have Hadm₃ := Hadm
  rw [← admStates_same { ρ₁ with wait := γw₁ } { ρ₃ with wait := γw₃ } hs₃,
    ← srvAuthAtLog_same { ρ₁ with wait := γw₁ } { ρ₃ with wait := γw₃ } hs₃] at Hadm₃
  have HLcst₂ := HLcst
  rw [← srvAuthAtLog_same { ρ₁ with wait := γw₁ } { ρ₂ with wait := γw₂ } hs₂] at HLcst₂
  have HLcst₃ := HLcst
  rw [← srvAuthAtLog_same { ρ₁ with wait := γw₁ } { ρ₃ with wait := γw₃ } hs₃] at HLcst₃
  ihave #Hhist₂ := akHistInv_same { ρ₁ with wait := γw₁ } { ρ₂ with wait := γw₂ } hs₂ $$ Hhist
  ihave #Hhist₃ := akHistInv_same { ρ₁ with wait := γw₁ } { ρ₃ with wait := γw₃ } hs₃ $$ Hhist
  -- the barrier at each member: `if !barrier(ak, lg) { return auth.Failed }`, k = 1, 2, 3
  (try wp_auto)
  wp_apply (wp_barrier a₁ lg (akV a₁ ρ₁ R₁) s₁ E₁ { ρ₁ with wait := γw₁ } cid₁ mid₁ γa₁ γz hs
      Lset Lc rset Hpe₁ (by omega) HR₁.1 hAs) as %ok₁ Hb₁
  · iframe #; ipureintro; exact ⟨Hadm, HLcst⟩
  icases Hb₁ with (%Hb | ⟨%Hb, %i₁, #Hfix₁⟩) <;> subst Hb
  · wp_auto
    iapply HΦ; ipureintro; right; left; rfl
  wp_auto
  wp_apply (wp_barrier a₂ lg (akV a₂ ρ₂ R₂) s₂ E₂ { ρ₂ with wait := γw₂ } cid₂ mid₂ γa₂ γz hs
      Lset Lc rset Hpe₂ (by omega) HR₂.1 hAs) as %ok₂ Hb₂
  · iframe #; ipureintro; exact ⟨Hadm₂, HLcst₂⟩
  icases Hb₂ with (%Hb | ⟨%Hb, %i₂, #Hfix₂⟩) <;> subst Hb
  · wp_auto
    iapply HΦ; ipureintro; right; left; rfl
  wp_auto
  wp_apply (wp_barrier a₃ lg (akV a₃ ρ₃ R₃) s₃ E₃ { ρ₃ with wait := γw₃ } cid₃ mid₃ γa₃ γz hs
      Lset Lc rset Hpe₃ (by omega) HR₃.1 hAs) as %ok₃ Hb₃
  · iframe #; ipureintro; exact ⟨Hadm₃, HLcst₃⟩
  icases Hb₃ with (%Hb | ⟨%Hb, %i₃, #Hfix₃⟩) <;> subst Hb
  · wp_auto
    iapply HΦ; ipureintro; right; left; rfl
  wp_auto
  -- the clients: root at member 1, u at member 2, v at member 3, the one with no token at member 2
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #Hall : client.ctxErrClientAll (GF := GF) $$ []
  · ihave #Hw := client.ctxErrClientAllW_of wp_ErrAny hAs $$ Pctx
    iunfold client.ctxErrClientAllW at Hw
    iunfold client.ctxErrClientAll
    iexact Hw
  wp_apply (wp_newUserClient a₁ go!"root" go!"root-pw" lg (akV a₁ ρ₁ R₁)
      (fun t => auth.tokIssued γa₁ t go!"root") Hpe₁ (by omega) (by unfold strsSizeOk; decide))
    as %rcl %rerr Hrc
  · iframe #
    iapply (client.authTokReg_of _ _ _ γa₁)
    iexact HAu₁
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
  wp_apply (wp_newUserClient a₂ go!"u" go!"u-pw" lg (akV a₂ ρ₂ R₂)
      (fun t => auth.tokIssued γa₂ t go!"u") Hpe₂ (by omega) (by unfold strsSizeOk; decide))
    as %ucl %uerr Huc
  · iframe #
    iapply (client.authTokReg_of _ _ _ γa₂)
    iexact HAu₂
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
  wp_apply (wp_newUserClient a₃ go!"v" go!"v-pw" lg (akV a₃ ρ₃ R₃)
      (fun t => auth.tokIssued γa₃ t go!"v") Hpe₃ (by omega) (by unfold strsSizeOk; decide))
    as %vcl %verr Hvc
  · iframe #
    iapply (client.authTokReg_of _ _ _ γa₃)
    iexact HAu₃
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
  wp_apply (wp_NewClient a₂ lg (akV a₂ ρ₂ R₂) Hpe₂ Htb31) as %bcl %berr Hbc
  · iframe #
  icases Hbc with (⟨%Hberr, #Hbnc, #Hbtk⟩ | %Hbfail)
  rotate_left
  · obtain ⟨Hberr, -⟩ := Hbfail
    cases berr with
    | nil => exact absurd rfl Hberr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ipureintro; right; left; rfl
  subst Hberr
  wp_auto
  -- the workloads: `for _, who := range auth.Principals() { ...; wg.Add(1); go func() {
  -- auth.Work(c, who); wg.Done() }() }`, then `wg.Wait()`
  wp_apply wp_Principals as %psl Hpsl
  imod ownSlice_persist _ _ _ $$ Hpsl with #Hpsl
  (try wp_auto)
  ihave %Hpl := ownSlice_len $$ Hpsl
  ipersist cli
  ipersist ucli
  ipersist vcli
  ipersist bcli
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
    -- `c` is `ucli` for u, `vcli` for v, `bcli` for bad, `cli` for anon
    wp_if_destruct
    rotate_left
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
        first
        | (wp_apply (wp_Work _ _ a₂ (akV a₂ ρ₂ R₂) s₂ E₂ { ρ₂ with wait := γw₂ } cid₂ mid₂ γa₂
              Lset i₂ hwho HR₂.1 ⟨rfl, rfl, rfl, rfl, HR₂.2.2, HR₂.2.1, rfl⟩ hAs)
           · iframe #
             rw [akTokP, ite_eq_left (Or.inl rfl)]; iexact Hutk
           (try wp_auto)
           wp_apply (sync.join.WaitGroup.wp_Done_of sync.WaitGroup.wp_Done iprop(True) wg_ptr)
             $$ [Hdone]
           · iframe
           itrivial)
        | (wp_apply (wp_Work _ _ a₃ (akV a₃ ρ₃ R₃) s₃ E₃ { ρ₃ with wait := γw₃ } cid₃ mid₃ γa₃
              Lset i₃ hwho HR₃.1 ⟨rfl, rfl, rfl, rfl, HR₃.2.2, HR₃.2.1, rfl⟩ hAs)
           · iframe #
             rw [akTokP, ite_eq_left (Or.inr rfl)]; iexact Hvtk
           (try wp_auto)
           wp_apply (sync.join.WaitGroup.wp_Done_of sync.WaitGroup.wp_Done iprop(True) wg_ptr)
             $$ [Hdone]
           · iframe
           itrivial)
        | (wp_apply (wp_Work _ _ a₂ (akV a₂ ρ₂ R₂) s₂ E₂ { ρ₂ with wait := γw₂ } cid₂ mid₂ γa₂
              Lset i₂ hwho HR₂.1 ⟨rfl, rfl, rfl, rfl, HR₂.2.2, HR₂.2.1, rfl⟩ hAs)
           · iframe #
             rw [akTokP, ite_eq_right (fun h => h.elim ‹_› ‹_›)]; iexact Hbtk
           (try wp_auto)
           wp_apply (sync.join.WaitGroup.wp_Done_of sync.WaitGroup.wp_Done iprop(True) wg_ptr)
             $$ [Hdone]
           · iframe
           itrivial)
        | (wp_apply (wp_Work _ _ a₁ (akV a₁ ρ₁ R₁) s₁ E₁ { ρ₁ with wait := γw₁ } cid₁ mid₁ γa₁
              Lset i₁ hwho HR₁.1 ⟨rfl, rfl, rfl, rfl, HR₁.2.2, HR₁.2.1, rfl⟩ hAs)
           · iframe #
             rw [akTokP, ite_eq_right (fun h => h.elim ‹_› ‹_›)]; iexact Hctk
           (try wp_auto)
           wp_apply (sync.join.WaitGroup.wp_Done_of sync.WaitGroup.wp_Done iprop(True) wg_ptr)
             $$ [Hdone]
           · iframe
           itrivial)
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
  ihave #Hend := akHist_endAu ρ₁.rd.kv go!"end" $$ Hhist
  imod v3rpc.kvLogLb_nil (GF := GF) E₁.γs with #HF0
  ihave #Hnil := optsAt_nil (GF := GF)
  ihave #Hrtk0 := Hrtk
  iunfold clientTokAt at Hrtk0
  icases Hrtk0 with ⟨%rapi, %rconn, #Hrkvf, #Hrobj, -, -, -⟩
  wp_apply context.wp_Background
  (try wp_auto)
  wp_apply (client.wp_WithTimeout_bg wp_WithTimeout wp_ErrAny hAs _)
    as %ectx %ecd %ecancel ⟨#Hecancel, #Hectx, #Hece, -, #HeO⟩
  iunfold metadata.outgoingCtxOkC at HeO
  icases HeO with ⟨%eom, #Heom⟩
  (try wp_auto)
  wp_apply (client_Put_on rcl rapi rconn a₁ s₁ E₁ { ρ₁ with wait := γw₁ } cid₁ mid₁
      ectx eom ecd endKey go!"end" slice.nil (fun _ => iprop(True)) []
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
    as %hctx %γhctx %hcancel ⟨#Hhcancel, #Hhctx, -, #hctxFrom⟩
  ihave #hctxO := metadata.outgoingCtxOkC_bgFrom hctx $$ hctxFrom
  ihave #hctxM := metadata.outMD_bgFrom hctx $$ hctxFrom
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
    client.watcher_of_clientTokAt wp_ErrAny hAs rcl _ (akV a₁ ρ₁ R₁)
      (fun t => auth.tokIssued γa₁ t go!"root") rfl rfl rfl rfl $$ [Pcl Pctx Ppb Hrnc HWF₁ Hrtk]
  · iframe #
  (try wp_auto)
  ihave #Hrau := akHist_readAu ρ₁.rd.kv $$ Hhist
  iunfold kvReadAu at Hrau
  iunfold kvAu at Hrau
  wp_apply (wp_Watch rw { akV a₁ ρ₁ R₁ with conn := rwconn, ics := rwics, wc := rwwc, lg := rwlg } ρ₁.rd.kv
      hctx ({ Values := ∅, Deadline := none, Done_gn := γhctx, PDone := iprop(True) } :
        context.ContextDesc (IProp GF)) none
      _ _ [withPrefixM, withRevM (W64 1)] (W64 1) (fun σ => iprop(⌜stateHistOk σ⌝)) 0) $$ []
    as %hch %γh ⟨#Hhsp, Hhcons, Hhcur⟩
  · iframe #
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply EtcdGrove.context.watchCtx_of_isContext; isplitl [] <;> iassumption
    isplitr
    · ipureintro; exact ⟨watch_all_ok.1, watch_all_ok.2, by decide⟩
    iintro !> %h
    exact absurd h.2 (Nat.lt_irrefl 0)
  ihave #Hhch := etcdstart.isRespChan_of_state hch _ γh _ (fun σ => iprop(⌜stateHistOk σ⌝)) _ $$ Hhsp
  (try wp_auto)
  -- `evs, ok := etcdstart.Collect(hch, end.Header.Revision)`: every event admitted (`root_resp`)
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
  wp_apply (wp_Collect (etcdstart.stateOk _ (fun σ => iprop(⌜stateHistOk σ⌝))) (fun _ _ => True)
      (fun _ e => iprop(⌜rootEvOk e⌝)) iprop(True) hch γh _ (W64 0) trivial (fun _ _ _ _ => inferInstance)
      (fun c c' v r => etcdstart.stateOk_closeErr _ _ c c' v r)
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
    as %uctx %γuctx %ucancel ⟨#Hucancel, #Huctx, -, #uctxFrom⟩
  ihave #uctxO := metadata.outgoingCtxOkC_bgFrom uctx $$ uctxFrom
  ihave #uctxM := metadata.outMD_bgFrom uctx $$ uctxFrom
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
    client.watcher_of_clientTokAt wp_ErrAny hAs ucl _ (akV a₂ ρ₂ R₂)
      (fun t => auth.tokIssued γa₂ t go!"u") rfl rfl rfl rfl $$ [Pcl Pctx Ppb Hunc HWF₂ Hutk]
  · iframe #
  (try wp_auto)
  ihave #Hrau₂ := akHist_readAu ρ₂.rd.kv $$ Hhist₂
  iunfold kvReadAu at Hrau₂
  iunfold kvAu at Hrau₂
  wp_apply (wp_Watch uw { akV a₂ ρ₂ R₂ with conn := uwconn, ics := uwics, wc := uwwc, lg := uwlg }
      ρ₂.rd.kv uctx ({ Values := ∅, Deadline := none, Done_gn := γuctx, PDone := iprop(True) } :
        context.ContextDesc (IProp GF)) none
      _ _ [withRangeM hi, withRevM (W64 1)] (W64 1) (fun σ => iprop(⌜stateHistOk σ⌝)) 0) $$ []
    as %uch %γu ⟨#Husp, Hucons, Hucur⟩
  · iframe #
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply EtcdGrove.context.watchCtx_of_isContext; isplitl [] <;> iassumption
    isplitr
    · ipureintro; exact ⟨watch_ab_ok.1.1, watch_ab_ok.1.2, by decide⟩
    iintro !> %h
    exact absurd h.2 (Nat.lt_irrefl 0)
  rw [OpFull.watchNorm_of_ne (opWatchModel lo [withRangeM hi, withRevM (W64 1)])
    (by rw [watch_ab_ok.2.1]; decide)]
  ihave #Huch := etcdstart.isRespChan_of_state uch _ γu _ (fun σ => iprop(⌜stateHistOk σ⌝)) _ $$ Husp
  (try wp_auto)
  -- `uevs, ok := etcdstart.Collect(uch, LastIn(evs))`
  wp_apply (wp_LastIn esl evs (DFrac.own 1)) $$ [Hes] as Hes
  · iframe; try iframe #
  ihave Hucons : etcdWatchConsumer γu 0 (W64 0) $$ [Hucons Hucur]
  · unfold etcdWatchConsumer
    iexists []
    rw [← h10]
    iframe Hucons Hucur
    ipureintro; rfl
  wp_apply (wp_Collect (etcdstart.stateOk _ (fun σ => iprop(⌜stateHistOk σ⌝))) (fun _ _ => True)
      (fun _ e => iprop(⌜permittedK go!"u" e.Key'⌝)) iprop(True) uch γu _ (W64 0) trivial
      (fun _ _ _ _ => inferInstance)
      (fun c c' v r => etcdstart.stateOk_closeErr _ _ c c' v r)
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
  ihave HU : (∃ (j : w64) (e0 : etcdstart.wev),
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

end etcd_auth3
end EtcdGrove
end Perennial
