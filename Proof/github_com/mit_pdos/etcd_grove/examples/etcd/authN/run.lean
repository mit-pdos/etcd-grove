/-
`run(srvs, ms, lg)` (`examples/etcd/authN/authN.go`; authN, `notes/authN-plan.md`, 2026-11-15):
**proved**, over its callees' specs. Lean-first (no Rocq counterpart). auth3's `run.wp_proof`
(`auth3/run.lean`) with loops over the `k` members:

- the serve loop: each member served by `serve_member` (auth3's, copied), the one thread token passed
  on to the next member; the served members' facts accumulate as a persistent big-sep (`srvd`);
- the set-up through member `0` (`SetUp`);
- the barrier loop: at each member, the set-up's facts carried to its names (`etcdstart.sameCluster`,
  `*_same`) and root's barrier read (`barrier`), giving `akAuthFixed` at that member's names; the
  members' facts accumulate as a persistent big-sep (`ready`);
- each principal's client and workload at its member's names, looked up in that big-sep: anon at
  member `0`, u and bad at member `1 mod k`, v at member `2 mod k` (`Work`);
- root's last write, history watch and `CheckHistory` through member `0`, u's watch through u's
  member, as in auth3's `run`.
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

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.authN.run
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.authN.newUserClient
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.authN.barrier
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.auth3.AuthFixed
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.MembersDefs

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_authN

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver etcd_auth etcdstart
open etcd_auth3 (admStates_same srvAuthAtLog_same srvRLogLb_same srvReqLogLb_same authHistFrozen_same
  akHistInv_same)

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **A member's clients' watch environment** (auth3's `akV`): one server, at its model and watch
facts with auth on, at the client address `addr`. -/
abbrev akV (addr : GoString) (ρ : ReqNames) (R : v3rpc.WSrv GF) : client.WEnv GF :=
  ⟨R, addr, [], null, null, go!"a", null, v3rpc.etcdModelOfServer R.E ρ.rd true,
    client.srvWL (etcdstart.srvWOf R.E ρ.rd true), fun _ => (addr, R), 1, ρ.rd.kv,
    etcdstart.srvWOf R.E ρ.rd true, fun _ => etcdstart.srvWOf R.E ρ.rd true⟩

end defs

section served
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [go_etcd_io.etcd.client.v3.Assumptions]

/-- **What serving a member's Lease service takes** (`serve_member`'s post): the premises of
`etcdstart.lease_served_on` past the packages' initializers and the id credential, at the server `s`
that `Serve` started on `addr` in lease mode `m`: the server's views in the mode on, its range check and
lessor reader side, the Lease service's registrations (`grpcLeaseUp`), the three unary interceptors and
the gRPC server they run in, the revocation loop built and the run pool. authN serves no Lease service
and drops it; authlease's `serve_member_lease` serves it from this. -/
def leaseReady (addr : GoString) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (m : lease.Mode) :
    IProp GF :=
  iprop(∃ (A : v3rpc.KVAns GF) (il im iu : GoFunc) (regs : List (GoString × GoFunc × GoInterface))
      (sms : List (GrpcStreamMethod GF)),
    ⌜A.revR = mvcc.api.mvccReaders E.γ 1⌝ ∗
    isServerReqM true s E ρ ∗ isServerReadM true s E ρ.rd ∗ srvAuthLb s E ∗ srvLeaseRd s E m ∗
    grpcLeaseUp s A regs ∗
    srvInterceptorOk il (srvLgReader s) v3rpc.learnerReqOk ∗
    srvInterceptorOk im iprop(True) v3rpc.learnerReqOk ∗
    srvInterceptorOk iu (levelTok 0) v3rpc.learnerReqOk ∗
    grpcServerAt addr [il, im, iu] regs etcdTys sms ∗ srvRevokeBuilt s E ∗ srvRunPool s E ρ.rd)

instance leaseReady_persistent (addr : GoString) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
    (m : lease.Mode) : Persistent (leaseReady addr s E ρ m) := by
  unfold leaseReady; infer_instance

/-- **A served member's facts** (`serve_member`'s post, at the witnesses): server `s` of member `x`
with auth on at `γa`, environment `E`, wait names `γw`, cluster and member ids `cid`/`mid`, watch
server `R`. -/
def srvdAt (s : Loc) (x : GMember × MemberG GF) (γa : auth.AuthNames) (E : apply.AEnv GF) (γw : GName)
    (cid mid : w64) (R : v3rpc.WSrv GF) : IProp GF :=
  iprop(⌜E.authMode = .on γa ∧ R.E = E ∧ R.s = s⌝ ∗ isServerReadM true s E x.2.ρ.rd ∗
    □ (srvTLSId s -∗ False) ∗ akKVOn x.1.Client' s E { x.2.ρ with wait := γw } cid mid ∗
    setupAuthServed x.1.Client' s E { x.2.ρ with wait := γw } ∗
    isGrpcRpc x.1.Client' authnMethod (client.etcdAuthenticateSpec γa) ∗
    watchAddrFacts (akV x.1.Client' x.2.ρ R) ∗ auth.modeTag R.tag (.on γa))

instance srvdAt_persistent (s : Loc) (x : GMember × MemberG GF) (γa : auth.AuthNames)
    (E : apply.AEnv GF) (γw : GName) (cid mid : w64) (R : v3rpc.WSrv GF) :
    Persistent (srvdAt s x γa E γw cid mid R) := by
  unfold srvdAt; infer_instance

/-- **A served member's witnesses**: its auth names, environment, wait names, cluster and member
ids, and watch server. -/
structure Wit (GF : BundledGFunctors) where
  γa : auth.AuthNames
  E : apply.AEnv GF
  γw : GName
  cid : w64
  mid : w64
  R : v3rpc.WSrv GF

/-- **A served member** (the serve loop's accumulated fact), at its witnesses. -/
abbrev srvdW (s : Loc) (x : GMember × MemberG GF) (w : Wit GF) : IProp GF :=
  srvdAt s x w.γa w.E w.γw w.cid w.mid w.R

/-- **A served member past the barrier** (the barrier loop's accumulated fact): the auth state fixed
after the set-up (requested log `Lset`) at its names. -/
def fixedW (Lset : List EntryModel) (x : GMember × MemberG GF) (w : Wit GF) : IProp GF :=
  iprop(∃ i : Nat, akAuthFixed w.γa { x.2.ρ with wait := w.γw } Lset i)

instance fixedW_persistent (Lset : List EntryModel) (x : GMember × MemberG GF) (w : Wit GF) :
    Persistent (fixedW Lset x w) := by
  unfold fixedW; infer_instance

/-- `c % k` at `k = len`, a positive length of at most 1000, as a signed index. -/
theorem mod_len_sint (len : w64) (L c : Nat) (hkl : uint.nat len = L) (hL : 0 < L) (hL' : L ≤ 1000)
    (hc : c < 2 ^ 32) : sint.Z (W64 (c : Int) % len) = ((c % L : Nat) : Int) := by
  subst hkl
  have hm := Nat.mod_lt c hL
  have h0 : (W64 (c : Int)).toNat = c := by simp [W64]; omega
  have h1 : (W64 (c : Int) % len).toNat = c % len.toNat := by rw [BitVec.toNat_umod, h0]
  have h2 : uint.nat len = len.toNat := rfl
  have hL2 : len.toNat ≤ 1000 := hL'
  have hm2 : c % len.toNat < len.toNat := hm
  have h3 : (W64 (c : Int) % len).toNat < 1000 := by rw [h1]; omega
  rw [h2, ← h1]
  generalize (W64 (c : Int) % len) = x at h3 ⊢
  word

/-- **A member served** (auth3's, copied; `Run`'s `Serve` step): `etcdstart.Serve(s, addr)` with the ghost steps
`ak_served_kv` and `ak_served_watch`; on success, the member's served facts at its environment and
the thread token (from the `GoAttach` resources `grpcUpOn` holds), and what serving its Lease service
in its lease mode `m` takes (`leaseReady`: authN's members are in mode `.none` and drop it; authlease's
`serve_member_lease` serves the Lease service of its `.revocable` members from it). -/
theorem serve_member [HasExt idIssueExt] [go_etcd_io.etcd.cache.v3.Assumptions]
    (wp_Serve : etcdstart.Serve.spec (GF := GF) (hG := hG))
    (wp_BcryptCost : auth.authStore.BcryptCost.spec (GF := GF) (hG := hG))
    (hP : mvcc.api.persistent.law (GF := GF))
    (hR : mvcc.api.mvccState_reachable.law (GF := GF))
    (s lg : Loc) (addr : GoString) (ρ : ReqNames) (E₀ : apply.AEnv GF) (γn : NetNames GF)
    (id : w64) (γa : auth.AuthNames) (m : lease.Mode)
    (Htb : threadBound GF ≤ 2 ^ 28) (HLv : srvLevels (GF := GF)) (Hrb48 : receiptBound GF ≤ 2 ^ 48)
    (Hbuq : apply.backendUnderQuota) (Hrf : grpcRepliesFit) (Hms : v3rpc.ServerMethodSets)
    (hlog : ρ.rd.kv.log0 = [[], []]) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗ client.eofOk ∗
        zapLoggerOk lg ∗ netAddrFree addr ∗ etcdstart.memberUpOn s ρ E₀ lg γn id γa m }}
      (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Serve)) (Val #s))
        (Val #addr))
    {{ (err : GoInterface), RET #err; ⌜err ≠ GoInterface.nil⌝ ∨
        (⌜err = GoInterface.nil⌝ ∗ threadTok ∗
          ∃ (E : apply.AEnv GF) (γw : GName) (cid mid : w64) (R : v3rpc.WSrv GF),
            ⌜E.authMode = .on γa ∧ R.E = E ∧ R.s = s⌝ ∗ isServerReadM true s E ρ.rd ∗
            □ (srvTLSId s -∗ False) ∗ akKVOn addr s E { ρ with wait := γw } cid mid ∗
            setupAuthServed addr s E { ρ with wait := γw } ∗
            isGrpcRpc addr authnMethod (client.etcdAuthenticateSpec γa) ∗
            watchAddrFacts (akV addr ρ R) ∗ auth.modeTag R.tag (.on γa) ∗
            leaseReady addr s E { ρ with wait := γw } m) }} := by
  iintro %Φ ⟨#Pst, #Psrv, #Pv3, #Ppb, #Heo, #Hlgz, Haddr, Hup⟩ HΦ
  icases etcdstart.memberUpOn_served _ _ _ _ _ _ _ m $$ Hup with ⟨%E, %cfg, %γw, %HE, #Hreq, #Hrd0,
    #Hlb, #Hsf, Hgo, Hlg3, Hbemu, #Hwb, Hstk, -, #Htls, #HBF, #Hlr⟩
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
        watchAddrFacts (akV addr ρ R) ∗ auth.modeTag R.tag E.authMode ∗ srvGoRes s ∗
        leaseReady addr s E { ρ with wait := γw } m)))
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
      Hlis, Hleft, #Hlu⟩
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
      $$ [Hgsn Hlis Hleft] with ⟨Hserv, #Hss, #HKV, #HSA, #HAu, #Hsat⟩
    · iframe; iframe #
      iintro !>
      imodintro
      iunfold idCred
      ipureintro; exact Hrb48
    imod (ak_served_watch hP (akV addr ρ R) addr pw s E ρ.rd rfl hRE hRs
        (by simp) (kvSame_refl _) hlog (by omega) rfl rfl rfl rfl)
      $$ [] with ⟨#HWF, #Htag⟩
    · iframe; iframe #
    -- what serving the Lease service in lease mode `m` takes (`leaseReady`)
    ihave #Hil' := Hil $$ %v3rpc.learnerReqOk
    ihave #Him' := Him $$ %v3rpc.learnerReqOk
    ihave #Hreq' : isServerReqM true s E { ρ with wait := γw } $$ []
    · rw [← hon]; iexact Hreq
    ihave #Hrd' : isServerReadM true s E ρ.rd $$ []
    · rw [← hon]; iexact Hrd0
    ihave #HLS : leaseReady addr s E { ρ with wait := γw } m $$ []
    · iunfold leaseReady
      iexists C.A, il, im, iu, regs, _
      isplitl []
      · ipureintro; rw [HCA]; rfl
      rw [HCA]
      iframe #
    imodintro
    iframe HKV HSA HAu HWF Htag Hgr HLS
    isplitl [Hserv]
    · iexists _; iexact Hserv
    ipureintro; exact ⟨hRE, hRs⟩
  iapply HΦ
  icases Hs with (%Hserr | ⟨%Hserr, %cid, %mid, %R, ⟨%HRQ, #HKV, #HSA, #HAu, #HWF, #Htag, Hgr, #HLS⟩⟩)
  · ileft; ipureintro; exact Hserr
  iright
  iunfold srvGoRes at Hgr
  icases Hgr with ⟨-, Htok⟩
  iframe Htok
  isplitl []
  · ipureintro; exact Hserr
  iexists E, γw, cid, mid, R
  rw [← hon]
  iframe HKV HSA HAu HWF Hrd0 Htls HLS
  isplitl []
  · ipureintro; exact ⟨HEo, HRQ⟩
  rw [← HEo]; iexact Htag


end served

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.authN.Assumptions]

set_option maxHeartbeats 3200000 in
set_option maxRecDepth 10000 in
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
  intro CS ES FS RS srvsl msl lg ss xs x0 γn hx0 hxl Hpe Htb HLv Hrb48 Hbuq Hrf Hms hAs hc0
    hlog hsc
  have Htb31 : threadBound GF ≤ 2 ^ 31 := by omega
  have hk1 : 1 ≤ xs.length := by
    cases xs with
    | nil => simp at hx0
    | cons _ _ => simp
  have hlogx : ∀ x ∈ xs, x.2.ρ.rd.kv.log0 = [[], []] := fun x hx => by rw [(hsc x hx).2.2.2.1, hlog]
  wp_start as ⟨#Hlgz, Hss, #Hmsl, Htok, Hcfree, Hups, #Hhist, Hview⟩
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
  ihave %Hupl := BigSepL2.bigSepL2_length $$ Hups
  ihave %Hssl := ownSlice_len $$ Hss
  ihave %Hmsll := ownSlice_len $$ Hmsl
  have hkl : uint.nat msl.len = xs.length := by have := Hmsll.1; simp at this; word
  have Hb0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z msl.len := by
    have := Hmsll.1; simp at this; constructor <;> word
  have hm0 : (xs.map (·.1))[(sint.Z (W64 0)).toNat]? = some x0.1 := by
    rw [show (sint.Z (W64 0)).toNat = 0 from rfl, List.getElem?_map, hx0]; rfl
  have hk0 : ¬ (uint.Z msl.len = 0) := by word
  -- (for `run`'s indexing) u's member `1 % k`, v's member `2 % k`
  have hmodZ := fun c hc => mod_len_sint msl.len xs.length c hkl (by omega) hxl hc
  obtain ⟨xu, hxu⟩ : ∃ x, xs[1 % xs.length]? = some x :=
    ⟨_, List.getElem?_eq_getElem (Nat.mod_lt _ (by omega))⟩
  obtain ⟨xv, hxv⟩ : ∃ x, xs[2 % xs.length]? = some x :=
    ⟨_, List.getElem?_eq_getElem (Nat.mod_lt _ (by omega))⟩
  have hmsZ : sint.Z msl.len = (xs.length : Int) := by have := Hmsll.1; simp at this; word
  have hu : sint.Z (W64 1 % msl.len) = ((1 % xs.length : Nat) : Int) := hmodZ 1 (by omega)
  have hv : sint.Z (W64 2 % msl.len) = ((2 % xs.length : Nat) : Int) := hmodZ 2 (by omega)
  have Hbu : 0 ≤ sint.Z (W64 1 % msl.len) ∧ sint.Z (W64 1 % msl.len) < sint.Z msl.len := by
    rw [hu, hmsZ]; have := Nat.mod_lt 1 (by omega : xs.length > 0); omega
  have Hbv : 0 ≤ sint.Z (W64 2 % msl.len) ∧ sint.Z (W64 2 % msl.len) < sint.Z msl.len := by
    rw [hv, hmsZ]; have := Nat.mod_lt 2 (by omega : xs.length > 0); omega
  have hmu : (xs.map (·.1))[(sint.Z (W64 1 % msl.len)).toNat]? = some xu.1 := by
    rw [hu, Int.toNat_natCast, List.getElem?_map, hxu]; rfl
  have hmv : (xs.map (·.1))[(sint.Z (W64 2 % msl.len)).toNat]? = some xv.1 := by
    rw [hv, Int.toNat_natCast, List.getElem?_map, hxv]; rfl
  imod ownSlice_persist _ _ _ $$ Hss with #Hss
  (try wp_auto)
  -- the serve loop: `for j, m := range ms { if err := Serve(srvs[j], m.Client); err != nil { return
  -- Failed } }`, the thread token from member to member
  ihave IH : (∃ (n jv : w64) (mv : GMember) (ws : List (Wit GF)),
      "i" ∷ i_ptr ↦ n ∗ "j" ∷ j_ptr ↦ jv ∗ "m" ∷ m_ptr ↦ mv ∗ "Htok" ∷ threadTok ∗
      "Hups" ∷ ([∗list] s; x ∈ ss.drop (sint.nat n); xs.drop (sint.nat n),
        (threadTok -∗ ∃ γa : auth.AuthNames, etcdstart.memberUpOn s x.2.ρ x.2.E lg γn x.2.id γa)) ∗
      "Hcfree" ∷ ([∗list] x ∈ xs.drop (sint.nat n), netAddrFree (GF := GF) x.1.Client') ∗
      "#Hsv" ∷ ([∗list] q ∈ ((ss.zip xs).take (sint.nat n)).zip ws, srvdW q.1.1 q.1.2 q.2) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ xs.length ∧ ws.length = sint.nat n⌝ : IProp GF)
      $$ [i j m Htok Hups Hcfree]
  · iexists W64 0, _, _, []
    have h00 : sint.nat (W64 0) = 0 := rfl
    simp only [h00, List.drop_zero, List.take_zero, List.zip_nil_left]
    iframe
    isplitl
    · iapply BigSepL.bigSepL_nil.2; itrivial
    ipureintro; exact ⟨by decide, by omega, rfl⟩
  wp_for IH
  wp_if_destruct
  · have hlt : sint.nat n < xs.length := by have := Hmsll.1; simp at this; word
    list_elem ss (sint.nat n) as sj
    list_elem xs (sint.nat n) as xj
    have hnz : (sint.Z n).toNat = sint.nat n := by word
    have Hbm : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z msl.len := ⟨Hn.1, Hif⟩
    have Hbs : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z srvsl.len := ⟨Hn.1, by have := Hssl.1; word⟩
    (try wp_auto)
    simp only [Hbm, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index msl (sint.Z n) _ _ xj.1 Hbm.1 $$ [Hmsl] as -
    · iframe #; ipureintro; rw [hnz, List.getElem?_map, Hxj_lookup]; rfl
    (try wp_auto)
    simp only [Hbs, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index srvsl (sint.Z n) _ _ sj Hbs.1 $$ [Hss] as -
    · iframe #; ipureintro; rw [hnz]; exact Hsj_lookup
    (try wp_auto)
    -- the member's `memberUpOn`, the token given to it
    isimp only [drop_cons_of_getElem? ss _ sj Hsj_lookup, drop_cons_of_getElem? xs _ xj Hxj_lookup] at Hups
    ihave Hups := BigSepL2.bigSepL2_cons.1 $$ Hups
    icases Hups with ⟨Hupj, Hups⟩
    ihave ⟨%γa, Hupj⟩ := Hupj $$ Htok
    isimp only [drop_cons_of_getElem? xs _ xj Hxj_lookup] at Hcfree
    ihave Hcfree := BigSepL.bigSepL_cons.1 $$ Hcfree
    icases Hcfree with ⟨Hcj, Hcfree⟩
    have hxj : xj ∈ xs := List.mem_of_getElem? Hxj_lookup
    wp_apply (serve_member wp_Serve wp_BcryptCost hP hR sj lg xj.1.Client' xj.2.ρ xj.2.E γn xj.2.id γa
        .none Htb HLv Hrb48 Hbuq Hrf Hms (hlogx xj hxj)) $$ [Hcj Hupj] as %serr Hs
    · iframe; iframe #
    icases Hs with (%Hserr | ⟨%Hserr, Htok, %E, %γw, %cid, %mid, %R, %HR, #Hrd, #Htls,
      #HKV, #HSA, #HAu, #HWF, #Htag, -⟩)
    · cases serr with
      | nil => exact absurd rfl Hserr
      | ok ei => ?_
      (try wp_auto)
      wp_for_post
      iapply HΦ; ipureintro; right; left; rfl
    subst Hserr
    (try wp_auto)
    have hzj : (ss.zip xs)[sint.nat n]? = some (sj, xj) :=
      List.getElem?_zip_eq_some.2 ⟨Hsj_lookup, Hxj_lookup⟩
    have htl : ((ss.zip xs).take (sint.nat n)).length = ws.length := by
      rw [List.length_take, List.length_zip, Hupl, Hn.2.2]; omega
    have hzz : ((ss.zip xs).take (sint.nat n + 1)).zip (ws ++ [⟨γa, E, γw, cid, mid, R⟩]) =
        ((ss.zip xs).take (sint.nat n)).zip ws ++ [((sj, xj), ⟨γa, E, γw, cid, mid, R⟩)] := by
      rw [List.take_add_one, hzj, Option.toList_some, List.zip_append htl]; rfl
    ihave #Hsv' : [∗list] q ∈ ((ss.zip xs).take (sint.nat n + 1)).zip (ws ++ [⟨γa, E, γw, cid, mid, R⟩]),
        srvdW q.1.1 q.1.2 q.2 $$ []
    · rw [hzz]
      iapply BigSepL.bigSepL_snoc.2
      iframe #
      iunfold srvdW
      iunfold srvdAt
      iframe #
      ipureintro; exact HR
    iclear Hsv
    wp_for_post
    iframe
    have hn1 : sint.nat (n + W64 1) = sint.nat n + 1 := by word
    iexists n + W64 1, n, xj.1, ws ++ [⟨γa, E, γw, cid, mid, R⟩]
    rw [hn1]
    iframe
    iframe #
    ipureintro; exact ⟨by word, by omega, by simp [Hn.2.2]⟩
  -- every member served
  have hnk : sint.nat n = xs.length := by have := Hmsll.1; simp at this; word
  have hwl : ws.length = xs.length := by rw [Hn.2.2, hnk]
  ihave #Hsv : [∗list] q ∈ (ss.zip xs).zip ws, srvdW q.1.1 q.1.2 q.2 $$ []
  · iExactEq Hsv; rw [hnk, List.take_of_length_le (by simp [Hupl])]
  iclear Hups Hcfree
  -- `a0 := ms[0].Client`, `au := ms[1%k].Client`, `av := ms[2%k].Client`
  simp only [Hb0, _root_.and_self, ↓reduceIte]
  icases ownSlice_elem_acc _ _ _ _ _ Hb0.1 hm0 $$ Hmsl with ⟨#Hm0, -⟩
  iStructNamedSuffix Hm0 "_m0"
  (try wp_auto)
  simp only [hk0, ↓reduceIte]
  (try wp_auto)
  simp only [Hbu, _root_.and_self, ↓reduceIte]
  icases ownSlice_elem_acc _ _ _ _ _ Hbu.1 hmu $$ Hmsl with ⟨#Hmu, -⟩
  iStructNamedSuffix Hmu "_mu"
  (try wp_auto)
  simp only [hk0, ↓reduceIte]
  (try wp_auto)
  simp only [Hbv, _root_.and_self, ↓reduceIte]
  icases ownSlice_elem_acc _ _ _ _ _ Hbv.1 hmv $$ Hmsl with ⟨#Hmv, -⟩
  iStructNamedSuffix Hmv "_mv"
  (try wp_auto)
  -- member 0's served facts (its witnesses `w0`), u's member's and v's member's witnesses
  have hx0m : x0 ∈ xs := List.mem_of_getElem? hx0
  have hxum : xu ∈ xs := List.mem_of_getElem? hxu
  have hxvm : xv ∈ xs := List.mem_of_getElem? hxv
  have hzl : ((ss.zip xs).zip ws).length = xs.length := by simp [Hupl, hwl]
  have hgz : ∀ (i : Nat) (x : GMember × MemberG GF), xs[i]? = some x →
      ∃ s w, ((ss.zip xs).zip ws)[i]? = some ((s, x), w) := by
    intro i x hx
    have hi : i < xs.length := (List.getElem?_eq_some_iff.1 hx).1
    obtain ⟨s, hs⟩ : ∃ s, ss[i]? = some s := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨w, hw⟩ : ∃ w, ws[i]? = some w := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    exact ⟨s, w, List.getElem?_zip_eq_some.2 ⟨List.getElem?_zip_eq_some.2 ⟨hs, hx⟩, hw⟩⟩
  obtain ⟨s0, w0, hy0⟩ := hgz 0 x0 hx0
  obtain ⟨su, wu, hyu⟩ := hgz _ xu hxu
  obtain ⟨sv, wv, hyv⟩ := hgz _ xv hxv
  ihave #H0' := BigSepL.bigSepL_lookup hy0 $$ Hsv
  ihave #H0 : srvdW s0 x0 w0 $$ []
  · iexact H0'
  iclear H0'
  iunfold srvdW at H0
  iunfold srvdAt at H0
  icases H0 with ⟨%HR₁, #Hrd₁, #Htls₁, #HKV₁, #HSA₁, #HAu₁, #HWF₁, #Htag₁⟩
  -- `NewClient(a1, lg)`: the client with no user name, at member 0
  icases (threadTok_level0 (GF := GF)).1 $$ Htok with ⟨Hlt, -⟩
  wp_apply (wp_NewClient x0.1.Client' lg (akV x0.1.Client' x0.2.ρ w0.R) (Hpe x0 hx0m) (by omega)) $$ [$Hlt] as %cl %cerr ⟨Hlt, Hcl⟩
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
  -- `SetUp(cli)` through member 0
  ihave #Hsau : iprop(□ ∀ k : GoString, ⌜k ∈ setupKeys⌝ -∗
      kvOpAu1 x0.2.ρ.rd.kv (.put (client.putKeyOp k go!"setup")) (fun _ => iprop(True))) $$ []
  · iintro !> %k %hk
    ihave #H := akHist_setupAu x0.2.ρ.rd.kv k hk $$ Hhist
    iexact H
  ihave #Hput : isGrpcRpcMd x0.1.Client' go!"/etcdserverpb.KV/Put"
      (client.etcdPutSpecOn (srvTLSId s0) w0.E { x0.2.ρ with wait := w0.γw } w0.cid w0.mid) $$ []
  · iunfold akKVOn at HKV₁
    icases HKV₁ with ⟨#H, -, -, -⟩
    iexact H
  wp_apply (wp_SetUp cl x0.1.Client' (akV x0.1.Client' x0.2.ρ w0.R) s0 w0.E { x0.2.ρ with wait := w0.γw } w0.cid w0.mid w0.γa HR₁.1
      (by show uint.Z x0.2.ρ.rd.kv.c0 ≤ uint.Z x0.2.ρ.rd.raft.ai0; rw [hc0]; word) hAs)
    $$ [$Hlt Hview] as %ok ⟨Hlt, Hok⟩
  · iframe; iframe #
  cases ok
  · wp_auto
    iapply HΦ; ipureintro; right; left; rfl
  rw [ite_eq_left rfl]
  icases Hok with ⟨%γz, %hs, %Lset, %kpub, %rset, #Hfz, #Hllb, %Hadm, -, -, %Lc, #HLc,
    %HLcst⟩
  (try wp_auto)
  -- the barrier loop: `for _, m := range ms { if !barrier(m.Client, lg) { return Failed } }`, each
  -- member's auth state fixed after the set-up, at its witnesses
  ihave IB : (∃ (n : w64) (mv : GMember),
      "i" ∷ i_ptr ↦ n ∗ "m" ∷ m_ptr ↦ mv ∗
      "#Hfx" ∷ ([∗list] q ∈ ((ss.zip xs).zip ws).take (sint.nat n), fixedW Lset q.1.2 q.2) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ xs.length⌝ : IProp GF) $$ [i m]
  · iexists W64 0, _
    have h00 : sint.nat (W64 0) = 0 := rfl
    simp only [h00, List.take_zero]
    iframe
    isplitl
    · iapply BigSepL.bigSepL_nil.2; itrivial
    ipureintro; exact ⟨by decide, by omega⟩
  wp_for IB
  wp_if_destruct
  · have hlt : sint.nat n < xs.length := by have := Hmsll.1; simp at this; word
    list_elem xs (sint.nat n) as xj
    obtain ⟨sj, wj, hyj⟩ := hgz _ xj Hxj_lookup
    have hxj : xj ∈ xs := List.mem_of_getElem? Hxj_lookup
    have hsj := hsc xj hxj
    have hnz : (sint.Z n).toNat = sint.nat n := by word
    have Hbm : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z msl.len := ⟨Hn.1, Hif⟩
    have Hadmj := Hadm
    rw [← admStates_same { x0.2.ρ with wait := w0.γw } { xj.2.ρ with wait := wj.γw } hsj,
      ← srvAuthAtLog_same { x0.2.ρ with wait := w0.γw } { xj.2.ρ with wait := wj.γw } hsj] at Hadmj
    have HLcstj := HLcst
    rw [← srvAuthAtLog_same { x0.2.ρ with wait := w0.γw } { xj.2.ρ with wait := wj.γw } hsj] at HLcstj
    (try wp_auto)
    simp only [Hbm, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index msl (sint.Z n) _ _ xj.1 Hbm.1 $$ [Hmsl] as -
    · iframe #; ipureintro; rw [hnz, List.getElem?_map, Hxj_lookup]; rfl
    (try wp_auto)
    -- the member's served facts, the set-up's facts at its names
    ihave #Hj' := BigSepL.bigSepL_lookup hyj $$ Hsv
    ihave #Hj : srvdW sj xj wj $$ []
    · iexact Hj'
    iclear Hj'
    iunfold srvdW at Hj
    iunfold srvdAt at Hj
    icases Hj with ⟨%HRj, #Hrdj, -, #HKVj, -, #HAuj, -, -⟩
    ihave #Hfzj := authHistFrozen_same { x0.2.ρ with wait := w0.γw } { xj.2.ρ with wait := wj.γw } hsj γz hs
      $$ Hfz
    ihave #Hllbj := srvReqLogLb_same { x0.2.ρ with wait := w0.γw } { xj.2.ρ with wait := wj.γw } hsj Lset
      $$ Hllb
    ihave #HLcj := srvRLogLb_same { x0.2.ρ with wait := w0.γw } { xj.2.ρ with wait := wj.γw } hsj Lc $$ HLc
    wp_apply (wp_barrier xj.1.Client' lg (akV xj.1.Client' xj.2.ρ wj.R) sj wj.E { xj.2.ρ with wait := wj.γw }
        wj.cid wj.mid wj.γa γz hs Lset Lc rset (Hpe xj hxj) (by omega) HRj.1 hAs) $$ [$Hlt] as %okj ⟨Hlt, Hbj⟩
    · iframe #; ipureintro; exact ⟨Hadmj, HLcstj⟩
    icases Hbj with (%Hb | ⟨%Hb, %ij, #Hfixj⟩) <;> subst Hb
    · (try wp_auto)
      wp_for_post
      iapply HΦ; ipureintro; right; left; rfl
    (try wp_auto)
    have htk : ((ss.zip xs).zip ws).take (sint.nat n + 1) =
        ((ss.zip xs).zip ws).take (sint.nat n) ++ [((sj, xj), wj)] := by
      rw [List.take_add_one, hyj, Option.toList_some]
    ihave #Hfx' : [∗list] q ∈ ((ss.zip xs).zip ws).take (sint.nat n + 1), fixedW Lset q.1.2 q.2 $$ []
    · rw [htk]
      iapply BigSepL.bigSepL_snoc.2
      iframe #
      iunfold fixedW
      iexists ij; iexact Hfixj
    iclear Hfx
    wp_for_post
    iframe
    have hn1 : sint.nat (n + W64 1) = sint.nat n + 1 := by word
    iexists n + W64 1, xj.1
    rw [hn1]
    iframe
    iframe #
    ipureintro; exact ⟨by word, by omega⟩
  -- every member past the barrier
  have hnk' : sint.nat n = xs.length := by have := Hmsll.1; simp at this; word
  ihave #Hfx : [∗list] q ∈ (ss.zip xs).zip ws, fixedW Lset q.1.2 q.2 $$ []
  · iExactEq Hfx; rw [hnk', List.take_of_length_le (by omega)]
  -- the principals' members' facts: member 0's, u's member's (`1 % k`), v's member's (`2 % k`)
  ihave #F0' := BigSepL.bigSepL_lookup hy0 $$ Hfx
  ihave #F0 : fixedW Lset x0 w0 $$ []
  · iexact F0'
  iclear F0'
  iunfold fixedW at F0
  icases F0 with ⟨%i₁, #Hfix₁⟩
  ihave #Hu' := BigSepL.bigSepL_lookup hyu $$ Hsv
  ihave #Hu : srvdW su xu wu $$ []
  · iexact Hu'
  iclear Hu'
  iunfold srvdW at Hu
  iunfold srvdAt at Hu
  icases Hu with ⟨%HR₂, -, #Htls₂, #HKV₂, -, #HAu₂, #HWF₂, #Htag₂⟩
  ihave #Fu' := BigSepL.bigSepL_lookup hyu $$ Hfx
  ihave #Fu : fixedW Lset xu wu $$ []
  · iexact Fu'
  iclear Fu'
  iunfold fixedW at Fu
  icases Fu with ⟨%i₂, #Hfix₂⟩
  ihave #Hv' := BigSepL.bigSepL_lookup hyv $$ Hsv
  ihave #Hv : srvdW sv xv wv $$ []
  · iexact Hv'
  iclear Hv'
  iunfold srvdW at Hv
  iunfold srvdAt at Hv
  icases Hv with ⟨%HR₃, -, #Htls₃, #HKV₃, -, #HAu₃, #HWF₃, #Htag₃⟩
  ihave #Fv' := BigSepL.bigSepL_lookup hyv $$ Hfx
  ihave #Fv : fixedW Lset xv wv $$ []
  · iexact Fv'
  iclear Fv'
  iunfold fixedW at Fv
  icases Fv with ⟨%i₃, #Hfix₃⟩
  ihave #Hhistu := akHistInv_same x0.2.ρ xu.2.ρ (hsc xu hxum) $$ Hhist
  ihave #Hhistv := akHistInv_same x0.2.ρ xv.2.ρ (hsc xv hxvm) $$ Hhist
  -- the clients: root at member 0, u at member `1 % k`, v at member `2 % k`, the one with no token at
  -- member `1 % k`
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #Hall : client.ctxErrClientAll (GF := GF) $$ []
  · ihave #Hw := client.ctxErrClientAllW_of wp_ErrAny hAs $$ Pctx
    iunfold client.ctxErrClientAllW at Hw
    iunfold client.ctxErrClientAll
    iexact Hw
  wp_apply (wp_newUserClient x0.1.Client' go!"root" go!"root-pw" lg (akV x0.1.Client' x0.2.ρ w0.R)
      (fun t => auth.tokIssued w0.γa t go!"root") (Hpe x0 hx0m) (by omega) (by unfold strsSizeOk; decide))
    $$ [$Hlt] as %rcl %rerr ⟨Hlt, Hrc⟩
  · iframe #
    iapply (client.authTokReg_of _ _ _ w0.γa)
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
  wp_apply (wp_newUserClient xu.1.Client' go!"u" go!"u-pw" lg (akV xu.1.Client' xu.2.ρ wu.R)
      (fun t => auth.tokIssued wu.γa t go!"u") (Hpe xu hxum) (by omega) (by unfold strsSizeOk; decide))
    $$ [$Hlt] as %ucl %uerr ⟨Hlt, Huc⟩
  · iframe #
    iapply (client.authTokReg_of _ _ _ wu.γa)
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
  wp_apply (wp_newUserClient xv.1.Client' go!"v" go!"v-pw" lg (akV xv.1.Client' xv.2.ρ wv.R)
      (fun t => auth.tokIssued wv.γa t go!"v") (Hpe xv hxvm) (by omega) (by unfold strsSizeOk; decide))
    $$ [$Hlt] as %vcl %verr ⟨Hlt, Hvc⟩
  · iframe #
    iapply (client.authTokReg_of _ _ _ wv.γa)
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
  wp_apply (wp_NewClient xu.1.Client' lg (akV xu.1.Client' xu.2.ρ wu.R) (Hpe xu hxum) (by omega)) $$ [$Hlt] as %bcl %berr ⟨Hlt, Hbc⟩
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
      wp_apply wp_fork_level0 $$ [Hdone who c]
      · iintro Hlt
        (try wp_auto)
        first
        | (wp_apply (wp_Work _ _ xu.1.Client' (akV xu.1.Client' xu.2.ρ wu.R) su wu.E { xu.2.ρ with wait := wu.γw } wu.cid wu.mid wu.γa
              Lset i₂ hwho HR₂.1 ⟨rfl, rfl, rfl, rfl, HR₂.2.2, HR₂.2.1, rfl⟩ hAs) $$ [$Hlt] as ⟨Hlt, -⟩
           · iframe #
             rw [akTokP, ite_eq_left (Or.inl rfl)]; iexact Hutk
           (try wp_auto)
           wp_apply (sync.join.WaitGroup.wp_Done_of sync.WaitGroup.wp_Done iprop(True) wg_ptr)
             $$ [Hdone]
           · iframe
           iframe Hlt; try itrivial)
        | (wp_apply (wp_Work _ _ xv.1.Client' (akV xv.1.Client' xv.2.ρ wv.R) sv wv.E { xv.2.ρ with wait := wv.γw } wv.cid wv.mid wv.γa
              Lset i₃ hwho HR₃.1 ⟨rfl, rfl, rfl, rfl, HR₃.2.2, HR₃.2.1, rfl⟩ hAs) $$ [$Hlt] as ⟨Hlt, -⟩
           · iframe #
             rw [akTokP, ite_eq_left (Or.inr rfl)]; iexact Hvtk
           (try wp_auto)
           wp_apply (sync.join.WaitGroup.wp_Done_of sync.WaitGroup.wp_Done iprop(True) wg_ptr)
             $$ [Hdone]
           · iframe
           iframe Hlt; try itrivial)
        | (wp_apply (wp_Work _ _ xu.1.Client' (akV xu.1.Client' xu.2.ρ wu.R) su wu.E { xu.2.ρ with wait := wu.γw } wu.cid wu.mid wu.γa
              Lset i₂ hwho HR₂.1 ⟨rfl, rfl, rfl, rfl, HR₂.2.2, HR₂.2.1, rfl⟩ hAs) $$ [$Hlt] as ⟨Hlt, -⟩
           · iframe #
             rw [akTokP, ite_eq_right (fun h => h.elim ‹_› ‹_›)]; iexact Hbtk
           (try wp_auto)
           wp_apply (sync.join.WaitGroup.wp_Done_of sync.WaitGroup.wp_Done iprop(True) wg_ptr)
             $$ [Hdone]
           · iframe
           iframe Hlt; try itrivial)
        | (wp_apply (wp_Work _ _ x0.1.Client' (akV x0.1.Client' x0.2.ρ w0.R) s0 w0.E { x0.2.ρ with wait := w0.γw } w0.cid w0.mid w0.γa
              Lset i₁ hwho HR₁.1 ⟨rfl, rfl, rfl, rfl, HR₁.2.2, HR₁.2.1, rfl⟩ hAs) $$ [$Hlt] as ⟨Hlt, -⟩
           · iframe #
             rw [akTokP, ite_eq_right (fun h => h.elim ‹_› ‹_›)]; iexact Hctk
           (try wp_auto)
           wp_apply (sync.join.WaitGroup.wp_Done_of sync.WaitGroup.wp_Done iprop(True) wg_ptr)
             $$ [Hdone]
           · iframe
           iframe Hlt; try itrivial)
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
  ihave #Hend := akHist_endAu x0.2.ρ.rd.kv go!"end" $$ Hhist
  imod v3rpc.kvLogLb_nil (GF := GF) w0.E.γs with #HF0
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
  wp_apply (client_Put_on rcl rapi rconn x0.1.Client' s0 w0.E { x0.2.ρ with wait := w0.γw } w0.cid w0.mid
      ectx eom ecd endKey go!"end" slice.nil (fun _ => iprop(True)) []
      (opSizeOk_opPutModel (K := 2 ^ 28) (E := 0) (V := 2 ^ 28) (optsKeep_nil _ _ _) (by decide)
        (by decide) (by decide))) $$ [$Hlt] as %eresp %eerr ⟨Hlt, Hend'⟩
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
    client.watcher_of_clientTokAt wp_ErrAny hAs rcl _ (akV x0.1.Client' x0.2.ρ w0.R)
      (fun t => auth.tokIssued w0.γa t go!"root") rfl rfl rfl rfl $$ [Pcl Pctx Ppb Hrnc HWF₁ Hrtk]
  · iframe #
  (try wp_auto)
  ihave #Hrau := akHist_readAu x0.2.ρ.rd.kv $$ Hhist
  iunfold kvReadAu at Hrau
  iunfold kvAu at Hrau
  wp_apply (wp_Watch rw { akV x0.1.Client' x0.2.ρ w0.R with conn := rwconn, ics := rwics, wc := rwwc, lg := rwlg } x0.2.ρ.rd.kv
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
    client.watcher_of_clientTokAt wp_ErrAny hAs ucl _ (akV xu.1.Client' xu.2.ρ wu.R)
      (fun t => auth.tokIssued wu.γa t go!"u") rfl rfl rfl rfl $$ [Pcl Pctx Ppb Hunc HWF₂ Hutk]
  · iframe #
  (try wp_auto)
  ihave #Hrauu := akHist_readAu xu.2.ρ.rd.kv $$ Hhistu
  iunfold kvReadAu at Hrauu
  iunfold kvAu at Hrauu
  wp_apply (wp_Watch uw { akV xu.1.Client' xu.2.ρ wu.R with conn := uwconn, ics := uwics, wc := uwwc, lg := uwlg }
      xu.2.ρ.rd.kv uctx ({ Values := ∅, Deadline := none, Done_gn := γuctx, PDone := iprop(True) } :
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
  · have Hlt : sint.Z j < sint.Z usl.len := by
      exact Hif
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

end etcd_authN
end EtcdGrove
end Perennial
