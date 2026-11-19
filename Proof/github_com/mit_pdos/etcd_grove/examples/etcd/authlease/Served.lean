/-
**authlease's served members** (auth-lease S4, item 9): authN's `serve_member` with the member's Lease
service with auth on (`etcdstart.lease_served_on`, the member in the revocable lease mode), and the serve
loop's accumulated fact (authN's `srvdAt`, the Lease service added). authN's `Wit`, `fixedW`, `akV` and
`mod_len_sint` are reused. Lean-first (no Rocq counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.authN.run
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.ServedLeaseOnLinked

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_authlease

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver etcd_auth etcdstart
open etcd_authN (Wit akV mod_len_sint fixedW)

section served
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [go_etcd_io.etcd.client.v3.Assumptions]

/-- **A served member's facts** (`serve_member_lease`'s post, at the witnesses): server `s` of member `x`
with auth on at `γa`, environment `E`, wait names `γw`, cluster and member ids `cid`/`mid`, watch
server `R`. -/
def srvdAt (s : Loc) (x : GMember × MemberG GF) (γa : auth.AuthNames) (E : apply.AEnv GF) (γw : GName)
    (cid mid : w64) (R : v3rpc.WSrv GF) : IProp GF :=
  iprop(⌜E.authMode = .on γa ∧ R.E = E ∧ R.s = s⌝ ∗ isServerReadM true s E x.2.ρ.rd ∗
    □ (srvTLSId s -∗ False) ∗ akKVOn x.1.Client' s E { x.2.ρ with wait := γw } cid mid ∗
    setupAuthServed x.1.Client' s E { x.2.ρ with wait := γw } ∗
    isGrpcRpc x.1.Client' authnMethod (client.etcdAuthenticateSpec γa) ∗
    watchAddrFacts (akV x.1.Client' x.2.ρ R) ∗ auth.modeTag R.tag (.on γa) ∗
    etcdstart.etcdLeaseServedOn x.1.Client' s E { x.2.ρ with wait := γw })

instance srvdAt_persistent (s : Loc) (x : GMember × MemberG GF) (γa : auth.AuthNames)
    (E : apply.AEnv GF) (γw : GName) (cid mid : w64) (R : v3rpc.WSrv GF) :
    Persistent (srvdAt s x γa E γw cid mid R) := by
  unfold srvdAt; infer_instance

/-- **A served member** (the serve loop's accumulated fact), at its witnesses. -/
abbrev srvdW (s : Loc) (x : GMember × MemberG GF) (w : Wit GF) : IProp GF :=
  srvdAt s x w.γa w.E w.γw w.cid w.mid w.R

end served

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **A member served, its Lease service with auth on too** (authN's `serve_member`, the lease part added;
`run`'s `Serve` step): `etcdstart.Serve(s, addr)` with the ghost steps `ak_served_kv`, `ak_served_watch`
and `etcdstart.lease_served_on` (the member in the revocable lease mode); on success, the member's served
facts at its environment and the thread token. -/
theorem serve_member_lease [go_etcd_io.etcd.cache.v3.Assumptions]
    (wp_Serve : etcdstart.Serve.spec (GF := GF) (hG := hG))
    (wp_BcryptCost : auth.authStore.BcryptCost.spec (GF := GF) (hG := hG))
    (hP : mvcc.api.persistent.law (GF := GF))
    (hR : mvcc.api.mvccState_reachable.law (GF := GF))
    (s lg : Loc) (addr : GoString) (ρ : ReqNames) (E₀ : apply.AEnv GF) (γn : NetNames GF)
    (id : w64) (γa : auth.AuthNames)
    (Htb : threadBound GF ≤ 2 ^ 28) (HLv : srvLevels (GF := GF)) (Hrb48 : receiptBound GF ≤ 2 ^ 48)
    (Hbuq : apply.backendUnderQuota) (Hrf : grpcRepliesFit) (Hms : v3rpc.ServerMethodSets)
    (hlog : ρ.rd.kv.log0 = [[], []]) (hlm : ρ.rd.kv.lm = .revocable) (hLp : leasePeersOk) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗ client.eofOk ∗
        zapLoggerOk lg ∗ netAddrFree addr ∗ etcdstart.memberUpOn s ρ E₀ lg γn id γa .revocable }}
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
            etcdstart.etcdLeaseServedOn addr s E { ρ with wait := γw }) }} := by
  iintro %Φ ⟨#Pst, #Psrv, #Pv3, #Ppb, #Heo, #Hlgz, Haddr, Hup⟩ HΦ
  icases etcdstart.memberUpOn_served _ _ _ _ _ _ _ .revocable $$ Hup with ⟨%E, %cfg, %γw, %HE, #Hreq, #Hrd0,
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
        etcdstart.etcdLeaseServedOn addr s E { ρ with wait := γw })))
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
      Hlis, #Hlu⟩
    obtain ⟨HCA, HCE, Hregs1, HregsA, Hregs2, hRs, hRE, hRw, hRγ, Hnd⟩ := HC
    imod (etcdstart.kvServeStocks_pools s E ρ.rd ⊤) $$ Hstk with ⟨#Hrp, #Hrb⟩
    ihave #Hkva := client.kvServerAt_of_is p s C.A cid mid C.n $$ Hkvs
    rw [HCA]
    imod (ak_served_kv addr gs q p pa s lis E { ρ with wait := γw } cid mid C.n
        il im iu ims is svcs regs sregs γa HEo Hregs1 HregsA wp_BcryptCost Hrf Hnd HLv)
      $$ [Hgsn Hlis] with ⟨%γ, Hserv, #Hss, #HKV, #HSA, #HAu, #Hsat⟩
    · iframe; iframe #
      iintro !>
      imodintro
      iunfold idCred
      ipureintro; exact Hrb48
    ihave %hkv := etcdstart.kv_wsIface_of_cfg s E cfg C $$ [Hsf Hgc]
    · iframe #
    ihave HWok : v3rpc.srvWOk (etcdstart.srvWOf R.E ρ.rd true) R.wsl v3rpc.wsN $$ []
    · rw [hRw, hRE]
      iapply (etcdstart.srvWOk_of_readOn hP hR s E ρ.rd C.wsl hkv (by omega))
      rw [← hon]; iexact Hrd0
    imod (ak_served_watch hP (akV addr ρ R) addr pw s E ρ.rd ims is sregs γ rfl hRE hRs rfl
        (by simp) (kvSame_refl _) hlog (by omega) Hms.watch_impl Hregs2 rfl rfl rfl rfl
        (by rw [sync.rwmutex.actualMaxReaders_unseal]; omega) HLv)
      $$ [HWok] with ⟨#HWF, #Htag⟩
    · iframe; iframe #
    -- the Lease service with auth on (`lease_served_on`)
    ihave #Hil' := Hil $$ %v3rpc.learnerReqOk
    ihave #Him' := Him $$ %v3rpc.learnerReqOk
    ihave #Hreq' : isServerReqM true s E { ρ with wait := γw } $$ []
    · rw [← hon]; iexact Hreq
    ihave #Hrd' : isServerReadM true s E ρ.rd $$ []
    · rw [← hon]; iexact Hrd0
    imod (etcdstart.lease_served_on addr s E { ρ with wait := γw } C.A il im iu regs γ γa HEo hlm
        (by rw [HCA]; rfl) (by omega) (by omega) hLp HLv) $$ [] with #HLS
    · iframe #
      rw [HCA]
      iframe #
      iintro !>
      imodintro
      iunfold idCred
      ipureintro; exact Hrb48
    imodintro
    iframe HKV HSA HAu HWF Htag Hgr HLS
    isplitl [Hserv]
    · iexists γ; iexact Hserv
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


end proof

end etcd_authlease
end EtcdGrove
end Perennial
