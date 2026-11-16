/-
**The server's `LeaseGrant` meets the handler's contract at the lessor's history** (the lease-grant
plan's 2.4, `notes/lease-grant-plan.md`): `lessorGrantOkLM E.authOn s E ρ S` (`InvLeaseGrant.lean`) from the
server's `EtcdServer.LeaseGrant.spec`, in a cluster that grants leases, at a run's resource `S`
lending the request path's readers. Lean-first (no Rocq counterpart).
-/
module

public import Proof.context.ReqKeys
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvLeaseGrant
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.ServerKV
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__LeaseGrant
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.LeaseApi
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseOn

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace v3rpc

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **The server's `LeaseGrant` meets the grant contract at the mode-free fact** (`grantLiveG`; the
lease-expiry plan's X2, 2026-11-04) in a cluster that grants leases, given the
run's resource `S` lending the request path's readers (`EtcdServer.LeaseGrant.spec`'s), with the auth store's contract
(`srvAuthAt`, amendment (G): from both server views, `srvAuthAt_of_views`). The
header's answer (`leaseHdrAns`): the revision reached (`leaseGrantedResp`'s `srvRevLb`), the four id fields from its `txn.respHdrOwn`; the error one the
gRPC layer can take (`srvErrIs_of_applyErrIs`). (E3, 2026-11-04) For the requests of a filter `R`
that, in the revocable lease mode, has only `ID = 0` (`EtcdServer.LeaseGrant.spec`'s premise).
(Auth-lease S3c, decision D6/C5′, 2026-11-15: at the environment's auth mode, the server's view
`isServerReqM E.authOn` and the contract `lessorGrantOkGM E.authOn`, the client's update passed
through and the result at the request context's token.) -/
theorem lessorGrantOkLive_of_server (hLG : EtcdServer.LeaseGrant.spec (GF := GF) (hG := hG))
    (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (S : IProp GF) (h : srvGrantsLeases E ρ)
    (R : w64 × w64 → Prop) (hR : ∀ m, R m → ρ.rd.kv.lm = .revocable → m.2 = W64 0) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReqM E.authOn s E ρ ∗ srvAuthAt s E ∗ □ (|==> idCred ρ.ids 1) ∗
      □ (S -∗ srvLeadTimeReader s ∗ E.RD ∗ (srvLeadTimeReader s ∗ E.RD -∗ S)) ⊢
      lessorGrantOkGM E.authOn s E ρ S (grantLiveG E) R := by
  iintro ⟨#Hpkg, #Hq, #Hau, #Hcred, #HS⟩
  unfold lessorGrantOkGM
  iintro %ci %cd %r %m %Q %n !> %Φ ⟨HSr, #Hn, #Hctx, #Hrun, #Hreq, Hid, %HRm, Hp⟩ HΦ
  ihave #Hspan := spanCtxOk_of_runCtx ci $$ Hrun
  ihave #Hlibc := libCtxOk_of_runCtx ci $$ Hrun
  ihave #Hst := startTimeOk_of_grpcRunCtx ci $$ Hrun
  ihave ⟨Hlt, HRD, Hback⟩ := HS $$ HSr
  -- the permit at the server's context form (`hdrBoundM_tok`)
  ihave Hp := leaseGrantPermitM_mono E.authOn ρ.raft ρ.kv _ (hdrBoundM true s E (GoInterface.ok ci)) m.1 Q
    (fun hm => hdrBoundM_tok s E (GoInterface.ok ci) hm) $$ Hp
  wp_apply (hLG s E ρ ci cd r m.1 m.2 Q n) $$ [Hlt HRD Hid Hp] as %resp %err ⟨Hlt, HRD, Hans⟩
  · iframe # Hlt HRD
    isplitr
    · ipureintro; exact ⟨h, hR m HRm⟩
    isplitl [Hid]
    · iunfold leaseGrantReqOwn
      iunfold leaseGrantReqIs at Hreq
      iunfold leaseGrantReqIdOwn at Hid
      icases Hreq with ⟨%Hrn, #Httl⟩
      iframe Httl Hid
      ipureintro; exact Hrn
    iexact Hp
  ihave HSr := Hback $$ [Hlt HRD]
  · iframe Hlt HRD
  iapply HΦ
  iframe HSr
  icases Hans with (⟨%He, Hresp, -, #Hfr, Hres⟩ | ⟨%He, #HaE⟩)
  · obtain ⟨rfl, hnn⟩ := He
    iunfold leaseGrantedResp at Hresp
    icases Hresp with ⟨%id, %ttl, %e, %i, %hh, %rv, #Hh, #Hrv, %Hrv0, #Hlb, Hown, #Hid', %Hid0,
      #Httl, #He', #Hgr⟩
    iunfold txn.respHdrOwn at Hown
    icases Hown with ⟨%h', #Hh', %Hnn', %c, %mm, %t, %l, Hc, Hm, Ht, Hl⟩
    icombine Hh Hh' gives %Hhh
    subst Hhh
    isplitl [Hc Hm Ht Hl]
    · iunfold leaseGrantAns
      ileft
      isplitr
      · ipureintro; exact ⟨rfl, hnn⟩
      isplitl
      · iunfold leaseHdrAns
        iexists hh, rv
        iframe Hh Hrv Hlb
        isplitl
        · iunfold hdrW
          isplitr
          · ipureintro; exact Hnn'
          iexists c, mm, t, l
          iframe Hc Hm Ht Hl
        ipureintro; exact Hrv0
      iunfold leaseGrantFields
      iexists id, ttl, e
      iframe Hid' Httl He'
      ipureintro; exact Hid0
    iright
    iexists id
    iframe Hid'
    isplitr [Hres]
    · iunfold grantLiveG
      icases Hgr with ⟨%l, #Hgl, #Hgreq⟩
      iexists i, l
      iframe Hgl Hgreq
    isplitl [Hres]
    rotate_left
    · iapply leaseCheckT_of_from s E (GoInterface.ok ci) n
      iapply leaseCheckFrom_of_authedFrom $$ Hfr
    cases hon : E.authOn
    · iapply leaseGrantResT_false
    · ihave ⟨%id', #Hid2, HT⟩ := leaseGrantResT_true s E ρ ci m.1 resp Q $$ Hres
      icombine Hid' Hid2 gives %Hii
      subst Hii
      iexact HT
  · obtain ⟨rfl, hne⟩ := He
    isplitl
    · iunfold leaseGrantAns
      iright
      iapply srvErrIs_of_applyErrIs _ hne $$ HaE
    ileft; ipureintro; exact hne

/-- **The server's `LeaseGrant` meets `lessorGrantOkLM`** (the grant at the lessor's history) in a
cluster that grants leases, (the lease-expiry plan's X2, 2026-11-04) in the monotone lease mode
(`lease.srvInv … .mono`), which turns the reply's mode-free fact (`lessorGrantOkLive_of_server`)
into the grant at the history (`lease.srvInv_grantedAt`); (E3) the names' lease mode not
revocable, so every request is covered. (Auth-lease S4, the C5′ merge, 2026-11-16: at the
environment's auth mode, the server's view `isServerReqM E.authOn`; until then `lessorGrantOkL_of_server`,
with auth off.) -/
theorem lessorGrantOkLM_of_server (hLG : EtcdServer.LeaseGrant.spec (GF := GF) (hG := hG))
    (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (S : IProp GF) (h : srvGrantsLeases E ρ)
    (hlm : ρ.rd.kv.lm ≠ .revocable) (on : Bool) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      lease.srvInv on s E .mono ∗
      isServerReqM E.authOn s E ρ ∗ srvAuthAt s E ∗ □ (|==> idCred ρ.ids 1) ∗
      □ (S -∗ srvLeadTimeReader s ∗ E.RD ∗ (srvLeadTimeReader s ∗ E.RD -∗ S)) ⊢
      lessorGrantOkLM E.authOn s E ρ S := by
  iintro ⟨#Hpkg, #Hli, #Hq, #Hau, #Hcred, #HS⟩
  ihave #HL := lessorGrantOkLive_of_server hLG s E ρ S h (fun _ => True)
      (fun _ _ hr => absurd hr hlm) $$ []
  · iframe #
  unfold lessorGrantOkLM
  iapply lessorGrantOkGM_mono E.authOn s E ρ S (grantLiveG E) _ (fun _ => True) (fun _ => True) (fun _ h => h)
  iframe HL
  iintro !> %m %id Hg
  iunfold grantLiveG at Hg
  icases Hg with ⟨%i, %l, #Hgr, -⟩
  ihave ⟨%j, -, #Hgj⟩ := lease.srvInv_grantedAt on s E i id l $$ [$Hli $Hgr]
  iexists j; iexact Hgj

end proof

end v3rpc
end EtcdGrove
end Perennial
