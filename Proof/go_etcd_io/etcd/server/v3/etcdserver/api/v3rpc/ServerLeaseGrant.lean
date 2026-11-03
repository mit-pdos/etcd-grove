/-
**The server's `LeaseGrant` meets the handler's contract at the lessor's history** (the lease-grant
plan's 2.4, `notes/lease-grant-plan.md`): `lessorGrantOkL s E S` (`InvLeaseGrant.lean`) from the
server's `EtcdServer.LeaseGrant.spec`, in a cluster that grants leases, at a run's resource `S`
lending the request path's readers. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvLeaseGrant
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.ServerKV
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__LeaseGrant

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

/-- **The server's `LeaseGrant` meets `lessorGrantOkL`** in a cluster that grants leases, given the
run's resource `S` lending the request path's readers (`EtcdServer.LeaseGrant.spec`'s), with the auth store's contract
(`srvAuthAt`, amendment (G): from both server views, `srvAuthAt_of_views`). The
header's answer (`leaseHdrAns`): the revision reached (`etcdReached_of_certOk` from
`leaseGrantedResp`'s `srvRevLb`), the four id fields from its `txn.respHdrOwn`; the error one the
gRPC layer can take (`srvErrIs_of_applyErrIs`). -/
theorem lessorGrantOkL_of_server (hLG : EtcdServer.LeaseGrant.spec (GF := GF) (hG := hG))
    (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (S : IProp GF) (h : srvGrantsLeases E ρ) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReq s E ρ ∗ srvAuthAt s E ∗ □ (|==> idCred ρ.ids 1) ∗
      □ (S -∗ srvLeadTimeReader s ∗ E.RD ∗ (srvLeadTimeReader s ∗ E.RD -∗ S)) ⊢
      lessorGrantOkL s E S := by
  iintro ⟨#Hpkg, #Hq, #Hau, #Hcred, #HS⟩
  iunfold lessorGrantOkL
  iintro %ci %cd %r %m !> %Φ ⟨HSr, #Hctx, -, #Hreq, Hid⟩ HΦ
  ihave ⟨Hlt, HRD, Hback⟩ := HS $$ HSr
  wp_apply (hLG s E ρ ci cd r m.1 m.2 h) $$ [Hlt HRD Hid] as %resp %err ⟨Hlt, HRD, Hans⟩
  · iframe # Hlt HRD
    iunfold leaseGrantReqOwn
    iunfold leaseGrantReqIs at Hreq
    iunfold leaseGrantReqIdOwn at Hid
    iframe Hreq Hid
  ihave HSr := Hback $$ [Hlt HRD]
  · iframe Hlt HRD
  iapply HΦ
  iframe HSr
  icases Hans with (⟨%He, Hresp⟩ | ⟨%He, #HaE⟩)
  · obtain ⟨rfl, hnn⟩ := He
    iunfold leaseGrantedResp at Hresp
    icases Hresp with ⟨%id, %ttl, %e, %i, %hh, %rv, #Hh, #Hrv, %Hrv0, #Hlb, Hown, #Hid', %Hid0,
      #Httl, #He', #Hgr⟩
    iunfold txn.respHdrOwn at Hown
    icases Hown with ⟨%h', #Hh', %Hnn', %c, %mm, %t, %l, Hc, Hm, Ht, Hl⟩
    icombine Hh Hh' gives %Hhh
    subst Hhh
    iunfold srvRevLb at Hlb
    icases Hlb with ⟨%log, -, #Hcert, %Hlt⟩
    ihave #Hreach := etcdReached_of_certOk E log rv Hlt $$ Hcert
    isplitl
    · iunfold leaseGrantAns
      ileft
      isplitr
      · ipureintro; exact ⟨rfl, hnn⟩
      isplitl
      · iunfold leaseHdrAns
        iexists hh, rv
        iframe Hh Hrv Hreach
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
    iexists id, i
    iframe Hid' Hgr
  · obtain ⟨rfl, hne⟩ := He
    isplitl
    · iunfold leaseGrantAns
      iright
      iapply srvErrIs_of_applyErrIs _ hne $$ HaE
    ileft; ipureintro; exact hne

end proof

end v3rpc
end EtcdGrove
end Perennial
