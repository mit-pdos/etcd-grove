/-
**The server's `LeaseRevoke` meets the handler's contract, mode-gated** (the lease-expiry plan's X6,
2026-11-04, `notes/lease-expiry-plan.md`): `lessorRevokeOk s E S` (`InvLease.lean`) from the server's
`EtcdServer.LeaseRevoke.spec` at auth off (`isServerReq`), in a cluster that revokes leases (`srvRevokesLeases`: the revocable
lease mode), at a run's resource `S` lending the request path's readers; `ServerLeaseGrant`'s
`lessorGrantOkLive_of_server` mirrored. Lean-first (no Rocq counterpart).
-/
module

public import Proof.context.ReqKeys
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.ServerLeaseGrant
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__LeaseRevoke
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

/-- **The server's `LeaseRevoke` meets the revoke contract** (`lessorRevokeOk`) in a cluster that
revokes leases (`srvRevokesLeases`), given the run's resource `S` lending the request path's readers
(`EtcdServer.LeaseRevoke.spec`'s), with the auth store's contract (`srvAuthAt`). The request's
`leaseRevokeReqIs` is the spec's `leaseRevokeReqRO`; the header's answer (`leaseHdrAns`): the
revision reached (`leaseRevokedResp`'s `srvRevLb`), the four id fields
from its `txn.respHdrOwn`; the error one the gRPC layer can take (`srvErrIs_of_applyErrIs`).
Mode-gated: the ungated `lessorRevokeOk` (`raftLessor`'s conjunct, any lease mode) stays an
undischarged premise of the client results. (Auth-lease S3c, decision D6/C5′, 2026-11-15: at the
environment's auth mode, the server's view `isServerReqM E.authOn` and the contract `lessorRevokeOkM
E.authOn`, the client's update passed through and the result at the request context's token; the
auth-off contract is its `_false` instance, `lessorRevokeOkM_false`.) -/
theorem lessorRevokeOk_of_server (hLR : EtcdServer.LeaseRevoke.spec (GF := GF) (hG := hG))
    (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (S : IProp GF) (h : srvRevokesLeases E ρ) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReqM E.authOn s E ρ ∗ srvAuthAt s E ∗ □ (|==> idCred ρ.ids 1) ∗
      □ (S -∗ srvLeadTimeReader s ∗ E.RD ∗ (srvLeadTimeReader s ∗ E.RD -∗ S)) ⊢
      lessorRevokeOkM E.authOn s E ρ S := by
  iintro ⟨#Hpkg, #Hq, #Hau, #Hcred, #HS⟩
  unfold lessorRevokeOkM
  iintro %ci %tok %cd %r %id %Q !> %Φ ⟨HSr, #Hctx, #Hrun, #HtokC, #Hreq, Hp⟩ HΦ
  ihave #Hspan := spanCtxOk_of_runCtx ci $$ Hrun
  ihave #Hlibc := libCtxOk_of_runCtx ci $$ Hrun
  ihave #Hst := startTimeOk_of_grpcRunCtx ci $$ Hrun
  ihave ⟨Hlt, HRD, Hback⟩ := HS $$ HSr
  -- the permit at the server's context form (`hdrBoundM_tok`)
  ihave Hp := leaseRevokePermitM_mono E.authOn ρ.raft ρ.kv _ (hdrBoundM true s E tok) id Q
    (fun hm => hdrBoundM_tok s E tok hm) $$ Hp
  wp_apply (hLR s E ρ ci cd tok r id Q) $$ [Hlt HRD Hp] as %resp %err ⟨Hlt, HRD, Hans⟩
  · iframe # Hlt HRD
    isplitr
    · ipureintro; exact h
    isplitr
    · iunfold leaseRevokeReqRO
      iunfold leaseRevokeReqIs at Hreq
      iexact Hreq
    iexact Hp
  ihave HSr := Hback $$ [Hlt HRD]
  · iframe Hlt HRD
  iapply HΦ
  iframe HSr
  icases Hans with (⟨%He, Hresp, -, Hres⟩ | ⟨%He, #HaE⟩)
  · obtain ⟨rfl, hnn⟩ := He
    isplitr [Hres]
    rotate_left
    · iright
      cases hon : E.authOn
      · iapply leaseRevokeResT_false
      · iapply leaseRevokeResT_true s E ρ tok id Q $$ Hres
    iunfold leaseRevokedResp at Hresp
    icases Hresp with ⟨%hh, %rv, #Hh, #Hrv, %Hrv0, #Hlb, Hown⟩
    iunfold txn.respHdrOwn at Hown
    icases Hown with ⟨%h', #Hh', %Hnn', %c, %mm, %t, %l, Hc, Hm, Ht, Hl⟩
    icombine Hh Hh' gives %Hhh
    subst Hhh
    iunfold leaseRevokeAns
    ileft
    isplitr
    · ipureintro; exact ⟨rfl, hnn⟩
    iunfold leaseHdrAns
    iexists hh, rv
    iframe Hh Hrv Hlb
    isplitl
    · iunfold hdrW
      isplitr
      · ipureintro; exact Hnn'
      iexists c, mm, t, l
      iframe Hc Hm Ht Hl
    ipureintro; exact Hrv0
  · obtain ⟨rfl, hne⟩ := He
    isplitl
    · iunfold leaseRevokeAns
      iright
      iapply srvErrIs_of_applyErrIs _ hne $$ HaE
    ileft; ipureintro; exact hne

/-- **`lessorRevokeOk_of_server` with auth off** (the server's view `isServerReq`), at the auth-off
contract `lessorRevokeOk` (`lessorRevokeOkM_false`). -/
theorem lessorRevokeOk_of_server_off (hLR : EtcdServer.LeaseRevoke.spec (GF := GF) (hG := hG))
    (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (S : IProp GF) (h : srvRevokesLeases E ρ) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReq s E ρ ∗ srvAuthAt s E ∗ □ (|==> idCred ρ.ids 1) ∗
      □ (S -∗ srvLeadTimeReader s ∗ E.RD ∗ (srvLeadTimeReader s ∗ E.RD -∗ S)) ⊢
      lessorRevokeOk s E S := by
  iintro ⟨#Hpkg, #Hq, #Hau, #Hcred, #HS⟩
  ihave %hoff := isServerReq_authOn s E ρ $$ Hq
  have hthm := lessorRevokeOk_of_server hLR s E ρ S h
  rw [hoff, isServerReqM_false] at hthm
  iapply (lessorRevokeOkM_false s E ρ S).1
  iapply hthm
  iframe #

end proof

end v3rpc
end EtcdGrove
end Perennial
