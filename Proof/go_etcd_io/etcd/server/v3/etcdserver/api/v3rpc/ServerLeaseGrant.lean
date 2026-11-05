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
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.LeaseApi

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

/-- **The grant contract is monotone in its success fact** (the lease-expiry plan's X2,
2026-11-04): a contract at `G` is one at any `G'` that `G` entails (at every request); (E3, 2026-11-04) and at any
request filter `R'` narrower than its `R`. -/
theorem lessorGrantOkG_mono (s : Loc) (E : apply.AEnv GF) (S : IProp GF)
    (G G' : w64 × w64 → w64 → IProp GF) (R R' : w64 × w64 → Prop) (hR : ∀ m, R' m → R m) :
    □ (∀ (m : w64 × w64) (id : w64), G m id -∗ G' m id) ∗ lessorGrantOkG s E S G R ⊢
      lessorGrantOkG s E S G' R' := by
  iintro ⟨#HGG, #HL⟩
  unfold lessorGrantOkG
  iintro %ci %cd %r %m !> %Φ ⟨HS0, Hctx, Hrc, Hreq, Hid, %HR'⟩ HΦ
  wp_apply HL $$ [HS0 Hctx Hrc Hreq Hid] as %resp %err ⟨HSr, Hans, Hg⟩
  · iframe; ipureintro; exact hR m HR'
  iapply HΦ
  iframe HSr Hans
  icases Hg with (%Hne | ⟨%id, #Hid, Hg⟩)
  · ileft; ipureintro; exact Hne
  iright
  iexists id
  iframe Hid
  iapply HGG $$ %m %id Hg

/-- **The server's `LeaseGrant` meets the grant contract at the mode-free fact** (`grantLiveG`; the
lease-expiry plan's X2, 2026-11-04) in a cluster that grants leases, given the
run's resource `S` lending the request path's readers (`EtcdServer.LeaseGrant.spec`'s), with the auth store's contract
(`srvAuthAt`, amendment (G): from both server views, `srvAuthAt_of_views`). The
header's answer (`leaseHdrAns`): the revision reached (`etcdReached_of_certOk` from
`leaseGrantedResp`'s `srvRevLb`), the four id fields from its `txn.respHdrOwn`; the error one the
gRPC layer can take (`srvErrIs_of_applyErrIs`). (E3, 2026-11-04) For the requests of a filter `R`
that, in the revocable lease mode, has only `ID = 0` (`EtcdServer.LeaseGrant.spec`'s premise). -/
theorem lessorGrantOkLive_of_server (hLG : EtcdServer.LeaseGrant.spec (GF := GF) (hG := hG))
    (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (S : IProp GF) (h : srvGrantsLeases E ρ)
    (R : w64 × w64 → Prop) (hR : ∀ m, R m → ρ.rd.kv.lm = .revocable → m.2 = W64 0) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReq s E ρ ∗ srvAuthAt s E ∗ □ (|==> idCred ρ.ids 1) ∗
      □ (S -∗ srvLeadTimeReader s ∗ E.RD ∗ (srvLeadTimeReader s ∗ E.RD -∗ S)) ⊢
      lessorGrantOkG s E S (grantLiveG E) R := by
  iintro ⟨#Hpkg, #Hq, #Hau, #Hcred, #HS⟩
  unfold lessorGrantOkG
  iintro %ci %cd %r %m !> %Φ ⟨HSr, #Hctx, -, #Hreq, Hid, %HRm⟩ HΦ
  ihave ⟨Hlt, HRD, Hback⟩ := HS $$ HSr
  wp_apply (hLG s E ρ ci cd r m.1 m.2 h (hR m HRm)) $$ [Hlt HRD Hid] as %resp %err ⟨Hlt, HRD, Hans⟩
  · iframe # Hlt HRD
    iunfold leaseGrantReqOwn
    iunfold leaseGrantReqIs at Hreq
    iunfold leaseGrantReqIdOwn at Hid
    icases Hreq with ⟨%Hrn, #Httl⟩
    iframe Httl Hid
    ipureintro; exact Hrn
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
    iexists id
    iframe Hid'
    iunfold grantLiveG
    icases Hgr with ⟨%l, %t', #Hgl, #Hgt, %Hge⟩
    iexists i, l, t'
    iframe Hgl Hgt
    ipureintro; exact Hge
  · obtain ⟨rfl, hne⟩ := He
    isplitl
    · iunfold leaseGrantAns
      iright
      iapply srvErrIs_of_applyErrIs _ hne $$ HaE
    ileft; ipureintro; exact hne

/-- **The server's `LeaseGrant` meets `lessorGrantOkL`** (the grant at the lessor's history) in a
cluster that grants leases, (the lease-expiry plan's X2, 2026-11-04) in the monotone lease mode
(`lease.srvInv … .mono`), which turns the reply's mode-free fact (`lessorGrantOkLive_of_server`)
into the grant at the history (`lease.srvInv_grantedAt`); (E3) the names' lease mode not
revocable, so every request is covered. -/
theorem lessorGrantOkL_of_server (hLG : EtcdServer.LeaseGrant.spec (GF := GF) (hG := hG))
    (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (S : IProp GF) (h : srvGrantsLeases E ρ)
    (hlm : ρ.rd.kv.lm ≠ .revocable) (on : Bool) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      lease.srvInv on s E .mono ∗
      isServerReq s E ρ ∗ srvAuthAt s E ∗ □ (|==> idCred ρ.ids 1) ∗
      □ (S -∗ srvLeadTimeReader s ∗ E.RD ∗ (srvLeadTimeReader s ∗ E.RD -∗ S)) ⊢
      lessorGrantOkL s E S := by
  iintro ⟨#Hpkg, #Hli, #Hq, #Hau, #Hcred, #HS⟩
  ihave #HL := lessorGrantOkLive_of_server hLG s E ρ S h (fun _ => True)
      (fun _ _ hr => absurd hr hlm) $$ []
  · iframe #
  unfold lessorGrantOkL
  iapply lessorGrantOkG_mono s E S (grantLiveG E) _ (fun _ => True) (fun _ => True) (fun _ h => h)
  iframe HL
  iintro !> %m %id Hg
  iunfold grantLiveG at Hg
  icases Hg with ⟨%i, %l, %t, #Hgr, -⟩
  ihave ⟨%j, -, #Hgj⟩ := lease.srvInv_grantedAt on s E i id l $$ [$Hli $Hgr]
  iexists j; iexact Hgj

end proof

end v3rpc
end EtcdGrove
end Perennial
