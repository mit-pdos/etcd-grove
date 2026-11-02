/-
**The server's lease reads meet the handlers' contract** (the lease rows at the gRPC level,
`notes/lease-grpc-plan.md`): `raftLeaseRead s E γl S R` (`InvLeaseRead.lean`) from the server's
proved `EtcdServer.LeaseTimeToLive.spec` and `EtcdServer.LeaseLeases.spec`, at the per-call
resources `S := E.RD ∗ threadTok` (the lessor's reader pool `lessorRdPool γl` a premise: the
lease-src plan, 2026-11-02) and the revision reader
`R := mvcc.storeReader E.s E.γ` (`srvKVAns`'s `revR`, so that the handlers' `A.revR` is it). The
two specs' bounds premises are this theorem's. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvLeaseRead
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__LeaseTimeToLive
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__LeaseLeases
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__LeaseRenew
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvLeaseKeepAlive

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace v3rpc

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The server's lease reads, from its linked specs** (no premise but the server's facts and the
bounds the two specs take): `raftLeaseRead` at `S := E.RD ∗ threadTok` and
`R := mvcc.storeReader E.s E.γ`; the server's header ids `cs ms` stay inside (`leasesAns`). -/
theorem raftLeaseRead_of_server (hTTL : EtcdServer.LeaseTimeToLive.spec (GF := GF) (hG := hG))
    (hLs : EtcdServer.LeaseLeases.spec (GF := GF) (hG := hG))
    (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (γl : GName) (cs ms : w64)
    (hT : threadBound GF ≤ 2 ^ 30 - 1) (hR : receiptBound GF ≤ 2 ^ 62) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReqM E.authOn s E ρ ∗ isServerReadM E.authOn s E γr ∗ srvAuthAt s E ∗
        srvAuthLeaseLb s E ∗ srvLessorRd s γl ∗ lease.lessorRdPool γl ∗ srvHeaderFacts s cs ms ⊢
      raftLeaseRead s E γl iprop(E.RD ∗ threadTok)
        (mvcc.storeReader E.s E.γ) := by
  iintro ⟨#Hpkg, #Hq, #Hrd, #Hat, #Hal, #Hlr, #Hpool, #Hhf⟩
  iunfold raftLeaseRead
  isplitr
  · iunfold lessorTTLOk
    iintro %ci %cd %r %dq %v %n %m !> %Φ ⟨⟨HRD, Htok⟩, HR, #Hctx, #Hpub, #Hllb, Hr⟩ HΦ
    wp_apply (hTTL s E ρ γr γl ci cd r dq v n m) $$ [HRD Htok Hr]
      as %resp %err ⟨HRD, Htok, Hr, Hans⟩
    · iframe; iframe #; ipureintro; exact hT
    iapply HΦ
    iframe
    iunfold ttlAns
    iexact Hans
  · iunfold lessorLeasesOk
    iintro %ci %cd %r %n %m !> %Φ ⟨⟨HRD, Htok⟩, HR, #Hctx, #Hpub, #Hllb⟩ HΦ
    wp_apply (hLs s E γr γl ci cd r ms cs n m) $$ [HRD Htok HR]
      as %resp %err ⟨HR, HRD, Htok, Hans⟩
    · iframe; iframe #; ipureintro; exact ⟨hT, hR⟩
    iapply HΦ
    iframe
    iunfold leasesAns
    icases Hans with (⟨%He, %i, %ids, %Hmi, #Hids, Hresp, #Hchk⟩ | Herr)
    · ileft
      iframe
      isplitr
      · ipureintro; exact He
      iframe #
      ipureintro; exact Hmi
    · iright; iexact Herr

/-- **The server's header fields, from its request side** (a law: `raftLeaseRead_of_server`'s
`srvHeaderFacts` premise needs no source of its own): the cluster's id and the member's of
`isServerReqM`'s fields (`srvReqFieldsAtM`: `cluster`, `memberID`, `lead`, `srvPeersOk`'s
`clusterCid`). -/
theorem srvHeaderFacts_of_reqM (on : Bool) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) :
    isServerReqM (GF := GF) on s E ρ ⊢ ∃ cs ms : w64, srvHeaderFacts s cs ms := by
  iintro #H
  ihave ⟨%v, #Hf⟩ : ∃ v : ReqFields, srvReqFieldsAtM on s E ρ v $$ [H]
  · cases on with
    | false =>
      iunfold isServerReqM at H
      icases H with ⟨#Hv, -⟩
      iexact Hv
    | true =>
      iunfold isServerReqM at H
      icases H with ⟨#Hv, -, -⟩
      iexact Hv
  iunfold srvReqFieldsAtM at Hf
  icases Hf with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hmid, #Hlead, #Hcl, -, #Hpeers,
    -, -, -, -, -, -⟩
  iunfold srvPeersOk at Hpeers
  icases Hpeers with ⟨#Hcid, -, -⟩
  iexists v.cid, v.memberID
  iunfold srvHeaderFacts
  iexists v.cluster
  iframe #
  iunfold srvAtomicU64 at Hlead
  iunfold srvLeadInv
  iexact Hlead

/-- **The server's renewals, from its linked spec** (the keep-alive's contract): `raftLeaseRenew` at
`S' := E.RD ∗ threadTok ∗ srvLgReader s ∗ srvReadReader s γr`, over the server's
facts, its peer round tripper (`srvPeerRt`) and the spec's thread bound. -/
theorem raftLeaseRenew_of_server (hRn : EtcdServer.LeaseRenew.spec (GF := GF) (hG := hG))
    (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (γl : GName)
    (hT : threadBound GF ≤ 2 ^ 30 - 1) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReqM E.authOn s E ρ ∗ isServerReadM E.authOn s E γr ∗ srvAuthAt s E ∗
        srvAuthLeaseLb s E ∗ srvLessorRd s γl ∗ lease.lessorRdPool γl ∗ srvPeerRt s ⊢
      raftLeaseRenew s E γl
        iprop(E.RD ∗ threadTok ∗ srvLgReader s ∗ srvReadReader s γr) := by
  iintro ⟨#Hpkg, #Hq, #Hrd, #Hat, #Hal, #Hlr, #Hpool, #Hpr⟩
  iunfold raftLeaseRenew
  iintro %ci %cd %id %n %m !> %Φ ⟨⟨HRD, Htok, Hlg, Hrr⟩, #Hctx, #Hpub, #Hllb⟩ HΦ
  wp_apply (hRn s E ρ γr γl ci cd id n m) $$ [HRD Htok Hlg Hrr]
    as %ttl %err ⟨HRD, Htok, Hlg, Hrr, Hans⟩
  · iframe; iframe #; ipureintro; exact hT
  iapply HΦ
  iframe
  iunfold renewAns
  iexact Hans

end proofs

end v3rpc
end EtcdGrove
end Perennial
