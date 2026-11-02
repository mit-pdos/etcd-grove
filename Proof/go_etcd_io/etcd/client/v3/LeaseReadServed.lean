/-
**etcd's lease reads, served** (the closed lease example, 2026-11-02; `notes/lease-ex-plan.md`).
Lean-first (no Rocq counterpart).

The `*quotaLeaseServer`'s `LeaseTimeToLive` and `LeaseLeases` (the embedded `*LeaseServer`'s,
promoted: `v3rpc.quotaLease_ttlHandlerOk`, `quotaLease_leasesHandlerOk`), `LeaseServer`'s (the
server's call, then the header filled; linked over the contract `v3rpc.raftLeaseRead`), meet the
client's specs `etcdLeaseTTLSpec`/`etcdLeaseLeasesSpec` (`InvLeaseRead.lean`), as the grant's and
revoke's meet theirs (`Results.lean`, `etcd_leaseGrantHandlerOk`):

* `etcd_leaseTTLHandlerOk`: the handler's answer (`leaseTTLOut`) is about the asked lease (its
  `ID`, the server's or the handler's not-found reply), its header persisted;
* `etcd_leaseLeasesHandlerOk`: the handler's listing is the lessor's IDs at some index
  (`leaseIdsAt`: no ID twice), or empty;
* `etcd_leaseTTLMethodOk`, `etcd_leaseLeasesMethodOk`: as grpc runs them (the generated handlers,
  under the interceptors); `etcdLeaseReadMethods`/`etcdLeaseReadRegs`: the two methods, registered.

Both handlers run at the slot `S ∗ A.revR` of the contract (`raftLeaseRead_server`'s `S := E.RD ∗
threadTok`, `A.revR` the store's reader), with the lower bounds `0` of the auth store and the
lessor's history (`grpcHandlerOk_slot` rearranges a run's slot into it).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.Results
public import Proof.go_etcd_io.etcd.client.v3.InvLeaseRead
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb._Lease_LeaseTimeToLive_Handler
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb._Lease_LeaseLeases_Handler

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace client

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver

section slot
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **A service method meeting `Spec` with `S` meets it with any slot `S'` that holds `S` and
gives it back** (`grpcHandlerOk_frame`'s, through the entailments `S' ⊢ S ∗ F`, `S ∗ F ⊢ S'`). -/
theorem grpcHandlerOk_slot {Req Rep : ProtoMsg GF} (h : val) (S S' F : IProp GF)
    (Spec : GrpcSpec Req Rep) (h1 : S' ⊢ S ∗ F) (h2 : S ∗ F ⊢ S') :
    grpcHandlerOk h S Spec ⊢ grpcHandlerOk h S' Spec := by
  iintro #Hh
  unfold grpcHandlerOk
  iintro %m %Φ %ci %cd %r !> %Ψ ⟨HS', #Hctx, #Hrc, #Hr, HSpec⟩ HΨ
  ihave ⟨HS, HF⟩ := h1 $$ HS'
  iapply Hh $$ %m %Φ %ci %cd %r [HS HSpec]
  · iframe; iframe #
  inext
  iintro %resp %err ⟨HS, Hres⟩
  iapply HΨ
  iframe Hres
  iapply h2
  iframe

end slot

section served
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- **etcd's `LeaseTimeToLive` handler meets etcd's `LeaseTimeToLive` spec** (`grpcHandlerOk`),
over the lease-read contract at the run resource `S` and the revision reader `A.revR`, at the lower
bounds `n` (the auth store) and `m` (the lessor's history): `LeaseServer.LeaseTimeToLive`'s answer,
persisted, is the reply's message, about the asked lease. -/
theorem etcd_leaseTTLHandlerOk (lp s : Loc) (A : v3rpc.KVAns GF) (cid mid : w64)
    (E : apply.AEnv GF) (γl : GName) (S : IProp GF) (n m : Nat) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        v3rpc.leaseServerAt lp s A cid mid ∗ v3rpc.raftLeaseRead s E γl S A.revR ∗
        auth.authPubLbM E.authMode n ∗ lease.lessorLb γl m ⊢
      grpcHandlerOk (lp @!! go.GoType.PointerType
          go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer.ty @!! go!"LeaseTimeToLive")
        iprop(S ∗ A.revR) etcdLeaseTTLSpec := by
  sorry

/-- **etcd's `LeaseLeases` handler meets etcd's `LeaseLeases` spec** (as
`etcd_leaseTTLHandlerOk`): the reply lists the lessor's IDs at some index of its history, or
none. -/
theorem etcd_leaseLeasesHandlerOk (lp s : Loc) (A : v3rpc.KVAns GF) (cid mid : w64)
    (E : apply.AEnv GF) (γl : GName) (S : IProp GF) (n m : Nat) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        v3rpc.leaseServerAt lp s A cid mid ∗ v3rpc.raftLeaseRead s E γl S A.revR ∗
        auth.authPubLbM E.authMode n ∗ lease.lessorLb γl m ⊢
      grpcHandlerOk (lp @!! go.GoType.PointerType
          go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer.ty @!! go!"LeaseLeases")
        iprop(S ∗ A.revR) etcdLeaseLeasesSpec := by
  sorry

/-- The lease reads' requests at a pointer: the learner check reads nothing of them. -/
theorem leaseTTLReq_learnerOk (l : Loc) :
    ⊢ v3rpc.learnerReqOk (GF := GF)
      (interface.mkOk (go.GoType.PointerType etcdserverpb.LeaseTimeToLiveRequest.ty) #l) :=
  v3rpc.learnerReqOk_ptr _ l (by
    simp [etcdserverpb.LeaseTimeToLiveRequest.ty, etcdserverpb.RangeRequest.ty])

theorem leaseLeasesReq_learnerOk (l : Loc) :
    ⊢ v3rpc.learnerReqOk (GF := GF)
      (interface.mkOk (go.GoType.PointerType etcdserverpb.LeaseLeasesRequest.ty) #l) :=
  v3rpc.learnerReqOk_ptr _ l (by
    simp [etcdserverpb.LeaseLeasesRequest.ty, etcdserverpb.RangeRequest.ty])

/-- **etcd's `LeaseTimeToLive`, as grpc runs it** (as `etcd_leaseGrantMethodOk`). -/
theorem etcd_leaseTTLMethodOk (q : Loc)
    (Spec : GrpcSpec (GF := GF) pbLeaseTimeToLiveRequest pbLeaseTimeToLiveResponse) (S : IProp GF)
    (ics : List GoFunc) (Rs : List (IProp GF)) :
    grpcHandlerOk (q @!! go.GoType.PointerType
          go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaLeaseServer.ty @!! go!"LeaseTimeToLive")
        S Spec ∗ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
        srvInterceptorsOk v3rpc.learnerReqOk ics Rs ⊢
      grpcMethodOk (@! etcdserverpb._Lease_LeaseTimeToLive_Handler)
        (interface.mkOk (go.GoType.PointerType
          go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaLeaseServer.ty) #q)
        ics iprop(S ∗ [∗list] R ∈ Rs, R) Spec := by
  sorry

/-- **etcd's `LeaseLeases`, as grpc runs it** (as `etcd_leaseGrantMethodOk`). -/
theorem etcd_leaseLeasesMethodOk (q : Loc)
    (Spec : GrpcSpec (GF := GF) pbLeaseLeasesRequest pbLeaseLeasesResponse) (S : IProp GF)
    (ics : List GoFunc) (Rs : List (IProp GF)) :
    grpcHandlerOk (q @!! go.GoType.PointerType
          go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaLeaseServer.ty @!! go!"LeaseLeases")
        S Spec ∗ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
        srvInterceptorsOk v3rpc.learnerReqOk ics Rs ⊢
      grpcMethodOk (@! etcdserverpb._Lease_LeaseLeases_Handler)
        (interface.mkOk (go.GoType.PointerType
          go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaLeaseServer.ty) #q)
        ics iprop(S ∗ [∗list] R ∈ Rs, R) Spec := by
  sorry

/-- **etcd's lease reads** as registered: `LeaseTimeToLive` and `LeaseLeases`, the generated
handlers of `Lease_ServiceDesc` with the `*quotaLeaseServer` `q`, with etcd's specs. -/
def etcdLeaseReadMethods (q : Loc) : List (GrpcMethod GF) :=
  [⟨go!"/etcdserverpb.Lease/LeaseTimeToLive", pbLeaseTimeToLiveRequest, pbLeaseTimeToLiveResponse,
     GrpcSpec.md etcdLeaseTTLSpec, (@! etcdserverpb._Lease_LeaseTimeToLive_Handler),
     interface.mkOk (go.GoType.PointerType
       go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaLeaseServer.ty) #q⟩,
   ⟨go!"/etcdserverpb.Lease/LeaseLeases", pbLeaseLeasesRequest, pbLeaseLeasesResponse,
     GrpcSpec.md etcdLeaseLeasesSpec, (@! etcdserverpb._Lease_LeaseLeases_Handler),
     interface.mkOk (go.GoType.PointerType
       go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.quotaLeaseServer.ty) #q⟩]

/-- **etcd's lease reads registered at `addr`** (persistent): what `examples/leasekv`'s client
calls. -/
def etcdLeaseReadAt (addr : GoString) : IProp GF :=
  iprop(isGrpcRpc addr go!"/etcdserverpb.Lease/LeaseTimeToLive" etcdLeaseTTLSpec ∗
    isGrpcRpc addr go!"/etcdserverpb.Lease/LeaseLeases" etcdLeaseLeasesSpec)

instance etcdLeaseReadAt_persistent (addr : GoString) :
    Persistent (etcdLeaseReadAt (GF := GF) addr) := by
  unfold etcdLeaseReadAt; infer_instance

end served

end client
end EtcdGrove
end Perennial
