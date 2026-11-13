/-
**Per-type instances: the lease keep-alive stream's messages** (stage A, CP3):
`LeaseKeepAliveRequest` (`StreamMsgT.ReqSat`, `wireLen_ok`) and `LeaseKeepAliveResponse`
(`StreamMsgT.RepSat`), with their registrations. Each instance is today's `StreamMsg`
(`LeaseKeepAliveMsg.lean`) with its normalizing store (`tree`).

The response's model is its `(ID, TTL)` only, not its header (`keepAliveRespMsg` holds "some
header"), so its store leaves `Header` `nil` whatever the sender's header: what the store gives is
what the model says, not what protobuf-go's decoder leaves of the server's (always present) header.
-/
module

public import Proof.google_golang_org.grpc.InvGrpcStream
public import Proof.go_etcd_io.etcd.api.v3.etcdserverpb.LeaseKeepAliveMsg

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [pkg_pb : go_etcd_io.etcd.api.v3.etcdserverpb.Assumptions]

/-- **The store of a keep-alive request**: its `ID` (the ghost bounds are not on the wire). -/
def kaReqTree (q : KaReqM) : VTree :=
  .strct etcdserverpb.LeaseKeepAliveRequest.ty [(go!"ID", go.int64)] [.leaf #q.id]

/-- **`pbLeaseKeepAliveRequest` with its store.** -/
def pbLeaseKeepAliveRequestT : StreamMsgT GF :=
  { pbLeaseKeepAliveRequest with tree := kaReqTree }

/-- **`pbLeaseKeepAliveRequestT`'s request model is satisfiable.** -/
theorem pbLeaseKeepAliveRequestT_reqSat : (pbLeaseKeepAliveRequestT (GF := GF)).ReqSat := by
  refine ⟨⟨etcdserverpb.LeaseKeepAliveRequest, inferInstance, inferInstance,
      (inferInstance : IntoValTyped etcdserverpb.LeaseKeepAliveRequest
        etcdserverpb.LeaseKeepAliveRequest.ty), fun l => .rfl⟩, ?_, ?_⟩
  · intro m
    simp only [pbLeaseKeepAliveRequestT, pbLeaseKeepAliveRequest]
    iintro ⟨%req, Hp, -⟩
    ihave %H := typedPointsto_not_null $$ Hp
    exact absurd rfl H
  intro ls l m
  simp only [pbLeaseKeepAliveRequestT, pbLeaseKeepAliveRequest]
  iintro ⟨Hs, %Hw, ⟨%x0, Hl⟩⟩
  iapply wp_fupd
  iapply (storeInto_wp_typed (V := etcdserverpb.LeaseKeepAliveRequest)
    (ty := etcdserverpb.LeaseKeepAliveRequest.ty) l x0)
  simp only [kaReqTree, treeWp, treeWpL, isPanic_intoVal]
  simp [litBody, strctKes, kesσ, envσ]
  repeat (isplitr; · ipureintro; trivial)
  wp_auto
  iexists _
  isplitr
  · ipureintro; rfl
  iframe Hl
  iintro Hl
  imodintro
  iframe Hs
  iexists _
  iframe Hl
  ipureintro; rfl

theorem pbLeaseKeepAliveRequestT_wireLen_ok :
    ∃ m, (pbLeaseKeepAliveRequestT (GF := GF)).wireLen m < grpcMsgMax :=
  ⟨⟨0, 0, 0⟩, by simp [pbLeaseKeepAliveRequestT, pbLeaseKeepAliveRequest, wireSlack, grpcMsgMax]⟩

/-- **The store of a keep-alive response**: its `ID` and `TTL`; its `Header` `nil` (the model does
not carry it: see the file header). -/
def kaRespTree (m : w64 × w64) : VTree :=
  .strct etcdserverpb.LeaseKeepAliveResponse.ty
    [(go!"Header", go.GoType.PointerType etcdserverpb.ResponseHeader.ty), (go!"ID", go.int64),
     (go!"TTL", go.int64)]
    [.leaf #(null : Loc), .leaf #m.1, .leaf #m.2]

/-- **`pbLeaseKeepAliveResponse` with its store.** -/
def pbLeaseKeepAliveResponseT : StreamMsgT GF :=
  { pbLeaseKeepAliveResponse with tree := kaRespTree }

/-- **`pbLeaseKeepAliveResponseT`'s reply model is satisfiable.** -/
theorem pbLeaseKeepAliveResponseT_repSat : (pbLeaseKeepAliveResponseT (GF := GF)).RepSat := by
  refine ⟨⟨etcdserverpb.LeaseKeepAliveResponse, inferInstance, inferInstance,
      (inferInstance : IntoValTyped etcdserverpb.LeaseKeepAliveResponse
        etcdserverpb.LeaseKeepAliveResponse.ty), fun l => .rfl⟩, ?_, ?_⟩
  · intro m
    simp only [pbLeaseKeepAliveResponseT, pbLeaseKeepAliveResponse, keepAliveRespMsg]
    iintro ⟨%H, -⟩
    exact absurd rfl H
  intro ls l m
  simp only [pbLeaseKeepAliveResponseT, pbLeaseKeepAliveResponse]
  iintro ⟨Hs, ⟨%x0, Hl⟩⟩
  iapply wp_fupd
  iapply (storeInto_wp_typed (V := etcdserverpb.LeaseKeepAliveResponse)
    (ty := etcdserverpb.LeaseKeepAliveResponse.ty) l x0)
  simp only [kaRespTree, treeWp, treeWpL, isPanic_intoVal]
  simp [litBody, strctKes, kesσ, envσ]
  repeat (isplitr; · ipureintro; trivial)
  wp_auto
  iexists _
  isplitr
  · ipureintro; rfl
  iframe Hl
  iintro Hl
  ihave %Hnn := typedPointsto_not_null $$ Hl
  icases typedPointsto_split _ _ _ $$ Hl with Hl
  simp only [TypedPointsto.typedPointstoDef]
  icases Hl with ⟨-, HH, HI, HT, -, -, -⟩
  imod (typedPointsto_dfractional (GF := GF) _ (null : Loc)).dfractional_persist _ $$ HH with #HH
  imod (typedPointsto_dfractional (GF := GF) _ m.1).dfractional_persist _ $$ HI with #HI
  imod (typedPointsto_dfractional (GF := GF) _ m.2).dfractional_persist _ $$ HT with #HT
  imodintro
  iframe Hs
  unfold keepAliveRespMsg
  isplitr
  · ipureintro; exact Hnn
  iexists null
  iframe HH HI HT

/-- **`LeaseKeepAliveRequest`'s registration** (stage A: the one model of the Go type
`LeaseKeepAliveRequest` as a stream's request). -/
axiom pbLeaseKeepAliveRequestT_reg :
    streamReqModelOf GF etcdserverpb.LeaseKeepAliveRequest.ty =
      some (pbLeaseKeepAliveRequestT (GF := GF))

/-- **`LeaseKeepAliveResponse`'s registration** (stage A: the one model of the Go type
`LeaseKeepAliveResponse` as a stream's reply). -/
axiom pbLeaseKeepAliveResponseT_reg :
    streamRepModelOf GF etcdserverpb.LeaseKeepAliveResponse.ty =
      some (pbLeaseKeepAliveResponseT (GF := GF))

end defs

end EtcdGrove
end Perennial
