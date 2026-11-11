/-
**Per-type instances: the Lease service's unary messages** (stage A, CP3): `LeaseGrantRequest`,
`LeaseRevokeRequest`, `LeaseTimeToLiveRequest`, `LeaseLeasesRequest` (`ReqSat`, `wireLen_ok`) and
`LeaseGrantResponse`, `LeaseRevokeResponse`, `LeaseTimeToLiveResponse`, `LeaseLeasesResponse`
(`RepSat`), with their registrations. Each instance is today's `ProtoMsg` (`InvLease.lean`,
`InvLeaseRead.lean`) with its normalizing store (`tree`).

The `LeaseTimeToLiveResponse` model does not carry the keys' contents (`LeaseTTLRespM`), so its store
leaves `Keys` `nil` whatever the sender's keys: what the store gives is what the model says, not
what protobuf-go's decoder leaves when the sender attached keys.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.PerTypeKV
public import Proof.go_etcd_io.etcd.client.v3.InvLeaseRead

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
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-! ## `LeaseGrant` -/

/-- **The store of a lease-grant request**: its `TTL` and `ID`. -/
def leaseGrantReqTree (m : w64 × w64) : VTree :=
  .strct etcdserverpb.LeaseGrantRequest.ty [(go!"TTL", go.int64), (go!"ID", go.int64)]
    [.leaf #m.1, .leaf #m.2]

/-- **`pbLeaseGrantRequest` with its store.** -/
def pbLeaseGrantRequestT : ProtoMsgT GF :=
  { pbLeaseGrantRequest with tree := leaseGrantReqTree }

/-- **`pbLeaseGrantRequestT`'s request model is satisfiable.** -/
theorem pbLeaseGrantRequestT_reqSat : (pbLeaseGrantRequestT (GF := GF)).ReqSat := by
  refine ⟨⟨etcdserverpb.LeaseGrantRequest, inferInstance, inferInstance,
      (inferInstance : IntoValTyped etcdserverpb.LeaseGrantRequest
        etcdserverpb.LeaseGrantRequest.ty), fun l => .rfl⟩,
    ⟨etcdserverpb.LeaseGrantRequest, inferInstance, inferInstance,
      (inferInstance : IntoValTyped etcdserverpb.LeaseGrantRequest
        etcdserverpb.LeaseGrantRequest.ty), fun l => .rfl⟩,
    ?_, ?_⟩
  · intro m
    simp only [pbLeaseGrantRequestT, pbLeaseGrantRequest]
    iintro ⟨%req, Hp, -⟩
    ihave %H := typedPointsto_not_null $$ Hp
    exact absurd rfl H
  intro ls l m
  simp only [pbLeaseGrantRequestT, pbLeaseGrantRequest]
  iintro ⟨⟨%req, Hp, %Hm⟩, %Hw, Hl⟩
  obtain ⟨rfl, Hu⟩ := Hm
  iapply wp_fupd
  iapply (storeInto_wp_typed (V := etcdserverpb.LeaseGrantRequest)
    (ty := etcdserverpb.LeaseGrantRequest.ty) l (zero_val etcdserverpb.LeaseGrantRequest))
  simp only [leaseGrantReqTree, treeWp, treeWpL, isPanic_intoVal]
  simp [litBody, strctKes, kesσ, envσ]
  repeat (isplitr; · ipureintro; trivial)
  wp_auto
  iexists _
  isplitr
  · ipureintro; rfl
  iframe Hl
  iintro Hl
  isplitl [Hp]
  · iexists req
    iframe Hp
    ipureintro; exact ⟨by simp, Hu⟩
  ihave %Hnn := typedPointsto_not_null $$ Hl
  icases typedPointsto_split _ _ _ $$ Hl with Hl
  simp only [TypedPointsto.typedPointstoDef]
  icases Hl with ⟨-, HT, HI, -, -, -⟩
  imod (typedPointsto_dfractional (GF := GF) _ req.TTL').dfractional_persist _ $$ HT with #HT
  imodintro
  iframe HI HT
  ipureintro; exact Hnn

theorem pbLeaseGrantRequestT_wireLen_ok :
    ∃ m, (pbLeaseGrantRequestT (GF := GF)).wireLen m < grpcMsgMax :=
  ⟨(0, 0), by simp [pbLeaseGrantRequestT, pbLeaseGrantRequest, wireSlack, grpcMsgMax]⟩

/-- **The store of a lease-grant response**: its header, `ID`, `TTL`, `Error`. -/
def leaseGrantRespTree (m : LeaseGrantRespM) : VTree :=
  .strct etcdserverpb.LeaseGrantResponse.ty
    [(go!"Header", go.GoType.PointerType etcdserverpb.ResponseHeader.ty), (go!"ID", go.int64),
     (go!"TTL", go.int64), (go!"Error", go.string)]
    [hdrTree m.hdr, .leaf #m.id, .leaf #m.ttl, .leaf #m.err]

/-- **`pbLeaseGrantResponse` with its store.** -/
def pbLeaseGrantResponseT : ProtoMsgT GF :=
  { pbLeaseGrantResponse with tree := leaseGrantRespTree }

/-- **`pbLeaseGrantResponseT`'s reply model is satisfiable.** -/
theorem pbLeaseGrantResponseT_repSat : (pbLeaseGrantResponseT (GF := GF)).RepSat := by
  apply ProtoMsgT.repSat_of_recvOwn_true _ (fun _ _ => rfl)
  refine ⟨⟨etcdserverpb.LeaseGrantResponse, inferInstance, inferInstance,
      (inferInstance : IntoValTyped etcdserverpb.LeaseGrantResponse
        etcdserverpb.LeaseGrantResponse.ty), fun l => .rfl⟩,
    ⟨etcdserverpb.LeaseGrantResponse, inferInstance, inferInstance,
      (inferInstance : IntoValTyped etcdserverpb.LeaseGrantResponse
        etcdserverpb.LeaseGrantResponse.ty), fun l => .rfl⟩,
    ?_, ?_⟩
  · intro m
    show leaseGrantRespMsg (GF := GF) null m ⊢ False
    unfold leaseGrantRespMsg
    iintro ⟨%H, -⟩
    exact absurd rfl H
  intro ls l (m : LeaseGrantRespM)
  show leaseGrantRespMsg (GF := GF) ls m ∗ (∃ v : etcdserverpb.LeaseGrantResponse, l ↦ v) ⊢
    WP (storeInto etcdserverpb.LeaseGrantResponse.ty l (leaseGrantRespTree m)) {{ _v, leaseGrantRespMsg ls m ∗ leaseGrantRespMsg l m }}
  iintro ⟨Hs, ⟨%x0, Hl⟩⟩
  iapply wp_fupd
  iapply (storeInto_wp_typed (V := etcdserverpb.LeaseGrantResponse)
    (ty := etcdserverpb.LeaseGrantResponse.ty) l x0)
  simp only [leaseGrantRespTree, treeWp, treeWpL]
  iapply treeWp_hdr
  iintro %h Hh
  repeat (isplitr; · ipureintro; exact isPanic_intoVal _)
  try simp only [isPanic_intoVal]
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
  icases Hl with ⟨-, HH, HI, HT, HE, -, -, -⟩
  imod (typedPointsto_dfractional (GF := GF) _ h).dfractional_persist _ $$ HH with #HH
  imod (typedPointsto_dfractional (GF := GF) _ m.id).dfractional_persist _ $$ HI with #HI
  imod (typedPointsto_dfractional (GF := GF) _ m.ttl).dfractional_persist _ $$ HT with #HT
  imod (typedPointsto_dfractional (GF := GF) _ m.err).dfractional_persist _ $$ HE with #HE
  imodintro
  iframe Hs
  unfold leaseGrantRespMsg
  isplitr
  · ipureintro; exact Hnn
  iexists h
  iframe HH Hh HI HT HE

/-! ## `LeaseRevoke` -/

/-- **The store of a lease-revoke request**: its `ID`. -/
def leaseRevokeReqTree (id : w64) : VTree :=
  .strct etcdserverpb.LeaseRevokeRequest.ty [(go!"ID", go.int64)] [.leaf #id]

/-- **`pbLeaseRevokeRequest` with its store.** -/
def pbLeaseRevokeRequestT : ProtoMsgT GF :=
  { pbLeaseRevokeRequest with tree := leaseRevokeReqTree }

/-- **`pbLeaseRevokeRequestT`'s request model is satisfiable.** -/
theorem pbLeaseRevokeRequestT_reqSat : (pbLeaseRevokeRequestT (GF := GF)).ReqSat := by
  refine ⟨⟨etcdserverpb.LeaseRevokeRequest, inferInstance, inferInstance,
      (inferInstance : IntoValTyped etcdserverpb.LeaseRevokeRequest
        etcdserverpb.LeaseRevokeRequest.ty), fun l => .rfl⟩,
    ⟨etcdserverpb.LeaseRevokeRequest, inferInstance, inferInstance,
      (inferInstance : IntoValTyped etcdserverpb.LeaseRevokeRequest
        etcdserverpb.LeaseRevokeRequest.ty), fun l => .rfl⟩,
    ?_, ?_⟩
  · intro m
    simp only [pbLeaseRevokeRequestT, pbLeaseRevokeRequest]
    iintro ⟨%req, Hp, -⟩
    ihave %H := typedPointsto_not_null $$ Hp
    exact absurd rfl H
  intro ls l m
  simp only [pbLeaseRevokeRequestT, pbLeaseRevokeRequest]
  iintro ⟨⟨%req, Hp, %Hm⟩, %Hw, Hl⟩
  obtain ⟨rfl, Hu⟩ := Hm
  iapply wp_fupd
  iapply (storeInto_wp_typed (V := etcdserverpb.LeaseRevokeRequest)
    (ty := etcdserverpb.LeaseRevokeRequest.ty) l (zero_val etcdserverpb.LeaseRevokeRequest))
  simp only [leaseRevokeReqTree, treeWp, treeWpL, isPanic_intoVal]
  simp [litBody, strctKes, kesσ, envσ]
  repeat (isplitr; · ipureintro; trivial)
  wp_auto
  iexists _
  isplitr
  · ipureintro; rfl
  iframe Hl
  iintro Hl
  isplitl [Hp]
  · iexists req
    iframe Hp
    ipureintro; exact ⟨by simp, Hu⟩
  ihave %Hnn := typedPointsto_not_null $$ Hl
  icases typedPointsto_split _ _ _ $$ Hl with Hl
  simp only [TypedPointsto.typedPointstoDef]
  icases Hl with ⟨-, HI, -, -, -⟩
  imod (typedPointsto_dfractional (GF := GF) _ req.ID').dfractional_persist _ $$ HI with #HI
  imodintro
  iframe HI
  ipureintro; exact Hnn

theorem pbLeaseRevokeRequestT_wireLen_ok :
    ∃ m, (pbLeaseRevokeRequestT (GF := GF)).wireLen m < grpcMsgMax :=
  ⟨(0 : w64), by simp [pbLeaseRevokeRequestT, pbLeaseRevokeRequest, wireSlack, grpcMsgMax]⟩

/-- **The store of a lease-revoke response**: its header. -/
def leaseRevokeRespTree (m : LeaseRevokeRespM) : VTree :=
  .strct etcdserverpb.LeaseRevokeResponse.ty
    [(go!"Header", go.GoType.PointerType etcdserverpb.ResponseHeader.ty)] [hdrTree m.hdr]

/-- **`pbLeaseRevokeResponse` with its store.** -/
def pbLeaseRevokeResponseT : ProtoMsgT GF :=
  { pbLeaseRevokeResponse with tree := leaseRevokeRespTree }

/-- **`pbLeaseRevokeResponseT`'s reply model is satisfiable.** -/
theorem pbLeaseRevokeResponseT_repSat : (pbLeaseRevokeResponseT (GF := GF)).RepSat := by
  apply ProtoMsgT.repSat_of_recvOwn_true _ (fun _ _ => rfl)
  refine ⟨⟨etcdserverpb.LeaseRevokeResponse, inferInstance, inferInstance,
      (inferInstance : IntoValTyped etcdserverpb.LeaseRevokeResponse
        etcdserverpb.LeaseRevokeResponse.ty), fun l => .rfl⟩,
    ⟨etcdserverpb.LeaseRevokeResponse, inferInstance, inferInstance,
      (inferInstance : IntoValTyped etcdserverpb.LeaseRevokeResponse
        etcdserverpb.LeaseRevokeResponse.ty), fun l => .rfl⟩,
    ?_, ?_⟩
  · intro m
    show leaseRevokeRespMsg (GF := GF) null m ⊢ False
    unfold leaseRevokeRespMsg
    iintro ⟨%H, -⟩
    exact absurd rfl H
  intro ls l (m : LeaseRevokeRespM)
  show leaseRevokeRespMsg (GF := GF) ls m ∗ (∃ v : etcdserverpb.LeaseRevokeResponse, l ↦ v) ⊢
    WP (storeInto etcdserverpb.LeaseRevokeResponse.ty l (leaseRevokeRespTree m)) {{ _v, leaseRevokeRespMsg ls m ∗ leaseRevokeRespMsg l m }}
  iintro ⟨Hs, ⟨%x0, Hl⟩⟩
  iapply wp_fupd
  iapply (storeInto_wp_typed (V := etcdserverpb.LeaseRevokeResponse)
    (ty := etcdserverpb.LeaseRevokeResponse.ty) l x0)
  simp only [leaseRevokeRespTree, treeWp, treeWpL]
  iapply treeWp_hdr
  iintro %h Hh
  repeat (isplitr; · ipureintro; exact isPanic_intoVal _)
  try simp only [isPanic_intoVal]
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
  icases Hl with ⟨-, HH, -, -, -⟩
  imod (typedPointsto_dfractional (GF := GF) _ h).dfractional_persist _ $$ HH with #HH
  imodintro
  iframe Hs
  unfold leaseRevokeRespMsg
  isplitr
  · ipureintro; exact Hnn
  iexists h
  iframe HH Hh

/-! ## `LeaseTimeToLive` -/

/-- **The store of a lease time-to-live request**: its `ID` and `Keys`. -/
def leaseTTLReqTree (m : w64 × Bool) : VTree :=
  .strct etcdserverpb.LeaseTimeToLiveRequest.ty [(go!"ID", go.int64), (go!"Keys", go.bool)]
    [.leaf #m.1, .leaf #m.2]

/-- **`pbLeaseTimeToLiveRequest` with its store.** -/
def pbLeaseTimeToLiveRequestT : ProtoMsgT GF :=
  { pbLeaseTimeToLiveRequest with tree := leaseTTLReqTree }

/-- **`pbLeaseTimeToLiveRequestT`'s request model is satisfiable.** -/
theorem pbLeaseTimeToLiveRequestT_reqSat : (pbLeaseTimeToLiveRequestT (GF := GF)).ReqSat := by
  refine ⟨⟨etcdserverpb.LeaseTimeToLiveRequest, inferInstance, inferInstance,
      (inferInstance : IntoValTyped etcdserverpb.LeaseTimeToLiveRequest
        etcdserverpb.LeaseTimeToLiveRequest.ty), fun l => .rfl⟩,
    ⟨etcdserverpb.LeaseTimeToLiveRequest, inferInstance, inferInstance,
      (inferInstance : IntoValTyped etcdserverpb.LeaseTimeToLiveRequest
        etcdserverpb.LeaseTimeToLiveRequest.ty), fun l => .rfl⟩,
    ?_, ?_⟩
  · intro m
    simp only [pbLeaseTimeToLiveRequestT, pbLeaseTimeToLiveRequest]
    iintro ⟨%req, Hp, -⟩
    ihave %H := typedPointsto_not_null $$ Hp
    exact absurd rfl H
  intro ls l m
  simp only [pbLeaseTimeToLiveRequestT, pbLeaseTimeToLiveRequest]
  iintro ⟨⟨%req, Hp, %Hm⟩, %Hw, Hl⟩
  obtain ⟨rfl, Hu⟩ := Hm
  iapply wp_fupd
  iapply (storeInto_wp_typed (V := etcdserverpb.LeaseTimeToLiveRequest)
    (ty := etcdserverpb.LeaseTimeToLiveRequest.ty) l
    (zero_val etcdserverpb.LeaseTimeToLiveRequest))
  simp only [leaseTTLReqTree, treeWp, treeWpL, isPanic_intoVal]
  simp [litBody, strctKes, kesσ, envσ]
  repeat (isplitr; · ipureintro; trivial)
  wp_auto
  iexists _
  isplitr
  · ipureintro; rfl
  iframe Hl
  iintro Hl
  isplitl [Hp]
  · iexists req
    iframe Hp
    ipureintro; exact ⟨by simp, Hu⟩
  imod (typedPointsto_dfractional (GF := GF) l _).dfractional_persist _ $$ Hl with #Hl
  imodintro
  isplitl
  · iexists _
    iframe Hl
    ipureintro; exact ⟨rfl, rfl⟩
  · ipureintro; trivial

theorem pbLeaseTimeToLiveRequestT_wireLen_ok :
    ∃ m, (pbLeaseTimeToLiveRequestT (GF := GF)).wireLen m < grpcMsgMax :=
  ⟨(0, false), by simp [pbLeaseTimeToLiveRequestT, pbLeaseTimeToLiveRequest, wireSlack,
    grpcMsgMax]⟩

/-- **The store of a lease time-to-live response**: its header, `ID`, `TTL`, `GrantedTTL`; its
`Keys` `nil` (the model does not carry them: see the file header). -/
def leaseTTLRespTree (m : LeaseTTLRespM) : VTree :=
  .strct etcdserverpb.LeaseTimeToLiveResponse.ty
    [(go!"Header", go.GoType.PointerType etcdserverpb.ResponseHeader.ty), (go!"ID", go.int64),
     (go!"TTL", go.int64), (go!"GrantedTTL", go.int64),
     (go!"Keys", go.GoType.SliceType (go.GoType.SliceType go.byte))]
    [hdrTree m.hdr, .leaf #m.id, .leaf #m.ttl, .leaf #m.grantedTtl, .leaf #slice.nil]

/-- **`pbLeaseTimeToLiveResponse` with its store.** -/
def pbLeaseTimeToLiveResponseT : ProtoMsgT GF :=
  { pbLeaseTimeToLiveResponse with tree := leaseTTLRespTree }

/-- **`pbLeaseTimeToLiveResponseT`'s reply model is satisfiable.** -/
theorem pbLeaseTimeToLiveResponseT_repSat : (pbLeaseTimeToLiveResponseT (GF := GF)).RepSat := by
  apply ProtoMsgT.repSat_of_recvOwn_true _ (fun _ _ => rfl)
  refine ⟨⟨etcdserverpb.LeaseTimeToLiveResponse, inferInstance, inferInstance,
      (inferInstance : IntoValTyped etcdserverpb.LeaseTimeToLiveResponse
        etcdserverpb.LeaseTimeToLiveResponse.ty), fun l => .rfl⟩,
    ⟨etcdserverpb.LeaseTimeToLiveResponse, inferInstance, inferInstance,
      (inferInstance : IntoValTyped etcdserverpb.LeaseTimeToLiveResponse
        etcdserverpb.LeaseTimeToLiveResponse.ty), fun l => .rfl⟩,
    ?_, ?_⟩
  · intro m
    show leaseTTLRespMsg (GF := GF) null m ⊢ False
    unfold leaseTTLRespMsg
    iintro ⟨%H, -⟩
    exact absurd rfl H
  intro ls l (m : LeaseTTLRespM)
  show leaseTTLRespMsg (GF := GF) ls m ∗ (∃ v : etcdserverpb.LeaseTimeToLiveResponse, l ↦ v) ⊢
    WP (storeInto etcdserverpb.LeaseTimeToLiveResponse.ty l (leaseTTLRespTree m)) {{ _v, leaseTTLRespMsg ls m ∗ leaseTTLRespMsg l m }}
  iintro ⟨Hs, ⟨%x0, Hl⟩⟩
  iapply wp_fupd
  iapply (storeInto_wp_typed (V := etcdserverpb.LeaseTimeToLiveResponse)
    (ty := etcdserverpb.LeaseTimeToLiveResponse.ty) l x0)
  simp only [leaseTTLRespTree, treeWp, treeWpL]
  iapply treeWp_hdr
  iintro %h Hh
  repeat (isplitr; · ipureintro; exact isPanic_intoVal _)
  try simp only [isPanic_intoVal]
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
  icases Hl with ⟨-, HH, HI, HT, HG, HK, -, -, -⟩
  imod (typedPointsto_dfractional (GF := GF) _ h).dfractional_persist _ $$ HH with #HH
  imod (typedPointsto_dfractional (GF := GF) _ m.id).dfractional_persist _ $$ HI with #HI
  imod (typedPointsto_dfractional (GF := GF) _ m.ttl).dfractional_persist _ $$ HT with #HT
  imod (typedPointsto_dfractional (GF := GF) _ m.grantedTtl).dfractional_persist _ $$ HG with #HG
  imod (typedPointsto_dfractional (GF := GF) _ slice.nil).dfractional_persist _ $$ HK with #HK
  imodintro
  iframe Hs
  unfold leaseTTLRespMsg
  isplitr
  · ipureintro; exact Hnn
  iexists h, slice.nil
  iframe HH Hh HI HT HG HK

/-! ## `LeaseLeases` -/

/-- **The store of a lease-list request** (no field). -/
def leaseLeasesReqTree (_ : Unit) : VTree :=
  .strct etcdserverpb.LeaseLeasesRequest.ty [] []

/-- **`pbLeaseLeasesRequest` with its store.** -/
def pbLeaseLeasesRequestT : ProtoMsgT GF :=
  { pbLeaseLeasesRequest with tree := leaseLeasesReqTree }

/-- **`pbLeaseLeasesRequestT`'s request model is satisfiable.** -/
theorem pbLeaseLeasesRequestT_reqSat : (pbLeaseLeasesRequestT (GF := GF)).ReqSat := by
  refine ⟨⟨etcdserverpb.LeaseLeasesRequest, inferInstance, inferInstance,
      (inferInstance : IntoValTyped etcdserverpb.LeaseLeasesRequest
        etcdserverpb.LeaseLeasesRequest.ty), fun l => .rfl⟩,
    ⟨etcdserverpb.LeaseLeasesRequest, inferInstance, inferInstance,
      (inferInstance : IntoValTyped etcdserverpb.LeaseLeasesRequest
        etcdserverpb.LeaseLeasesRequest.ty), fun l => .rfl⟩,
    ?_, ?_⟩
  · intro m
    simp only [pbLeaseLeasesRequestT, pbLeaseLeasesRequest]
    iintro ⟨%req, Hp, -⟩
    ihave %H := typedPointsto_not_null $$ Hp
    exact absurd rfl H
  intro ls l m
  simp only [pbLeaseLeasesRequestT, pbLeaseLeasesRequest]
  iintro ⟨Hs, %Hw, Hl⟩
  iapply wp_fupd
  iapply (storeInto_wp_typed (V := etcdserverpb.LeaseLeasesRequest)
    (ty := etcdserverpb.LeaseLeasesRequest.ty) l (zero_val etcdserverpb.LeaseLeasesRequest))
  simp only [leaseLeasesReqTree, treeWp, treeWpL]
  try simp [litBody, strctKes, kesσ]
  repeat (isplitr; · ipureintro; trivial)
  wp_auto
  iexists _
  isplitr
  · ipureintro; rfl
  iframe Hl
  iintro -
  imodintro
  iframe Hs
  isplit <;> ipureintro <;> trivial

theorem pbLeaseLeasesRequestT_wireLen_ok :
    ∃ m, (pbLeaseLeasesRequestT (GF := GF)).wireLen m < grpcMsgMax :=
  ⟨(), by simp [pbLeaseLeasesRequestT, pbLeaseLeasesRequest, wireSlack, grpcMsgMax]⟩

/-- **The store of a lease status** (a fresh `*LeaseStatus`): its `ID`. -/
def leaseStatusTree (id : w64) : VTree :=
  .ptr etcdserverpb.LeaseStatus.ty
    (.strct etcdserverpb.LeaseStatus.ty [(go!"ID", go.int64)] [.leaf #id])

/-- **The store of a lease-list response**: its header and its leases (`nil` if none). -/
def leaseLeasesRespTree (m : LeaseLeasesRespM) : VTree :=
  .strct etcdserverpb.LeaseLeasesResponse.ty
    [(go!"Header", go.GoType.PointerType etcdserverpb.ResponseHeader.ty),
     (go!"Leases", go.GoType.SliceType (go.GoType.PointerType etcdserverpb.LeaseStatus.ty))]
    [hdrTree m.hdr,
     sliceTree (go.GoType.PointerType etcdserverpb.LeaseStatus.ty) (m.ids.map leaseStatusTree)]

/-- **`pbLeaseLeasesResponse` with its store.** -/
def pbLeaseLeasesResponseT : ProtoMsgT GF :=
  { pbLeaseLeasesResponse with tree := leaseLeasesRespTree }

theorem treeWp_leaseStatus (id : w64) (Φ : val → IProp GF) :
    (∀ p : Loc, structFieldRef etcdserverpb.LeaseStatus go!"ID" p ↦□ id -∗ Φ #p) ⊢
      treeWp (leaseStatusTree id) Φ := by
  iintro H
  unfold leaseStatusTree
  iapply (treeWp_ptr_fupd (V := etcdserverpb.LeaseStatus))
  simp only [treeWp, treeWpL, isPanic_intoVal]
  simp [litBody, strctKes, kesσ, envσ]
  repeat (isplitr; · ipureintro; trivial)
  wp_auto
  iexists _
  isplitr
  · ipureintro; rfl
  iintro %p Hp
  icases typedPointsto_split _ _ _ $$ Hp with Hp
  simp only [TypedPointsto.typedPointstoDef]
  icases Hp with ⟨-, HI, -, -, -⟩
  imod (typedPointsto_dfractional (GF := GF) _ id).dfractional_persist _ $$ HI with #HI
  imodintro
  iapply H
  iexact HI

theorem leasesIs_of_sepL2 (ids : List w64) (ps : List Loc) :
    ([∗list] id;p ∈ ids;ps, structFieldRef etcdserverpb.LeaseStatus go!"ID" p ↦□ id : IProp GF) ⊢
      iprop(⌜ps.length = ids.length⌝ ∗
        [∗list] k ↦ p ∈ ps, ∃ id : w64, ⌜ids[k]? = some id⌝ ∗
          structFieldRef etcdserverpb.LeaseStatus go!"ID" p ↦□ id) := by
  iintro #H
  ihave %Hl := BigSepL2.bigSepL2_length $$ H
  isplitr
  · ipureintro; exact Hl.symm
  have key : ∀ (k : Nat) (p : Loc), ps[k]? = some p →
      (iprop(□ [∗list] id;p ∈ ids;ps, structFieldRef etcdserverpb.LeaseStatus go!"ID" p ↦□ id) :
        IProp GF) ⊢
        (iprop(∃ id : w64, ⌜ids[k]? = some id⌝ ∗
          structFieldRef etcdserverpb.LeaseStatus go!"ID" p ↦□ id) : IProp GF) := by
    intro k p hp
    have hk : k < ids.length := by
      have := (List.getElem?_eq_some_iff.mp hp).1; omega
    obtain ⟨id, hid⟩ : ∃ id, ids[k]? = some id := ⟨ids[k], List.getElem?_eq_getElem hk⟩
    iintro #H
    iexists id
    isplitr
    · ipureintro; exact hid
    iapply (BigSepL2.bigSepL2_lookup hid hp) $$ H
  iapply (BigSepL.bigSepL_intro key)
  imodintro
  iexact H

/-- **`pbLeaseLeasesResponseT`'s reply model is satisfiable.** -/
theorem pbLeaseLeasesResponseT_repSat : (pbLeaseLeasesResponseT (GF := GF)).RepSat := by
  apply ProtoMsgT.repSat_of_recvOwn_true _ (fun _ _ => rfl)
  refine ⟨⟨etcdserverpb.LeaseLeasesResponse, inferInstance, inferInstance,
      (inferInstance : IntoValTyped etcdserverpb.LeaseLeasesResponse
        etcdserverpb.LeaseLeasesResponse.ty), fun l => .rfl⟩,
    ⟨etcdserverpb.LeaseLeasesResponse, inferInstance, inferInstance,
      (inferInstance : IntoValTyped etcdserverpb.LeaseLeasesResponse
        etcdserverpb.LeaseLeasesResponse.ty), fun l => .rfl⟩,
    ?_, ?_⟩
  · intro m
    show leaseLeasesRespMsg (GF := GF) null m ⊢ False
    unfold leaseLeasesRespMsg
    iintro ⟨%H, -⟩
    exact absurd rfl H
  intro ls l (m : LeaseLeasesRespM)
  show leaseLeasesRespMsg (GF := GF) ls m ∗ (∃ v : etcdserverpb.LeaseLeasesResponse, l ↦ v) ⊢
    WP (storeInto etcdserverpb.LeaseLeasesResponse.ty l (leaseLeasesRespTree m)) {{ _v, leaseLeasesRespMsg ls m ∗ leaseLeasesRespMsg l m }}
  iintro ⟨Hs, ⟨%x0, Hl⟩⟩
  iapply wp_fupd
  iapply (storeInto_wp_typed (V := etcdserverpb.LeaseLeasesResponse)
    (ty := etcdserverpb.LeaseLeasesResponse.ty) l x0)
  simp only [leaseLeasesRespTree, treeWp, treeWpL]
  iapply treeWp_hdr
  iintro %h Hh
  isplitr
  · ipureintro; exact isPanic_intoVal h
  iapply (treeWp_sliceMap (V := Loc) leaseStatusTree
    (fun id p => iprop(structFieldRef etcdserverpb.LeaseStatus go!"ID" p ↦□ id))
    (fun a Φ => treeWp_leaseStatus a Φ))
  iintro %ps %sl %Hps Hids Hsl -
  isplitr
  · ipureintro; exact isPanic_intoVal sl
  try simp only [isPanic_intoVal]
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
  icases Hl with ⟨-, HH, HL, -, -, -⟩
  imod (typedPointsto_dfractional (GF := GF) _ h).dfractional_persist _ $$ HH with #HH
  imod (typedPointsto_dfractional (GF := GF) _ sl).dfractional_persist _ $$ HL with #HL
  imod ownSlice_persist _ _ _ $$ Hsl with #Hsl
  ihave ⟨%Hlen, #Hids⟩ := leasesIs_of_sepL2 m.ids ps $$ Hids
  imodintro
  iframe Hs
  unfold leaseLeasesRespMsg
  isplitr
  · ipureintro; exact Hnn
  iexists h, sl, ps
  iframe HH Hh HL Hsl Hids
  ipureintro; exact Hlen

/-! ## Registrations -/

/-- **`LeaseGrantRequest`'s registration** (stage A: the one model of the Go type
`LeaseGrantRequest` as a method's request). -/
axiom pbLeaseGrantRequestT_reg :
    grpcReqModelOf GF etcdserverpb.LeaseGrantRequest.ty = some (pbLeaseGrantRequestT (GF := GF))

/-- **`LeaseGrantResponse`'s registration** (stage A: the one model of the Go type
`LeaseGrantResponse` as a method's reply). -/
axiom pbLeaseGrantResponseT_reg :
    grpcRepModelOf GF etcdserverpb.LeaseGrantResponse.ty = some (pbLeaseGrantResponseT (GF := GF))

/-- **`LeaseRevokeRequest`'s registration** (stage A: the one model of the Go type
`LeaseRevokeRequest` as a method's request). -/
axiom pbLeaseRevokeRequestT_reg :
    grpcReqModelOf GF etcdserverpb.LeaseRevokeRequest.ty = some (pbLeaseRevokeRequestT (GF := GF))

/-- **`LeaseRevokeResponse`'s registration** (stage A: the one model of the Go type
`LeaseRevokeResponse` as a method's reply). -/
axiom pbLeaseRevokeResponseT_reg :
    grpcRepModelOf GF etcdserverpb.LeaseRevokeResponse.ty =
      some (pbLeaseRevokeResponseT (GF := GF))

/-- **`LeaseTimeToLiveRequest`'s registration** (stage A: the one model of the Go type
`LeaseTimeToLiveRequest` as a method's request). -/
axiom pbLeaseTimeToLiveRequestT_reg :
    grpcReqModelOf GF etcdserverpb.LeaseTimeToLiveRequest.ty =
      some (pbLeaseTimeToLiveRequestT (GF := GF))

/-- **`LeaseTimeToLiveResponse`'s registration** (stage A: the one model of the Go type
`LeaseTimeToLiveResponse` as a method's reply). -/
axiom pbLeaseTimeToLiveResponseT_reg :
    grpcRepModelOf GF etcdserverpb.LeaseTimeToLiveResponse.ty =
      some (pbLeaseTimeToLiveResponseT (GF := GF))

/-- **`LeaseLeasesRequest`'s registration** (stage A: the one model of the Go type
`LeaseLeasesRequest` as a method's request). -/
axiom pbLeaseLeasesRequestT_reg :
    grpcReqModelOf GF etcdserverpb.LeaseLeasesRequest.ty = some (pbLeaseLeasesRequestT (GF := GF))

/-- **`LeaseLeasesResponse`'s registration** (stage A: the one model of the Go type
`LeaseLeasesResponse` as a method's reply). -/
axiom pbLeaseLeasesResponseT_reg :
    grpcRepModelOf GF etcdserverpb.LeaseLeasesResponse.ty =
      some (pbLeaseLeasesResponseT (GF := GF))

end defs

end EtcdGrove
end Perennial
