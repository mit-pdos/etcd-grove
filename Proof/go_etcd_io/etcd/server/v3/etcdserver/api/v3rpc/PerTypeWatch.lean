/-
**Per-type prototype: the watch stream's messages at registered types** (stage A prototype; the
Scope's V for `StreamMsg`): `WatchRequest` (`StreamMsgT.ReqStore`: its oneof, a create request
with its key and range end `nil` if empty) and `WatchResponse` (`StreamMsgT.RepSat`: the header,
the flags, the events, each with its key-value and previous key-value).

The request side's `send null m ⊢ False` is proved: `watchReqSend` says the message is not `nil`
(`⌜l ≠ null⌝`, stage A; the client's `watchRequest.toPB` builds a fresh one). The request's
`OwnAny` and its store are proved too (`pbWatchRequestT_reqSat`).
-/
module

public import Proof.google_golang_org.grpc.InvGrpcStream
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvWatchStream

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace v3rpc

open Iris Iris.BI go_etcd_io.etcd.api.v3

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [pkg_pb : go_etcd_io.etcd.api.v3.etcdserverpb.Assumptions]
variable [pkg_mvccpb : go_etcd_io.etcd.api.v3.mvccpb.Assumptions]

/-! ## Watch requests -/

/-- **The store of a create request** (`nil` key, range end and filters if empty). -/
def createReqTree (c : CreateReqM) : VTree :=
  .ptr etcdserverpb.WatchCreateRequest.ty (.strct etcdserverpb.WatchCreateRequest.ty
    [(go!"Key", go.GoType.SliceType go.byte), (go!"RangeEnd", go.GoType.SliceType go.byte),
     (go!"StartRevision", go.int64), (go!"ProgressNotify", go.bool),
     (go!"Filters", go.GoType.SliceType etcdserverpb.WatchCreateRequest_FilterType.ty),
     (go!"PrevKv", go.bool), (go!"WatchId", go.int64), (go!"Fragment", go.bool)]
    [bytesTree go.byte c.key, bytesTree go.byte c.rangeEnd, .leaf #c.startRev,
     .leaf #c.progressNotify, bytesTree etcdserverpb.WatchCreateRequest_FilterType.ty c.filters,
     .leaf #c.prevKv, .leaf #c.watchId, .leaf #c.fragment])

/-- **A oneof's wrapper** `wty` holding, in its field `fname`, a fresh inner message. -/
def oneofTree (wty : go.GoType) (fname : GoString) (ity : go.GoType) (inner : VTree) : VTree :=
  .ptr wty (.strct wty [(fname, go.GoType.PointerType ity)] [inner])

/-- **The store of a cancel request.** -/
def cancelReqTree (id : w64) : VTree :=
  .ptr etcdserverpb.WatchCancelRequest.ty (.strct etcdserverpb.WatchCancelRequest.ty
    [(go!"WatchId", go.int64)] [.leaf #id])

/-- **The store of a progress request** (no field). -/
def progressReqTree : VTree :=
  .ptr etcdserverpb.WatchProgressRequest.ty (.strct etcdserverpb.WatchProgressRequest.ty [] [])

/-- **The store of a watch request**: its oneof's wrapper and inner request (always allocated,
as protobuf-go decodes a present oneof field), or no oneof. -/
def watchReqTree : WatchReqM → VTree
  | .create c => .strct etcdserverpb.WatchRequest.ty
      [(go!"RequestUnion", go.GoType.PointerType etcdserverpb.WatchRequest_CreateRequest.ty)]
      [oneofTree etcdserverpb.WatchRequest_CreateRequest.ty go!"CreateRequest"
        etcdserverpb.WatchCreateRequest.ty (createReqTree c)]
  | .cancel id => .strct etcdserverpb.WatchRequest.ty
      [(go!"RequestUnion", go.GoType.PointerType etcdserverpb.WatchRequest_CancelRequest.ty)]
      [oneofTree etcdserverpb.WatchRequest_CancelRequest.ty go!"CancelRequest"
        etcdserverpb.WatchCancelRequest.ty (cancelReqTree id)]
  | .progress => .strct etcdserverpb.WatchRequest.ty
      [(go!"RequestUnion", go.GoType.PointerType etcdserverpb.WatchRequest_ProgressRequest.ty)]
      [oneofTree etcdserverpb.WatchRequest_ProgressRequest.ty go!"ProgressRequest"
        etcdserverpb.WatchProgressRequest.ty progressReqTree]
  | .other => .strct etcdserverpb.WatchRequest.ty [] []

/-- **`pbWatchRequest` with its store.** -/
def pbWatchRequestT : StreamMsgT GF :=
  { pbWatchRequest with tree := watchReqTree }

theorem treeWp_createReq (c : CreateReqM) (Φ : val → IProp GF)
    (hk : c.key.length < 2 ^ 63 - 1) :
    (∀ p : Loc, createReqOwn p c -∗ Φ #p) ⊢ treeWp (createReqTree c) Φ := by
  iintro H
  unfold createReqTree
  iapply (treeWp_ptr_fupd (V := etcdserverpb.WatchCreateRequest))
  simp only [treeWp, treeWpL]
  iapply treeWp_bytes
  iintro %ksl %Hks Hks -
  repeat (isplitr; · ipureintro; exact isPanic_intoVal _)
  iapply treeWp_bytes
  iintro %esl %Hes Hes -
  repeat (isplitr; · ipureintro; exact isPanic_intoVal _)
  iapply treeWp_bytes
  iintro %fsl %Hfs Hfs -
  repeat (isplitr; · ipureintro; exact isPanic_intoVal _)
  simp [litBody, strctKes, kesσ, envσ]
  repeat (isplitr; · ipureintro; trivial)
  wp_auto
  iexists _
  isplitr
  · ipureintro; rfl
  iintro %p Hp
  ihave %Hnn := typedPointsto_not_null $$ Hp
  icases typedPointsto_split _ _ _ $$ Hp with Hp
  simp only [TypedPointsto.typedPointstoDef]
  icases Hp with ⟨-, HK, HE, HS, HPN, HF, HPK, HW, HFr, -, -, -⟩
  imod (typedPointsto_dfractional (GF := GF) _ c.startRev).dfractional_persist _ $$ HS with #HS
  imod (typedPointsto_dfractional (GF := GF) _ c.progressNotify).dfractional_persist _ $$ HPN with #HPN
  imod (typedPointsto_dfractional (GF := GF) _ fsl).dfractional_persist _ $$ HF with #HF
  imod (typedPointsto_dfractional (GF := GF) _ c.prevKv).dfractional_persist _ $$ HPK with #HPK
  imod (typedPointsto_dfractional (GF := GF) _ c.watchId).dfractional_persist _ $$ HW with #HW
  imod (typedPointsto_dfractional (GF := GF) _ c.fragment).dfractional_persist _ $$ HFr with #HFr
  imod ownSlice_persist _ _ _ $$ Hks with #Hks
  imod ownSlice_persist _ _ _ $$ Hes with #Hes
  imod ownSlice_persist _ _ _ $$ Hfs with #Hfs
  imodintro
  iapply H
  unfold createReqOwn
  isplitr
  · ipureintro; exact ⟨Hnn, hk⟩
  iexists ksl, esl, fsl
  iframe HK Hks HE Hes HS HPN HF Hfs HPK HW HFr

/-- **`pbWatchRequestT`'s store gives the decoded request.** -/
theorem pbWatchRequestT_reqStore : (pbWatchRequestT (GF := GF)).ReqStore := by
  intro ls l m
  simp only [pbWatchRequestT, pbWatchRequest]
  iintro ⟨Hs, %Hw, ⟨%x0, Hl⟩⟩
  iapply wp_fupd
  iapply (storeInto_wp_typed (V := etcdserverpb.WatchRequest)
    (ty := etcdserverpb.WatchRequest.ty) l x0)
  cases m with
  | create c =>
    have hk : c.key.length < 2 ^ 63 - 1 := by
      simp only [watchReqWireLen, wireSlack, grpcMsgMax] at Hw; omega
    simp only [watchReqTree, treeWp, treeWpL]
    unfold oneofTree
    iapply (treeWp_ptr_fupd (V := etcdserverpb.WatchRequest_CreateRequest))
    simp only [treeWp, treeWpL]
    iapply treeWp_createReq c _ hk
    iintro %cr Hcr
    repeat (isplitr; · ipureintro; exact isPanic_intoVal _)
    try simp [litBody, strctKes, kesσ, envσ]
    repeat (isplitr; · ipureintro; trivial)
    wp_auto
    iexists _
    isplitr
    · ipureintro; rfl
    iintro %w Hw
    icases typedPointsto_split _ _ _ $$ Hw with Hw
    simp only [TypedPointsto.typedPointstoDef]
    icases Hw with ⟨HC, -⟩
    imod (typedPointsto_dfractional (GF := GF) _ cr).dfractional_persist _ $$ HC with #HC
    imodintro
    try simp [litBody, strctKes, kesσ, envσ]
    repeat (isplitr; · ipureintro; trivial)
    wp_auto
    iexists _
    isplitr
    · ipureintro; rfl
    iframe Hl
    iintro Hl
    icases typedPointsto_split _ _ _ $$ Hl with Hl
    simp only [TypedPointsto.typedPointstoDef]
    icases Hl with ⟨-, HU, -⟩
    imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ HU with #HU
    imodintro
    iframe Hs
    unfold watchReqRecv
    iexists _
    iframe HU
    iexists cr
    iframe Hcr
    unfold oneofCreate
    iexists w
    iframe HC
    ipureintro; rfl
  | cancel id =>
    simp only [watchReqTree, treeWp, treeWpL]
    unfold oneofTree
    iapply (treeWp_ptr_fupd (V := etcdserverpb.WatchRequest_CancelRequest))
    simp only [treeWp, treeWpL]
    unfold cancelReqTree
    iapply (treeWp_ptr_fupd (V := etcdserverpb.WatchCancelRequest))
    simp only [treeWp, treeWpL, isPanic_intoVal]
    simp [litBody, strctKes, kesσ, envσ]
    repeat (isplitr; · ipureintro; trivial)
    wp_auto
    iexists _
    isplitr
    · ipureintro; rfl
    iintro %cr Hcr
    ihave %Hcnn := typedPointsto_not_null $$ Hcr
    icases typedPointsto_split _ _ _ $$ Hcr with Hcr
    simp only [TypedPointsto.typedPointstoDef]
    icases Hcr with ⟨-, HI, -, -, -⟩
    imod (typedPointsto_dfractional (GF := GF) _ id).dfractional_persist _ $$ HI with #HI
    imodintro
    repeat (isplitr; · ipureintro; exact isPanic_intoVal _)
    try simp [litBody, strctKes, kesσ, envσ]
    repeat (isplitr; · ipureintro; trivial)
    wp_auto
    iexists _
    isplitr
    · ipureintro; rfl
    iintro %w Hw
    icases typedPointsto_split _ _ _ $$ Hw with Hw
    simp only [TypedPointsto.typedPointstoDef]
    icases Hw with ⟨HC, -⟩
    imod (typedPointsto_dfractional (GF := GF) _ cr).dfractional_persist _ $$ HC with #HC
    imodintro
    try simp [litBody, strctKes, kesσ, envσ]
    repeat (isplitr; · ipureintro; trivial)
    wp_auto
    iexists _
    isplitr
    · ipureintro; rfl
    iframe Hl
    iintro Hl
    icases typedPointsto_split _ _ _ $$ Hl with Hl
    simp only [TypedPointsto.typedPointstoDef]
    icases Hl with ⟨-, HU, -⟩
    imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ HU with #HU
    imodintro
    iframe Hs
    unfold watchReqRecv
    iexists _
    iframe HU
    iexists cr
    isplitr
    · ipureintro; exact Hcnn
    iframe HI
    unfold oneofCancel
    iexists w
    iframe HC
    ipureintro; rfl
  | progress =>
    simp only [watchReqTree, treeWp, treeWpL]
    unfold oneofTree
    iapply (treeWp_ptr_fupd (V := etcdserverpb.WatchRequest_ProgressRequest))
    simp only [treeWp, treeWpL]
    unfold progressReqTree
    iapply (treeWp_ptr_fupd (V := etcdserverpb.WatchProgressRequest))
    simp only [treeWp, treeWpL]
    try simp [litBody, strctKes, kesσ, envσ]
    repeat (isplitr; · ipureintro; trivial)
    wp_auto
    iexists _
    isplitr
    · ipureintro; rfl
    iintro %cr Hcr
    ihave %Hcnn := typedPointsto_not_null $$ Hcr
    imodintro
    repeat (isplitr; · ipureintro; exact isPanic_intoVal _)
    try simp [litBody, strctKes, kesσ, envσ]
    repeat (isplitr; · ipureintro; trivial)
    wp_auto
    iexists _
    isplitr
    · ipureintro; rfl
    iintro %w Hw
    icases typedPointsto_split _ _ _ $$ Hw with Hw
    simp only [TypedPointsto.typedPointstoDef]
    icases Hw with ⟨HC, -⟩
    imod (typedPointsto_dfractional (GF := GF) _ cr).dfractional_persist _ $$ HC with #HC
    imodintro
    try simp [litBody, strctKes, kesσ, envσ]
    repeat (isplitr; · ipureintro; trivial)
    wp_auto
    iexists _
    isplitr
    · ipureintro; rfl
    iframe Hl
    iintro Hl
    icases typedPointsto_split _ _ _ $$ Hl with Hl
    simp only [TypedPointsto.typedPointstoDef]
    icases Hl with ⟨-, HU, -⟩
    imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ HU with #HU
    imodintro
    iframe Hs
    unfold watchReqRecv
    iexists _
    iframe HU
    iexists cr
    isplitr
    · ipureintro; exact Hcnn
    unfold oneofProgress
    iexists w
    iframe HC
    ipureintro; rfl
  | other =>
    simp only [watchReqTree, treeWp, treeWpL]
    try simp [litBody, strctKes, kesσ, envσ]
    repeat (isplitr; · ipureintro; trivial)
    wp_auto
    iexists _
    isplitr
    · ipureintro; rfl
    iframe Hl
    iintro Hl
    icases typedPointsto_split _ _ _ $$ Hl with Hl
    simp only [TypedPointsto.typedPointstoDef]
    icases Hl with ⟨-, HU, -⟩
    imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ HU with #HU
    imodintro
    iframe Hs
    unfold watchReqRecv
    iexists _
    iframe HU
    ileft
    ipureintro; rfl

/-! ## Watch responses -/

/-- **The store of a response header** (always present). -/
def hdrTreeW (h : HdrM) : VTree :=
  .ptr etcdserverpb.ResponseHeader.ty (.strct etcdserverpb.ResponseHeader.ty
    [(go!"ClusterId", go.uint64), (go!"MemberId", go.uint64), (go!"Revision", go.int64),
     (go!"RaftTerm", go.uint64), (go!"LeaderId", go.uint64)]
    [.leaf #h.clusterId, .leaf #h.memberId, .leaf #h.revision, .leaf #h.raftTerm, .leaf #h.leaderId])

/-- **The store of a key-value** (`nil` key and value if empty). -/
def kvTreeW (v : EtcdKv) : VTree :=
  .ptr mvccpb.KeyValue.ty (.strct mvccpb.KeyValue.ty
    [(go!"Key", go.GoType.SliceType go.byte), (go!"CreateRevision", go.int64),
     (go!"ModRevision", go.int64), (go!"Version", go.int64),
     (go!"Value", go.GoType.SliceType go.byte), (go!"Lease", go.int64)]
    [bytesTree go.byte v.key, .leaf #v.createRev, .leaf #v.modRev, .leaf #v.version,
     bytesTree go.byte v.value, .leaf #v.lease])

/-- **The store of an event**: its type, its key-value, its previous key-value or `nil`. -/
def evTree (ev : mvcc.EvM) : VTree :=
  .ptr mvccpb.Event.ty (.strct mvccpb.Event.ty
    [(go!"Type", mvccpb.Event_EventType.ty), (go!"Kv", go.GoType.PointerType mvccpb.KeyValue.ty),
     (go!"PrevKv", go.GoType.PointerType mvccpb.KeyValue.ty)]
    [.leaf #(mvcc.evType ev), kvTreeW ev.kv,
     match ev.prevKv with | none => .leaf #(null : Loc) | some pk => kvTreeW pk])

/-- **The store of a watch response.** -/
def watchRespTree (m : WatchRespM) : VTree :=
  .strct etcdserverpb.WatchResponse.ty
    [(go!"Header", go.GoType.PointerType etcdserverpb.ResponseHeader.ty), (go!"WatchId", go.int64),
     (go!"Created", go.bool), (go!"Canceled", go.bool), (go!"CompactRevision", go.int64),
     (go!"CancelReason", go.string), (go!"Fragment", go.bool),
     (go!"Events", go.GoType.SliceType (go.GoType.PointerType mvccpb.Event.ty))]
    [hdrTreeW m.hdr, .leaf #m.watchId, .leaf #m.created, .leaf #m.canceled, .leaf #m.compactRev,
     .leaf #m.cancelReason, .leaf #m.fragment,
     sliceTree (go.GoType.PointerType mvccpb.Event.ty) (m.evs.map evTree)]

/-- **`pbWatchResponse` with its store.** -/
def pbWatchResponseT : StreamMsgT GF :=
  { pbWatchResponse with tree := watchRespTree }

theorem treeWp_hdrOwn (h : HdrM) (Φ : val → IProp GF) :
    (∀ p : Loc, hdrOwn p h -∗ Φ #p) ⊢ treeWp (hdrTreeW h) Φ := by
  iintro H
  unfold hdrTreeW
  iapply (treeWp_ptr (V := etcdserverpb.ResponseHeader))
  simp only [treeWp, treeWpL, isPanic_intoVal]
  simp [litBody, strctKes, kesσ, envσ]
  repeat (isplitr; · ipureintro; trivial)
  wp_auto
  iexists _
  isplitr
  · ipureintro; rfl
  iintro %p Hp
  ihave %Hnn := typedPointsto_not_null $$ Hp
  icases typedPointsto_split _ _ _ $$ Hp with Hp
  simp only [TypedPointsto.typedPointstoDef]
  icases Hp with ⟨-, HC, HM, HR, HT, HL, -, -, -⟩
  iapply H
  unfold hdrOwn
  iframe HC HM HR HT HL
  ipureintro; exact Hnn

theorem treeWp_kvFixed (v : EtcdKv) (Φ : val → IProp GF) :
    (∀ p : Loc, ⌜p ≠ null⌝ -∗ mvcc.kvPtrFixed p v -∗ Φ #p) ⊢ treeWp (kvTreeW v) Φ := by
  iintro H
  unfold kvTreeW
  iapply (treeWp_ptr_fupd (V := mvccpb.KeyValue))
  simp only [treeWp, treeWpL]
  iapply treeWp_bytes
  iintro %ksl %Hks Hks -
  repeat (isplitr; · ipureintro; exact isPanic_intoVal _)
  iapply treeWp_bytes
  iintro %vsl %Hvs Hvs -
  repeat (isplitr; · ipureintro; exact isPanic_intoVal _)
  simp [litBody, strctKes, kesσ, envσ]
  repeat (isplitr; · ipureintro; trivial)
  wp_auto
  iexists _
  isplitr
  · ipureintro; rfl
  iintro %p Hp
  ihave %Hnn := typedPointsto_not_null $$ Hp
  imod (typedPointsto_dfractional (GF := GF) p _).dfractional_persist _ $$ Hp with #Hp
  imod ownSlice_persist _ _ _ $$ Hks with #Hks
  imod ownSlice_persist _ _ _ $$ Hvs with #Hvs
  imodintro
  iapply H $$ %p %Hnn
  unfold mvcc.kvPtrFixed
  iexists ksl, vsl, _, _, _
  iframe Hks Hvs
  iexact Hp

theorem treeWp_ev (ev : mvcc.EvM) (Φ : val → IProp GF) :
    (∀ p : Loc, mvcc.evIs p ev -∗ Φ #p) ⊢ treeWp (evTree ev) Φ := by
  iintro H
  unfold evTree
  iapply (treeWp_ptr_fupd (V := mvccpb.Event))
  simp only [treeWp, treeWpL]
  isplitr
  · ipureintro; exact isPanic_intoVal _
  iapply treeWp_kvFixed
  iintro %kp %Hknn #Hkp
  isplitr
  · ipureintro; exact isPanic_intoVal _
  cases hpk : ev.prevKv with
  | none =>
    simp only [treeWp, treeWpL, isPanic_intoVal]
    simp [litBody, strctKes, kesσ, envσ]
    repeat (isplitr; · ipureintro; trivial)
    wp_auto
    iexists _
    isplitr
    · ipureintro; rfl
    iintro %p Hp
    ihave %Hnn := typedPointsto_not_null $$ Hp
    imod (typedPointsto_dfractional (GF := GF) p _).dfractional_persist _ $$ Hp with #Hp
    imodintro
    iapply H
    unfold mvcc.evIs
    iexists kp, null, _, _, _
    rw [hpk]
    iframe Hp Hkp
    ipureintro; exact ⟨⟨Hnn, Hknn⟩, rfl⟩
  | some pk =>
    iapply treeWp_kvFixed
    iintro %qp %Hqnn #Hqp
    simp only [isPanic_intoVal]
    simp [litBody, strctKes, kesσ, envσ]
    repeat (isplitr; · ipureintro; trivial)
    wp_auto
    iexists _
    isplitr
    · ipureintro; rfl
    iintro %p Hp
    ihave %Hnn := typedPointsto_not_null $$ Hp
    imod (typedPointsto_dfractional (GF := GF) p _).dfractional_persist _ $$ Hp with #Hp
    imodintro
    iapply H
    unfold mvcc.evIs
    iexists kp, qp, _, _, _
    rw [hpk]
    iframe Hp Hkp Hqp
    ipureintro; exact ⟨Hnn, Hknn⟩

/-- **`pbWatchResponseT`'s reply model is satisfiable.** -/
theorem pbWatchResponseT_repSat : (pbWatchResponseT (GF := GF)).RepSat := by
  refine ⟨⟨etcdserverpb.WatchResponse, inferInstance, inferInstance,
      (inferInstance : IntoValTyped etcdserverpb.WatchResponse etcdserverpb.WatchResponse.ty),
      fun l => .rfl⟩, ?_, ?_⟩
  · intro m
    simp only [pbWatchResponseT, pbWatchResponse, watchRespMsg]
    iintro ⟨%H, -⟩
    exact absurd rfl H
  intro ls l m
  simp only [pbWatchResponseT, pbWatchResponse]
  iintro ⟨Hs, ⟨%x0, Hl⟩⟩
  iapply wp_fupd
  iapply (storeInto_wp_typed (V := etcdserverpb.WatchResponse)
    (ty := etcdserverpb.WatchResponse.ty) l x0)
  simp only [watchRespTree, treeWp, treeWpL]
  iapply treeWp_hdrOwn
  iintro %h Hh
  repeat (isplitr; · ipureintro; exact isPanic_intoVal _)
  iapply (treeWp_sliceMap (V := Loc) evTree (fun ev p => mvcc.evIs (GF := GF) p ev)
    (fun a Φ => treeWp_ev a Φ))
  iintro %ps %sl %Hps Hevs Hsl -
  isplitr
  · ipureintro; exact isPanic_intoVal sl
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
  icases Hl with ⟨-, HH, HW, HCr, HCa, HCo, HR, HF, HE, -, -, -⟩
  imod ownSlice_persist _ _ _ $$ Hsl with #Hsl
  ihave Hevs := (BigSepL2.bigSepL2_flip).2 $$ Hevs
  ihave Hevs := (BigSepL2.bigSepL2_alt).1 $$ Hevs
  icases Hevs with ⟨%Hlen, Hevs⟩
  imodintro
  iframe Hs
  unfold watchRespRecv
  isplitr
  · ipureintro; exact Hnn
  iexists h, sl, ps
  iframe HH Hh HW HCr HCa HCo HR HF HE Hsl Hevs
  ipureintro; exact Hlen

/-- **`pbWatchRequestT`'s request model is satisfiable.** -/
theorem pbWatchRequestT_reqSat : (pbWatchRequestT (GF := GF)).ReqSat := by
  refine ⟨⟨etcdserverpb.WatchRequest, inferInstance, inferInstance,
      (inferInstance : IntoValTyped etcdserverpb.WatchRequest etcdserverpb.WatchRequest.ty),
      fun _ => .rfl⟩, ?_, pbWatchRequestT_reqStore⟩
  intro m
  simp only [pbWatchRequestT, pbWatchRequest, watchReqSend]
  iintro ⟨%H, -⟩
  exact absurd rfl H

/-- **A watch request fits a gRPC message** (rule 7's witness that `wireLen` is not the default). -/
theorem pbWatchRequestT_wireLen_ok : ∃ m, (pbWatchRequestT (GF := GF)).wireLen m < grpcMsgMax :=
  ⟨.other, by simp [pbWatchRequestT, pbWatchRequest, watchReqWireLen, wireSlack, grpcMsgMax]⟩

/-- **`WatchRequest`'s registration** (the stream request registry; its `Sat` is
`pbWatchRequestT_reqSat`). -/
axiom pbWatchRequestT_reg :
    streamReqModelOf GF etcdserverpb.WatchRequest.ty = some (pbWatchRequestT (GF := GF))

/-- **`WatchResponse`'s registration** (the stream reply registry; its `Sat` is
`pbWatchResponseT_repSat`). -/
axiom pbWatchResponseT_reg :
    streamRepModelOf GF etcdserverpb.WatchResponse.ty = some (pbWatchResponseT (GF := GF))

end defs

end v3rpc
end EtcdGrove
end Perennial
