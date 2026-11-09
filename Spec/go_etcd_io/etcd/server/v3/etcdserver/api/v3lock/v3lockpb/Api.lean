/-
# `v3lockpb`'s messages (batch 3h, round 1: 2e's request 2)

The lock service's messages (`server/etcdserver/api/v3lock/v3lockpb`, translated with its getters),
owned as 2e's provisional predicates in `V3lock`'s `Api.lean` said, same signatures: `lockReq`,
`unlockReq` (read-only requests, as gRPC hands them to the handler: persistent), `lockResp`,
`unlockResp` (fresh replies). Each is `Proto.msgAt` of a content holding its model (relation laws,
as `EtcdServerPb`'s); the relations are functional in the content.

Mapping for integration: `V3lock.lockReq`, `unlockReq`, `lockResp`, `unlockResp` become these.
Intended realization: as `etcdserverpb/Api.lean`'s (the field-level predicate is `msgAt`'s
realization at each type; a request read-only for good; a reply's header a `respHeaderOwn`).
-/
module

public import Spec.google_golang_org.protobuf.proto.Api
public import Spec.go_etcd_io.etcd.api.v3.Wire
public import GeneratedProof.go_etcd_io.etcd.server.v3.etcdserver.api.v3lock.v3lockpb
public import Spec.PkgInit.go_etcd_io.etcd.server.v3.etcdserver.api.v3lock.v3lockpb

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace V3lockpb

open Iris Iris.BI EtcdWire
open go_etcd_io.etcd.server.v3.etcdserver.api.v3lock

/-- The content is a `LockRequest` for `name` with `lease`. -/
opaque lockReqHolds (c : Proto.Content) (name : GoString) (lease : w64) : Prop
/-- The content is an `UnlockRequest` of `key`. -/
opaque unlockReqHolds (c : Proto.Content) (key : GoString) : Prop
/-- The content is a `LockResponse` holding `key` (the header any). -/
opaque lockRespHolds (c : Proto.Content) (key : GoString) : Prop
/-- The content is an `UnlockResponse`. -/
opaque unlockRespHolds (c : Proto.Content) : Prop

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- A read-only `*LockRequest` (persistent). -/
def lockReq (p : Loc) (name : GoString) (lease : w64) : IProp GF :=
  iprop(∃ c, Proto.msgAt v3lockpb.LockRequest.ty p DFrac.discard c ∗ ⌜lockReqHolds c name lease⌝)
/-- A read-only `*UnlockRequest` (persistent). -/
def unlockReq (p : Loc) (key : GoString) : IProp GF :=
  iprop(∃ c, Proto.msgAt v3lockpb.UnlockRequest.ty p DFrac.discard c ∗ ⌜unlockReqHolds c key⌝)
/-- A fresh `*LockResponse` holding the key. -/
def lockResp (p : Loc) (key : GoString) : IProp GF :=
  iprop(∃ c, Proto.msgAt v3lockpb.LockResponse.ty p (DFrac.own 1) c ∗ ⌜lockRespHolds c key⌝)
/-- A fresh `*UnlockResponse`. -/
def unlockResp (p : Loc) : IProp GF :=
  iprop(∃ c, Proto.msgAt v3lockpb.UnlockResponse.ty p (DFrac.own 1) c ∗ ⌜unlockRespHolds c⌝)

/-- The relations are functional in the content. -/
def holds_fun.spec : Prop :=
  (∀ c n l n' l', lockReqHolds c n l → lockReqHolds c n' l' → n = n' ∧ l = l') ∧
  (∀ c k k', unlockReqHolds c k → unlockReqHolds c k' → k = k') ∧
  (∀ c k k', lockRespHolds c k → lockRespHolds c k' → k = k')

/-- Their fields, for the handlers (`lockServer.Lock` reads `req.Name`, `req.Lease`; `Unlock` reads
`req.Key`): each request content's `Name`/`Lease`/`Key` field holds the model (byte slices
read-only). -/
def fields.spec : Prop :=
  (∀ p c n l, Proto.msgAt (GF := GF) v3lockpb.LockRequest.ty p DFrac.discard c ∗
      ⌜lockReqHolds c n l⌝ ⊢
    ∃ ns : GoSlice, p.[v3lockpb.LockRequest, go!"Name"] ↦□ ns ∗ ns ↦*□ n ∗
      p.[v3lockpb.LockRequest, go!"Lease"] ↦□ l) ∧
  (∀ p c k, Proto.msgAt (GF := GF) v3lockpb.UnlockRequest.ty p DFrac.discard c ∗
      ⌜unlockReqHolds c k⌝ ⊢
    ∃ ks : GoSlice, p.[v3lockpb.UnlockRequest, go!"Key"] ↦□ ks ∗ ks ↦*□ k)

/-- **Building the replies** (`&v3lockpb.LockResponse{Header: resp.Header, Key: m.Key()}`,
`&v3lockpb.UnlockResponse{Header: resp.Header}`): fresh bookkeeping, an owned header or `nil`, the
key read-only. -/
def resp_fold.spec : Prop :=
  (∀ (p h : Loc) (ho : Option HeaderM) (ks : GoSlice) (k : GoString),
    protoRest (GF := GF) v3lockpb.LockResponse p (DFrac.own 1) ∗
      p.[v3lockpb.LockResponse, go!"Header"] ↦ h ∗ optOwn respHeaderOwn h (DFrac.own 1) ho ∗
      p.[v3lockpb.LockResponse, go!"Key"] ↦ ks ∗ ks ↦*□ k ⊢ lockResp p k) ∧
  (∀ (p h : Loc) (ho : Option HeaderM),
    protoRest (GF := GF) v3lockpb.UnlockResponse p (DFrac.own 1) ∗
      p.[v3lockpb.UnlockResponse, go!"Header"] ↦ h ∗ optOwn respHeaderOwn h (DFrac.own 1) ho ⊢
      unlockResp p)

end res

end V3lockpb
end EtcdGrove
end Perennial
