/-
**The lease keep-alive stream's messages** (`/etcdserverpb.Lease/LeaseKeepAlive`; a trusted wire
model, shared by both ends: the client's lessor, `client/v3/InvLessor.lean`, and the server's
handler, `v3rpc/InvLeaseKeepAlive.lean`; moved from the client's `InvLessor.lean` on 2026-11-01,
the keep-alive stream's stage, `notes/lease-keepalive-plan.md`, K2). Lean-first (no Rocq
counterpart).

**A request** (`pbLeaseKeepAliveRequest`, model `KaReqM`): its `ID`, on the wire, and two ghost
bounds the client's content of the request may vouch for (`nb`, the auth store's published index;
`mb`, the lessor's history index: the bounds the server's verdict is at), not on the wire, as
watch's create `bound`. The owned struct on both ends.

**A response** (`pbLeaseKeepAliveResponse`): its `(ID, TTL)` and some header, read-only on both
ends (`keepAliveRespMsg`).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvOp
public import Proof.google_golang_org.grpc.InvGrpcStream

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

/-- **A keep-alive request's model**: its `ID` (on the wire) and the client's ghost bounds `nb`
(the auth store's published index) and `mb` (the lessor's history index). -/
structure KaReqM where
  id : w64
  nb : Nat
  mb : Nat

instance KaReqM.countable : Pos.Countable KaReqM :=
  .ofInjective (fun q => Pos.Countable.encode (q.id, q.nb, q.mb))
    (fun a b h => by
      have := Pos.encode_inj h
      cases a; cases b; simp_all)

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The `*pb.LeaseKeepAliveResponse` `l` holds `(ID, TTL)`** (read-only, with some header). -/
def keepAliveRespMsg (l : Loc) (m : w64 × w64) : IProp GF :=
  iprop(⌜l ≠ null⌝ ∗ ∃ h : Loc,
    structFieldRef etcdserverpb.LeaseKeepAliveResponse go!"Header" l ↦□ h ∗
    structFieldRef etcdserverpb.LeaseKeepAliveResponse go!"ID" l ↦□ m.1 ∗
    structFieldRef etcdserverpb.LeaseKeepAliveResponse go!"TTL" l ↦□ m.2)

instance keepAliveRespMsg_persistent (l : Loc) (m : w64 × w64) :
    Persistent (keepAliveRespMsg (GF := GF) l m) := by
  unfold keepAliveRespMsg; infer_instance

/-- **The keep-alive requests on the wire** (a trusted wire model): a request's `ID`, the owned
struct on both ends; the ghost bounds ride along (the transport delivers the model `send` holds
at). -/
abbrev pbLeaseKeepAliveRequest : StreamMsg GF where
  ty := etcdserverpb.LeaseKeepAliveRequest.ty
  M := KaReqM
  cnt := inferInstance
  send l q := iprop(∃ v : etcdserverpb.LeaseKeepAliveRequest, l ↦ v ∗
    ⌜q.id = v.ID' ∧ v.unknownFields' = slice.nil⌝)
  wireLen _ := wireSlack
  recv l q := iprop(∃ v : etcdserverpb.LeaseKeepAliveRequest, l ↦ v ∗ ⌜q.id = v.ID'⌝)
  own l := iprop(∃ v : etcdserverpb.LeaseKeepAliveRequest, l ↦ v)

/-- **The keep-alive responses on the wire** (a trusted wire model): a response's `(ID, TTL)`,
read-only on both ends (`keepAliveRespMsg`). -/
abbrev pbLeaseKeepAliveResponse : StreamMsg GF where
  ty := etcdserverpb.LeaseKeepAliveResponse.ty
  M := w64 × w64
  cnt := inferInstance
  send := keepAliveRespMsg
  recv := keepAliveRespMsg
  own l := iprop(∃ v : etcdserverpb.LeaseKeepAliveResponse, l ↦ v)

end defs

end EtcdGrove
end Perennial
