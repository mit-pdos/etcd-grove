/-
`(*lockServer).Lock(ctx, req)` (`server/etcdserver/api/v3lock/lock.go`; the auth plan's A3c,
2026-10-24). Lean-first (no Rocq counterpart); see `v3lock/Defs.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3lock.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace v3lock

open Iris Iris.BI go_etcd_io.etcd.client.v3.concurrency concurrency
  _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.v3lock

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.v3lock.Assumptions]

/-- **`Lock(ctx, req)`**: on a lock server over a client meeting `lockClientOk`, for a request
whose name is `name` and lease `lease`, and a cancelable request context, it makes only these
client calls: a session over the lease (`NewSession`, `WithLease(lease)`, `WithContext(ctx)`),
`Orphan`, and a mutex on `name` (`NewMutex`, `Lock(ctx)`), so its keys are under `name/`. It returns
the response `{Header, Key}` of a lock the mutex holds (`lockedAt`, or the key recreated,
`keyRecreated`: `Mutex.Lock`'s), whose key is under `name/`, or no response and an error.

The name is at most the server's receive limit long (`v3rpc.grpcRecvBytesOk`, the receive-size
fact: grpc's server decoded the request under etcd's limit `v3rpc.etcdMaxRecvMsgSize maxReq`,
`maxReq` the configuration's `MaxRequestBytes`, which meets `v3rpc.etcdMaxRequestBytesOk`;
2026-10-30, `notes/decisions.md`, "The receive-size fact"). -/
abbrev lockServer.Lock.spec : Prop :=
  ∀ (ls c req : Loc) (nsl : GoSlice) (name : GoString) (lease : w64) (ctx : GoInterfaceOk)
    (cs : context.ContextDesc (IProp GF)) (maxReq : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3lock ∗
      isLockServer ls c ∗ lockClientOk c ∗
      structFieldRef v3lockpb.LockRequest go!"Name" req ↦□ nsl ∗
      nsl ↦*□ name ∗
      ⌜v3rpc.etcdMaxRequestBytesOk maxReq ∧
        v3rpc.grpcRecvBytesOk (v3rpc.etcdMaxRecvMsgSize maxReq) name⌝ ∗
      structFieldRef v3lockpb.LockRequest go!"Lease" req ↦□ lease ∗
      context.isContext ctx cs ∗ context.isCancelCtxCtx ctx cs }}
    (App (App (Val (ls @!! go.GoType.PointerType lockServer.ty @!! go!"Lock"))
      (Val #(GoInterface.ok ctx))) (Val #req))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ (key : GoString) (rev R : w64) (hdr : Loc) (ksl : GoSlice)
          (v : v3lockpb.LockResponse),
        resp ↦ v ∗ ⌜v.Header' = hdr ∧ v.Key' = ksl⌝ ∗ ksl ↦* key ∗ hdrRevAt hdr R ∗
        etcdReached R ∗ (lockedAt (name ++ go!"/") key rev R ∨ keyRecreated (name ++ go!"/") key rev R) ∗
        ⌜(name ++ go!"/") <+: key⌝) ∨
      ⌜resp = null ∧ err ≠ GoInterface.nil⌝ }}

end spec

end v3lock
end EtcdGrove
end Perennial
