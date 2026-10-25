/-
`(*lockServer).Unlock(ctx, req)` (`server/etcdserver/api/v3lock/lock.go`; the auth plan's A3c,
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.v3lock.Assumptions]

/-- **`Unlock(ctx, req)`**: on a lock server over a client meeting `unlockKVOk`, it makes one
client call, the delete of the request's key (`c.Delete(ctx, key)`), and returns the response
`{Header}` of that delete with its result (`deleteResult` of the key), or no response and the
delete's error. -/
abbrev lockServer.Unlock.spec : Prop :=
  ∀ (ls c req : Loc) (ksl : GoSlice) (key : GoString) (ctx : GoInterfaceOk)
    (cs : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3lock ∗
      isLockServer ls c ∗ unlockKVOk c ∗
      structFieldRef v3lockpb.UnlockRequest go!"Key" req ↦□ ksl ∗
      ksl ↦*□ key ∗
      context.isContext ctx cs }}
    (App (App (Val (ls @!! go.GoType.PointerType lockServer.ty @!! go!"Unlock"))
      (Val #(GoInterface.ok ctx))) (Val #req))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ (hdr : Loc) (v : v3lockpb.UnlockResponse),
        resp ↦ v ∗ ⌜v.Header' = hdr⌝ ∗
        deleteResult [] (W64 0) (opDeleteModel key []) GoInterface.nil) ∨
      ⌜resp = null ∧ err ≠ GoInterface.nil⌝ }}

end spec

end v3lock
end EtcdGrove
end Perennial
