/-
## `(*lockServer).Unlock(ctx, req)` (`lock.go:52-58`): translated

**Users.** The `Unlock` RPC. **Proof sketch.** The client's `Delete` of the key (W0's
`KV.DeleteTriple` at the client, its update built from `etcdPerm` with `delEff`).
**Changes** (from `specs-ref`'s `lockServer__Unlock.lean`): over the permission. **Margin.** The
deletion's state is not stated.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3lock.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace V3lock

open Iris Iris.BI EtcdModel ClientV3 Concurrency

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3lock.Assumptions]

/-- **Releases the lock**: deletes its key. -/
def lockServer.Unlock.spec : Prop :=
  ∀ (ls c : Loc) (γ : Cluster) (who : Principal) (ctx : GoInterface) (req : Loc) (key : GoString)
    (T : State → State → Prop),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3lock ∗ isLockServer ls c ∗ ClientV3.isClient c γ who ∗ Context.ctxOk ctx ∗ ClientV3.ctxPrin ctx who ∗ unlockReq req key ∗
      etcdPerm γ T ∗ ⌜effIn (delEff (fun k => k = key)) T⌝ }}
    (App (App (Val (ls @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3lock.lockServer.ty @!! go!"Unlock")) (Val #ctx)) (Val #req))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (⌜err = GoInterface.nil⌝ ∗ unlockResp resp) ∨ ⌜err ≠ GoInterface.nil⌝ }}

end spec

end V3lock
end EtcdGrove
end Perennial
