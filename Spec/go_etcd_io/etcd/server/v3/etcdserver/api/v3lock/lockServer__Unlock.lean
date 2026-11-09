/-
## `(*lockServer).Unlock(ctx, req)` (`lock.go:52-58`): translated

**Users.** The `Unlock` RPC; `ReqLockOverInProc`. **Proof sketch.** The client's `Delete` of the key
(W0's `KV.DeleteTriple`, its update built from the lent permission with `delEff`).
**Changes** (from `specs-ref`'s `lockServer__Unlock.lean`): over the permission. **Margin.** The
deletion's state is not stated.

**The principal** (round 1, completeness F9): the in-process client (`v3client.New(s)`, default
principal `dflt`: none) forwards each call's token, so the call's principal is the context's `who`
(`ClientV3.ctxPrin dflt ctx who`), the effects under it, as 1d's specs state them. `v3client.New`'s
spec (an `isClient … none` from `isServer`) is requested of 1c (`req/…client_v3.md`, "from 2e,
round 1").
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
  ∀ (ls c : Loc) (γ : Cluster) (dflt who : Principal) (ctx : GoInterface) (σ0 : State) (req : Loc) (key : GoString) (T : State → State → Prop) (P : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3lock ∗ isLockServer ls c ∗ ClientV3.isClient c γ dflt ∗ Context.ctxOk ctx ∗ ClientV3.ctxPrin dflt ctx who ∗ etcdLb γ σ0 ∗ unlockReq req key ∗
      etcdLent γ T P ∗ P ∗ ⌜effIn (delEff (fun k => k = key)) T⌝ }}
    (App (App (Val (ls @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3lock.lockServer.ty @!! go!"Unlock")) (Val #ctx)) (Val #req))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (⌜err = GoInterface.nil⌝ ∗ unlockResp resp) ∨ ⌜err ≠ GoInterface.nil⌝ }}

end spec

end V3lock
end EtcdGrove
end Perennial
