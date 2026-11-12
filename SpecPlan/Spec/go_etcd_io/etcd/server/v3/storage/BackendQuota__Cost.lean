/-
## `(*BackendQuota).Cost(req)` (`quota.go:129-175`): trusted (names only)

**Users.** 3a's capped applier, 2a's quota interceptors: with a `*PutRequest`, a `*TxnRequest` or
a `*LeaseGrantRequest`.
**Why it is true.** The type switch of `Cost` (`panic("unexpected cost")` for any other type:
`quotaReq`'s premise), the request's encoded size (`proto.Size`, reading the message);
`Available` adds the backend's `Size()` (an atomic read, `beReadable`).
**Changes** (from `specs-ref`'s `BackendQuota__Cost.lean`): the three request kinds as a premise.
**Margin.** The answer is not tied to the model: a refusal on `false` is a `Step` refusal.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.Api
public import SpecPlan.Spec.go_etcd_io.raft.v3.Api
public import SpecPlan.Spec.go_uber_org.zap.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ServerStorage

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.Assumptions]

/-- **`Cost(req)`**: the request's cost (some `int`). -/
def BackendQuota.Cost.spec : Prop :=
  ∀ (p : Loc) (v : GoInterface) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage ∗ isQuota (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.BackendQuota.ty) #p) ∗
      quotaReq v dq }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.BackendQuota.ty @!! go!"Cost")) (Val #v))
  {{ (n : w64), RET #n; quotaReq v dq }}

end spec

end ServerStorage
end EtcdGrove
end Perennial
