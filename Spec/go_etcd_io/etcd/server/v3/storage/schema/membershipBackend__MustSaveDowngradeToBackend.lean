/-
## `(*membershipBackend).MustSaveDowngradeToBackend(d)`: assumed (names only)

**Users.** `RaftCluster.SetDowngradeInfo` with `shouldApplyV3` (`cluster.go:814`, 2e; 3a's `DowngradeInfoSet`). Snippet: `examples/specreq/schema/schema.go` (`ReqMembersSaveRead`).

**Assumed** (`membership.go`): `json.Marshal(d)` (a `bool` and a string: no error, `lg.Panic` unreachable), `be.BatchTx()`, `LockInsideApply()` (`applyHook`), `UnsafePut(Cluster, downgrade, json)`, `Unlock()`. The buckets' records are as `memberBkts` says (the API's
header); a read transaction sees them as their only writer left them (the holder is outside a write
section: `specs-ref`'s `TestBksReadInsidePendingBatch`).

**Changes.** From `specs-ref`'s `membershipBackend__MustSaveDowngradeToBackend.lean` where there was one (over the real
backend's ghost names): over the schema's `memberBkts`. **Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.schema.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Schema

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

/-- **Stores the downgrade info** (the post-lock hook run). -/
def membershipBackend.MustSaveDowngradeToBackend.spec : Prop :=
  ∀ (mb lg : Loc) (be : GoInterface) (cb : ClusterBkts) (d : Loc) (dq : DFrac) (v : go_etcd_io.etcd.server.v3.etcdserver.version.DowngradeInfo) (Pre Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ (mb ↦□ (go_etcd_io.etcd.server.v3.storage.schema.membershipBackend.mk lg be) : IProp GF) ∗ Zap.isLogger lg ∗ memberBkts be (some cb) ∗ d ↦{dq} v ∗ applyHook be Pre Q ∗ Pre }}
    (App (Val (mb @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.membershipBackend.ty @!! go!"MustSaveDowngradeToBackend")) (Val #d))
  {{ RET #(); memberBkts be (some { cb with dg := some (v.Enabled', v.TargetVersion') }) ∗ d ↦{dq} v ∗ Q }}

end spec
end Schema
end EtcdGrove
end Perennial
