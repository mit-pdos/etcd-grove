/-
## `(*membershipBackend).MustCreateBackendBuckets()`: assumed (names only)

**Users.** `RaftCluster.Recover` (`cluster.go:249`, 2e). Snippet: `examples/specreq/schema/schema.go` (`ReqMembersSaveRead`).

**Assumed** (`membership.go`): `be.BatchTx()`, `LockOutsideApply()` (no hook), three `UnsafeCreateBucket`s, `Unlock()`. The buckets' records are as `memberBkts` says (the API's
header); a read transaction sees them as their only writer left them (the holder is outside a write
section: `specs-ref`'s `TestBksReadInsidePendingBatch`).

**Changes.** From `specs-ref`'s `membershipBackend__MustCreateBackendBuckets.lean` where there was one (over the real
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

/-- **Creates the three buckets** (if absent). -/
def membershipBackend.MustCreateBackendBuckets.spec : Prop :=
  ∀ (mb lg : Loc) (be : GoInterface) (cb : Option ClusterBkts),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ (mb ↦□ (go_etcd_io.etcd.server.v3.storage.schema.membershipBackend.mk lg be) : IProp GF) ∗ memberBkts be cb }}
    (App (Val (mb @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.membershipBackend.ty @!! go!"MustCreateBackendBuckets")) (Val #()))
  {{ RET #(); memberBkts be (some (cb.getD ClusterBkts.empty)) }}

end spec
end Schema
end EtcdGrove
end Perennial
