/-
## `(*membershipBackend).MustSaveClusterVersionToBackend(ver)`: assumed (names only)

**Users.** `RaftCluster.SetVersion` with `shouldApplyV3` (`cluster.go:614`, 2e; 3a's `ClusterVersionSet`). Snippet: `examples/specreq/schema/schema.go` (`ReqMembersSaveRead`).

**Assumed** (`membership.go`): `be.BatchTx()`, `LockInsideApply()` (`applyHook`), `UnsafePut(Cluster, clusterVersion, []byte(ver.String()))` (`Semver.Version.String.spec`), `Unlock()`. The buckets' records are as `memberBkts` says (the API's
header); a read transaction sees them as their only writer left them (the holder is outside a write
section: `specs-ref`'s `TestBksReadInsidePendingBatch`).

**Changes.** From `specs-ref`'s `membershipBackend__MustSaveClusterVersionToBackend.lean` where there was one (over the real
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

/-- **Stores the cluster version** (the post-lock hook run). -/
def membershipBackend.MustSaveClusterVersionToBackend.spec : Prop :=
  ∀ (mb lg : Loc) (be : GoInterface) (cb : ClusterBkts) (ver : Loc) (sv : Semver.SemVer) (Pre Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ (mb ↦□ (go_etcd_io.etcd.server.v3.storage.schema.membershipBackend.mk lg be) : IProp GF) ∗ memberBkts be (some cb) ∗ Semver.verAt ver sv ∗ applyHook be Pre Q ∗ Pre }}
    (App (Val (mb @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.membershipBackend.ty @!! go!"MustSaveClusterVersionToBackend")) (Val #ver))
  {{ RET #(); memberBkts be (some { cb with ver := some sv }) ∗ Q }}

end spec
end Schema
end EtcdGrove
end Perennial
