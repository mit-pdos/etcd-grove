/-
## `(*membershipBackend).ClusterVersionFromBackend()`: assumed (names only)

**Users.** `RaftCluster.Recover` (`cluster.go:257`, 2e). Snippet: `examples/specreq/schema/schema.go` (`ReqMembersSaveRead`).

**Assumed** (`membership.go`): `be.ReadTx()`, `RLock()` (the caller's thread token), `UnsafeRange(Cluster, clusterVersion, nil, 0)` (an absent bucket or key: `nil`), `semver.MustParse` of the stored `String()` (the premise: it parses back), `RUnlock()`. The buckets' records are as `memberBkts` says (the API's
header); a read transaction sees them as their only writer left them (the holder is outside a write
section: `specs-ref`'s `TestBksReadInsidePendingBatch`).

**Changes.** From `specs-ref`'s `membershipBackend__ClusterVersionFromBackend.lean` where there was one (over the real
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

/-- **The stored cluster version** (`nil` if none). -/
def membershipBackend.ClusterVersionFromBackend.spec : Prop :=
  ∀ (mb lg : Loc) (be : GoInterface) (cb : Option ClusterBkts),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ (mb ↦□ (go_etcd_io.etcd.server.v3.storage.schema.membershipBackend.mk lg be) : IProp GF) ∗ Zap.isLogger lg ∗ memberBkts be cb ∗ threadTok ∗ ⌜∀ c sv, cb = some c → c.ver = some sv → Semver.parse (Semver.render sv) = some sv⌝ }}
    (App (Val (mb @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.membershipBackend.ty @!! go!"ClusterVersionFromBackend")) (Val #()))
  {{ (p : Loc), RET #p; memberBkts be cb ∗ threadTok ∗ match cb.bind (·.ver) with | none => iprop(⌜p = null⌝) | some sv => Semver.verAt p sv }}

end spec
end Schema
end EtcdGrove
end Perennial
