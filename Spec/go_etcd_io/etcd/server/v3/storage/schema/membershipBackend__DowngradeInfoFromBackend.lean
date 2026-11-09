/-
## `(*membershipBackend).DowngradeInfoFromBackend()`: assumed (names only)

**Users.** `RaftCluster.Recover` (`cluster.go:259`, 2e). Snippet: `examples/specreq/schema/schema.go` (`ReqMembersSaveRead`).

**Assumed** (`membership.go`): `be.ReadTx()`, `RLock()` (the caller's thread token), `UnsafeRange(Cluster, downgrade, nil, 0)`, `json.Unmarshal` (the stored JSON: no error), `semver.NewVersion(TargetVersion)` if enabled (the premise: it parses, else `lg.Panic`), `RUnlock()`. The buckets' records are as `memberBkts` says (the API's
header); a read transaction sees them as their only writer left them (the holder is outside a write
section: `specs-ref`'s `TestBksReadInsidePendingBatch`).

**Changes.** From `specs-ref`'s `membershipBackend__DowngradeInfoFromBackend.lean` where there was one (over the real
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

/-- **The stored downgrade info** (`nil` if none). -/
def membershipBackend.DowngradeInfoFromBackend.spec : Prop :=
  ∀ (mb lg : Loc) (be : GoInterface) (cb : Option ClusterBkts),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ (mb ↦□ (go_etcd_io.etcd.server.v3.storage.schema.membershipBackend.mk lg be) : IProp GF) ∗ Zap.isLogger lg ∗ memberBkts be cb ∗ threadTok ∗ ⌜∀ c t, cb = some c → c.dg = some (true, t) → (Semver.parse t).isSome⌝ }}
    (App (Val (mb @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.membershipBackend.ty @!! go!"DowngradeInfoFromBackend")) (Val #()))
  {{ (p : Loc), RET #p; memberBkts be cb ∗ threadTok ∗ match cb.bind (·.dg) with | none => iprop(⌜p = null⌝) | some x => iprop(∃ v : go_etcd_io.etcd.server.v3.etcdserver.version.DowngradeInfo, p ↦ v ∗ ⌜(v.Enabled', v.TargetVersion') = x⌝) }}

end spec
end Schema
end EtcdGrove
end Perennial
