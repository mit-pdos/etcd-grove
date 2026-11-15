/-
## `NewBackendQuota(lg, quotaBytes, be, name)` (`quota.go:73-127`): trusted (names only)

**Users.** 3a's capped applier (`apply.newQuotaApplierV3`), 2a's quota interceptors
(`v3rpc.NewQuotaKVServer`, `NewQuotaLeaseServer`). Snippet: `etcdserverboot/storage.go`.

**Why it is true.** A `*passthroughQuota` for a negative size, else a `*BackendQuota` over `be`
(the default size for `0`); a metric set; log lines (a logger: `lg.Info` on a nil logger panics).

**Changes** (from `specs-ref`'s `NewBackendQuota.lean`, which carried the workload premise
`apply.backendUnderQuota`): no workload premise: a quota refusal is a `Step` refusal and the
`NOSPACE` alarm an environment step in W0's model. **Margin.** None.
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

/-- **The backend quota** (or none, for a negative size). -/
def NewBackendQuota.spec : Prop :=
  ∀ (lg : Loc) (qb : w64) (be : GoInterface) (name : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage ∗ Zap.isLogger lg ∗ beReadable be }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.NewBackendQuota)) (Val #lg)) (Val #qb)) (Val #be)) (Val #name))
  {{ (q : GoInterface), RET #q; isQuota q }}

end spec

end ServerStorage
end EtcdGrove
end Perennial
