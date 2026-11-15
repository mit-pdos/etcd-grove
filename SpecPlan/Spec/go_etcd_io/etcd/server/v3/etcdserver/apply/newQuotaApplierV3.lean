/-
`newQuotaApplierV3(lg, quotaBackendBytesCfg, be, app)` (`quota.go:32-34`): the quota applier over `app`, with `NewBackendQuota(lg, cfg, be, "v3-applier")`.

**Users.** `newApplierV3`.

**Proof sketch.** 2e's `ServerStorage.NewBackendQuota.spec` (`isQuota`); allocation.

**Changes** from `specs-ref`'s file of the same name: no `backendUnderQuota`; restated over the new vocabulary (`beAt`, `stAt`, `applierAt`, the model state); one spec for every mode.

**Margin.** None.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.ApiResult

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Apply

open Iris Iris.BI EtcdModel

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- **The quota applier over `app`.** -/
def newQuotaApplierV3.spec : Prop :=
  ∀ (lg : Loc) (qb : w64) (be app : GoInterface) (b aa : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗ Zap.isLogger lg ∗ ServerStorage.beReadable be ∗ applierAt app [Layer.backend] b aa }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.apply.newQuotaApplierV3)) (Val #lg)) (Val #qb)) (Val #be)) (Val #app))
  {{ (v : GoInterface), RET #v; applierAt v [Layer.quota, Layer.backend] b aa }}

end spec

end Apply
end EtcdGrove
end Perennial
