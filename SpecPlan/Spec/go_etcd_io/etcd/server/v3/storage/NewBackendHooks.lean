/-
## `NewBackendHooks(lg, indexer)` (`hooks.go:39-41`): translated

**Users.** `bootstrapBackend` (names only). **Proof sketch.** A struct literal; the mutex's
invariant holds the pending configuration (none). **Changes**: from `specs-ref`. **Margin.** None.
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

/-- **The backend's commit hooks** over the consistent indexer `ci`. -/
def NewBackendHooks.spec : Prop :=
  ∀ (lg : Loc) (ci : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage ∗ Zap.isLogger lg }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.NewBackendHooks)) (Val #lg)) (Val #ci))
  {{ (h : Loc), RET #h; isHooks h ci }}

end spec

end ServerStorage
end EtcdGrove
end Perennial
