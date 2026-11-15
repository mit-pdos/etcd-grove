/-
## `(*ServerConfig).BackendPath()` (`config.go`)

**Users.** `bootstrap`, `OpenBackend`, `OpenSnapshotBackend` (2d's `applySnapshot`). **Proof sketch.** names only: trusted (`datadir.ToBackendFileName`). **Changes**: from `specs-ref`'s
`ServerConfig__BackendPath.lean` where it existed (`config.backendPathOf`); `walDirOf` keyed by both
directories (the WAL API's critique 3). **Margin.** Exact (the path is opaque).
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.config.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Config

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.config.Assumptions]

/-- **`BackendPath()`**: the backend file's path under the data directory. -/
def ServerConfig.BackendPath.spec : Prop :=
  ∀ (c : Loc) (datadir : GoString),
  {{ (typedPointsto (structFieldRef go_etcd_io.etcd.server.v3.config.ServerConfig go!"DataDir" c) datadir DFrac.discard : IProp GF) }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.config.ServerConfig.ty @!! go!"BackendPath")) (Val #()))
  {{ RET #(Config.backendPathOf datadir); True }}

end spec

end Config
end EtcdGrove
end Perennial
