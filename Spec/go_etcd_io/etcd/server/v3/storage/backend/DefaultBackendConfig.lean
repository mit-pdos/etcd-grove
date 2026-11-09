/-
## `DefaultBackendConfig(lg)` (`backend.go:156-163`): translated

**Users.** `serverstorage.OpenBackend` (2e, `storage/backend.go:73`), `NewDefaultBackend`.
**Proof sketch.** Reads the package's `defaultBatchInterval`, `defaultBatchLimit` and
`InitialMmapSize` (initialized globals), builds the struct. **Changes.** New (no old spec).
**Margin.** The interval, limit and mmap size are not stated (any values: the specs do not depend
on them).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Backend

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- **`DefaultBackendConfig(lg)`**: no path, no hooks, the logger `lg`, `Mlock` and
`UnsafeNoFsync` off, blocking defragmentation. -/
def DefaultBackendConfig.spec : Prop :=
  ∀ (lg : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend }}
    (App (Val (@! go_etcd_io.etcd.server.v3.storage.backend.DefaultBackendConfig)) (Val #lg))
  {{ (c : go_etcd_io.etcd.server.v3.storage.backend.BackendConfig), RET #c;
      ⌜c.Logger' = lg ∧ c.Path' = [] ∧ c.Hooks' = interface.nil ∧ c.Mlock' = false ∧
        c.UnsafeNoFsync' = false ∧ c.NonBlockingDefrag' = false⌝ }}

end spec

end Backend
end EtcdGrove
end Perennial
