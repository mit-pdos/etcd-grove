/-
## `BackendConfig.mmapSize()` (`config_linux.go:33`): translated

**Users.** `newBackend` (`bopts.InitialMmapSize`). **Proof sketch.** Returns the field.
**Changes.** Unchanged. **Margin.** None.
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

/-- **`bcfg.mmapSize()`**: `bcfg.MmapSize`. -/
def BackendConfig.mmapSize.spec : Prop :=
  ∀ (cfg : go_etcd_io.etcd.server.v3.storage.backend.BackendConfig),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend }}
    (App (Val (cfg @!! go_etcd_io.etcd.server.v3.storage.backend.BackendConfig.ty @!! go!"mmapSize")) (Val #()))
  {{ RET #cfg.MmapSize'; True }}

end spec

end Backend
end EtcdGrove
end Perennial
