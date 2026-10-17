/-
`BackendConfig.mmapSize` (`config_linux.go`). `bcfg.mmapSize()`: the configuration's `MmapSize`,
as an `int`. Lean-first (no Rocq counterpart); 2026-10-17, branch `construct` (the backend's
constructor).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.backend

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- `bcfg.mmapSize()`: `int(bcfg.MmapSize)` (the same bits). -/
abbrev backend.BackendConfig.mmapSize.spec : Prop :=
  ∀ (c : Loc) (cfg : BackendConfig),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      c ↦ cfg }}
    (App (Val (c @!! go.GoType.PointerType BackendConfig.ty @!! go!"mmapSize")) (Val #()))
  {{ RET #cfg.MmapSize'; c ↦ cfg }}

end spec

end EtcdGrove
end Perennial
