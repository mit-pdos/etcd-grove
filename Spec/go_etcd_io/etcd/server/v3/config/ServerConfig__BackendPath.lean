/-
`(*config.ServerConfig).BackendPath()` (`server/config/config.go`:
`datadir.ToBackendFileName(c.DataDir)`, `<DataDir>/member/snap/db`; names-only). Lean-first (no
Rocq counterpart); etcd PR #22518 (branch `pr-verify/etcd-22518`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.InvSnapshotBackend

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI 

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `c.BackendPath()`: the backend file of the configuration's `DataDir`, which is in its snap
directory (`filepath.Join(SnapDir, "db")`). -/
abbrev config.ServerConfig.BackendPath.spec : Prop :=
  ∀ (c : Loc) (dq : DFrac) (dd : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.config ∗
      structFieldRef go_etcd_io.etcd.server.v3.config.ServerConfig go!"DataDir" c ↦{dq} dd }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.config.ServerConfig.ty
      @!! go!"BackendPath")) (Val #()))
  {{ RET #(cfgBackendPath dd);
      structFieldRef go_etcd_io.etcd.server.v3.config.ServerConfig go!"DataDir" c ↦{dq} dd ∗
      ⌜fs.dirOf (cfgBackendPath dd) = cfgSnapDir dd⌝ }}

end spec

end EtcdGrove
end Perennial
