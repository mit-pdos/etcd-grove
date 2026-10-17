/-
`(*config.ServerConfig).SnapDir()` (`server/config/config.go`: `filepath.Join(c.MemberDir(),
"snap")`; names-only). Lean-first (no Rocq counterpart); etcd PR #22518 (branch
`pr-verify/etcd-22518`).
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

/-- `c.SnapDir()`: the snap directory of the configuration's `DataDir`. -/
abbrev config.ServerConfig.SnapDir.spec : Prop :=
  ∀ (c : Loc) (dq : DFrac) (dd : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.config ∗
      structFieldRef go_etcd_io.etcd.server.v3.config.ServerConfig go!"DataDir" c ↦{dq} dd }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.config.ServerConfig.ty
      @!! go!"SnapDir")) (Val #()))
  {{ RET #(cfgSnapDir dd);
      structFieldRef go_etcd_io.etcd.server.v3.config.ServerConfig go!"DataDir" c ↦{dq} dd }}

end spec

end EtcdGrove
end Perennial
