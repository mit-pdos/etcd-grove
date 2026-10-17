/-
`storage.OpenBackend(cfg, hooks)` (`server/storage/backend.go`: opens the backend at
`cfg.BackendPath()`, in a goroutine, logging when it takes long; names-only). Lean-first (no Rocq
counterpart); etcd PR #22518 (branch `pr-verify/etcd-22518`).
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
variable [package_sem : go_etcd_io.etcd.server.v3.storage.Assumptions]
/-- `OpenBackend(cfg, hooks)` returns some backend (it does not fail: bbolt's open errors are
fatal in `backend.New`). Nothing more is needed of it here: the spec of `OpenSnapshotBackend`
is about what happens before it. -/
abbrev storage.OpenBackend.spec : Prop :=
  ∀ (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (hooks : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.OpenBackend)) (Val #cfg)) (Val #hooks))
  {{ (be : GoInterface), RET #be; True }}

end spec

end EtcdGrove
end Perennial
