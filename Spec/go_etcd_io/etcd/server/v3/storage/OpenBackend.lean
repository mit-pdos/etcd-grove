/-
`storage.OpenBackend(cfg, hooks)` (`server/storage/backend.go`; names only): the backend over the
database file at `cfg.BackendPath()`, opened by `newBackend(cfg, hooks)` (`backend.New` of the
configuration's backend settings) on a goroutine, the caller waiting for it (a log line if it
takes over 10 s). The trust boundary (D22 S-f, 2026-10-19; an axiom in
`Proof/go_etcd_io/etcd/server/v3/storage/OpenBackend.lean`: the goroutine can panic, see
`InvOpen.lean`'s `dbOpensOk`). Lean-first (no Rocq counterpart).

The pre: the file holding `D` (`fileHolds`) and `openPre` (`InvOpen.lean`). The post: what
`backend.New` gives (`newPost`), as a `Backend`, and, if `D` records no compaction
(`mvcc.noCmpData`), the backend's token of it (`mvcc.bkNoCmp`, what the store's `restore` consumes:
D22 S-g). Stated at `HasLC.hasLC` (`newPost` is).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.InvOpen
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Image

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI backend storage

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.Assumptions]

/-- `OpenBackend(cfg, hooks)` of the file holding `D`: the backend `backend.New` makes, with its
no-compaction token if `D` has neither compaction key. -/
abbrev storage.OpenBackend.spec : Prop :=
  ∀ (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (h : GoInterface) (P : BParams)
    (D : Data) (W Pk : BNames → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage ∗
      fileHolds (config.backendPathOf cfg.DataDir') D ∗ openPre cfg h P D W Pk }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.OpenBackend)) (Val #cfg)) (Val #h))
  {{ (b : Loc) (γ : BNames),
      RET #(interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #b);
      newPost γ P W Pk b D ∗ (⌜mvcc.noCmpData D⌝ -∗ mvcc.bkNoCmp γ) }}

end spec

end EtcdGrove
end Perennial
