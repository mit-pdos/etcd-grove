/-
`storage.OpenBackend(cfg, hooks)` (`server/storage/backend.go`; names only): the backend over the
database file at `cfg.BackendPath()`, opened by `newBackend(cfg, hooks)` (`backend.New` of the
configuration's backend settings) on a goroutine, the caller waiting for it (a log line if it
takes over 10 s). The trust boundary (D22 S-f, 2026-10-19; an axiom in
`Proof/go_etcd_io/etcd/server/v3/storage/OpenBackend.lean`: the goroutine can panic, see
`InvOpen.lean`'s `dbOpensOk`). Lean-first (no Rocq counterpart).

The pre: the file holding `D` (`fileHolds`) and `openPre` (`InvOpen.lean`). The post: what
`backend.New` gives (`newPostK`: D22 receiver epochs, S8a, 2026-10-24, the creator's batch-lock
step trades the fresh backend's payment rights `bFresh` for `K`, as `New`'s spec now says; until
then `newPost`, which is `K := bFresh`), as a `Backend`; `newPostK` holds the client's half of the
compaction keys' flag (`backend.fkOwn`, at `0` if `D` records no compaction: then it is the
backend's no-compaction token `mvcc.bkNoCmp`, what the store's `restore` consumes,
`mvcc.bkNoCmp_of_fkOwn`; the backend-compaction stage, 2026-10-29: until then a separate wand
`⌜noCmpData D⌝ -∗ bkNoCmp γ`, an opaque token, D22 S-g). Stated at `HasLC.hasLC` (`newPost` is).
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.Assumptions]

/-- `OpenBackend(cfg, hooks)` of the file holding `D`: the backend `backend.New` makes. -/
abbrev storage.OpenBackend.spec : Prop :=
  ∀ (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (h : GoInterface) (P : BParams)
    (D : Data) (W Pk K : BNames → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage ∗
      fileHolds (config.backendPathOf cfg.DataDir') D ∗ openPre cfg h P D W Pk K }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.OpenBackend)) (Val #cfg)) (Val #h))
  {{ (b : Loc) (γ : BNames),
      RET #(interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #b);
      newPostK γ P W Pk K b D }}

end spec

end EtcdGrove
end Perennial
