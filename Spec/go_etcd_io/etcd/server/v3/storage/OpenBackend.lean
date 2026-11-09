/-
## `OpenBackend(cfg, hooks)` (`backend.go:72-97`): trusted (names only)

**Users.** `bootstrap` (`bootstrapBackend`), `OpenSnapshotBackend` (2d's `applySnapshot`).

**Why it is true.** A goroutine runs `newBackend(cfg, hooks)` (`backend.New`: bbolt's `Open` of
`BackendPath()`, a panic if it fails: `diskOk`; the mmap size from the quota: `backendBootRes`'s
condition) and the caller waits for it (a log line after ten seconds). The file's image is the
backend's (4a); an absent file is created empty (`emptyImage`). `hooks` is called at every commit
(`isHooks`). Also `ETCD_VERIFY` unset (`backendBootRes`: the sweep's batch 1).

**Changes** (from `specs-ref`'s `OpenBackend.lean`, `storage.dbOpensOk`, `openMmapOk`): the disk
premise `diskOk`, the configuration's by the backend's provisional slot. **Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.Api
public import Spec.go_etcd_io.raft.v3.Api
public import Spec.go_uber_org.zap.Api
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiBoot

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

/-- **Opens the backend** at the configuration's path, with the hooks. -/
def OpenBackend.spec : Prop :=
  ∀ (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (h : Loc) (ci : GoInterface)
    (o : Option Snap.BeImage),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage ∗ Zap.isLogger cfg.Logger' ∗ EtcdServer.backendBootRes cfg ∗ ⌜diskOk⌝ ∗ isHooks h ci ∗
      Snap.beFile (Config.backendPathOf cfg.DataDir') o }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.OpenBackend)) (Val #cfg)) (Val #(interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.BackendHooks.ty) #h)))
  {{ (be : GoInterface), RET #be; ∃ img, beOpen be (Config.backendPathOf cfg.DataDir') img ∗
      ⌜match o with | some i => img = i | none => Snap.emptyImage img⌝ }}

end spec

end ServerStorage
end EtcdGrove
end Perennial
