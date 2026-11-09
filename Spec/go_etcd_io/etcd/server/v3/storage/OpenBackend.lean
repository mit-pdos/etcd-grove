/-
## `OpenBackend(cfg, hooks)` (`backend.go:72-97`): trusted (names only)

**Users.** `bootstrap` (`bootstrapBackend`), `OpenSnapshotBackend` (2d's `applySnapshot`).

**Why it is true.** A goroutine runs `newBackend(cfg, hooks)`, which builds a `BackendConfig` (the
path `BackendPath()`, `UnsafeNoFsync`, the batch limits, the logger, `NonBlockingDefrag` from the
feature gate, the mmap size from the quota: `backendBootRes`'s condition, `Mlock` from
`MemoryMlock`, the hooks) and calls 4a's `New` (`Backend.New.spec`, whose premises it passes on:
its environment premise `dbOpenOk` of that configuration is `diskOk`'s, its `Mlock` off is the
premise here, its registry premise `safeRegOk` is taken whatever the gate answers); the caller waits
for it on a channel (a log line after ten seconds). The caller's thread token goes to the forked
goroutine, which hands it to `New`'s commit loop (back at the backend's `Close`). Also `ETCD_VERIFY`
unset (`envOk`, from `backendBootRes`: the sweep's batch 1).

**Changes** (from `specs-ref`'s `OpenBackend.lean`, `storage.dbOpensOk`, `openMmapOk`): the disk
premise `diskOk`, the configuration's by the backend's provisional slot. Verify-round (A8
provability F5): over 4a's vocabulary: the post is `Backend.New.spec`'s (the client's allocation
step `Pk`/`K`, the buckets `Bs`, the hooks' footprint `Fh`, `isBackend`, the crash invariant and
`beSynced`), the file 4a's `beFile`; the provisional `ServerStorage.beOpen`/`Snap.emptyImage` gone
from this spec. **Margin.** None.

The client's allocation step's `Backend.hookOk γ (hooksIface h) Fh (Pk γ)` for etcd's hooks is
`BackendHooks.OnPreCommitUnsafe.spec` (last pass), at `Fh := hookFp`, from `hooksPkOk`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.Api
public import Spec.go_etcd_io.raft.v3.Api
public import Spec.go_uber_org.zap.Api
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiBoot
public import Perennial.ProgramLogic.Bounds

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

/-- **Opens the backend** at the configuration's path, with the hooks: 4a's `New` (the client's
allocation step at the file's image `o`, an empty one if there is no file). -/
def OpenBackend.spec : Prop :=
  ∀ (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (h : Loc) (ci : GoInterface)
    (o : Option Snap.BeImage) (Bs : Backend.BktInfo → Prop) (Fh : Backend.Fp)
    (Pk K : Backend.BeNames → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage ∗ Zap.isLogger cfg.Logger' ∗ EtcdServer.backendBootRes cfg ∗
      ⌜diskOk ∧ cfg.MemoryMlock' = false ∧ Backend.bktsOk Bs⌝ ∗ Backend.envOk ∗ Backend.safeRegOk ∗
      threadTok ∗ isHooks h ci ∗ Backend.beFile (Config.backendPathOf cfg.DataDir') o ∗
      (∀ γ : Backend.BeNames, Backend.beNew γ (o.getD Backend.Image.empty) ={⊤}=∗
        Pk γ ∗ Backend.hookOk γ (hooksIface h) Fh (Pk γ) ∗ Backend.commitOk γ (Pk γ) ∗ K γ) }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.OpenBackend)) (Val #cfg)) (Val #(hooksIface h)))
  {{ (be : GoInterface), RET #be; ∃ (b : Loc) (γ : Backend.BeNames), ⌜be = Backend.beIface b⌝ ∗
      Backend.isBackend γ b (Config.backendPathOf cfg.DataDir') (Pk γ) ∗ K γ ∗ Backend.beHookFp γ Fh ∗
      (□ ∀ bi, ⌜Bs bi⌝ -∗ Backend.beBkt γ bi) ∗ Backend.beDurInv γ (Config.backendPathOf cfg.DataDir') ∗
      (if cfg.UnsafeNoFsync' then iprop(True) else Backend.beSynced γ) }}

end spec

end ServerStorage
end EtcdGrove
end Perennial
