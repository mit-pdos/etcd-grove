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
from this spec. Changes: verify-round (second crash pass, G-a): statement unchanged; `Backend.beOpenUpd` now also takes the revert state (adding `none` when it opens a `none` file: bbolt creates it with no directory sync), so a client's crash state builds it from `beFile p o ∗ beRevs p os`.

**Margin.** None.

Verify round, crash pass (R-A8 N4): a crash **inside** the call finds the backend file in neither
the caller's disk state nor the file's crash invariant: `New` (4a) takes `beFile` in its
precondition and allocates `beDurInv` inside the call. Not fixed here (the statement passes `New`'s
premises on): requested of backend-schema (`New` taking the file through an update at bbolt's open,
with `beDurInv` given to the allocation step), recorded in `verify/repair2-crash.md`; until then
`ReqCrashRecover`'s "at any point" excludes this window.

Changes: verify-round (repair3-boot): **the window is closed.** The file is taken through 4a's
`Backend.beOpenUpd` (passed on to `New`, which fires it at bbolt's open; was `Backend.beFile` in the
precondition); the client's `R γ` goes to its allocation step. A crash inside the call finds the
file closed in the caller's disk state (before the open) or open there (`beDurInv ∗ beSynced ∗
beHist`, after it).

The client's allocation step's `Backend.hookOk γ (hooksIface h) Fh (Pk γ)` for etcd's hooks is
`BackendHooks.OnPreCommitUnsafe.spec` (last pass), at `Fh := hookFp`, from `hooksPkOk`.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.Api
public import SpecPlan.Spec.go_etcd_io.raft.v3.Api
public import SpecPlan.Spec.go_uber_org.zap.Api
public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiBoot
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
    (Pk K R : Backend.BeNames → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage ∗ Zap.isLogger cfg.Logger' ∗ EtcdServer.backendBootRes cfg ∗
      ⌜diskOk ∧ cfg.MemoryMlock' = false ∧ Backend.bktsOk Bs⌝ ∗ Backend.envOk ∗ Backend.safeRegOk ∗
      threadTok ∗ isHooks h ci ∗ Backend.beOpenUpd (Config.backendPathOf cfg.DataDir') o cfg.UnsafeNoFsync' R ∗
      (∀ γ : Backend.BeNames, R γ -∗ Backend.beNew γ (o.getD Backend.Image.empty) ={⊤}=∗
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
