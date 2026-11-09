/-
## `New(bcfg)` (`backend.go:166-168`; `newBackend`, `:199-261`): translated

**Users.** `serverstorage.OpenBackend` (2e, `storage/backend.go:72-97`, in a goroutine, the caller
waiting): `bootstrapBackend` (`bootstrap.go:240`), `OpenSnapshotBackend` (2d's `applySnapshot`),
`RecoverSnapshotBackend`. Snippets `examples/specreq/backend/commit.go` (`ReqReopen`,
`ReqHookWrites`), every snippet's setup (`openBackend`).

**Proof sketch.** `newBackend`: the options (`boltOpenOptions`, the package's initialized global:
`MAP_POPULATE` and `NoFreelistSync` on, `Durable.lean`'s assumed `boltOpenOptions_init`; 4c's `OptsM.ok` with `Mlock` off; `Open`'s freelist-commit update is then `emp`), the logger (`nil`: `zap.NewNop()`;
`newBoltLoggerZap`, a pointer-typed logger: 4c's logger contract), bbolt's `Open` of `cfg.Path`
(4c's `Open.spec` from `fileHolds` (the realization of `beFile p (some I)`; for
`beFile p none`, the names from 4c's `boltFresh_alloc`, state `BoltSt.fresh`), `dbOpenOk` excluding its error,
which `lg.Panic`s: `isBolt`, `boltState (init D)` with `imgOf D = I`). The struct, `readTx` with an
empty buffer, `newBatchTxBuffered` (its first `Commit`: `pending = 0`, no hook yet: begins bbolt's
write transaction and the read transaction, `begin`), `b.hooks := cfg.Hooks`. The ghost state is
allocated at `I`: the history `[I]`, the batch image and the visible image (their authorities in
the batch lock's and `readTx.mu`'s invariants), `beReaderN` slots (`readTx.mu`'s reader count and
the interval wait group's budget, bounded by `beReaderN ≤ 2^30 - 2`), the open token, the hook at
`nil`, the delete right; the client's step turns them into `Pk γ` (which goes into the batch lock's
invariant), the two contracts (into `isBackend`), and `K γ`. `go b.run()` with the caller's
`threadTok` (`Close` gives it back once the loop has exited). The buckets `Bs` (distinct ids:
`bktsOk`) become `beBkt`; the hooks' footprint `beHookFp`; `beDurInv` is 4c's `boltFile` of the
file (`fileHolds_alloc`); `beSynced` records `UnsafeNoFsync` off (the crash law's gate). With a
non-blocking defragmentation configured, the safe-range registry must name only safe-range buckets
(`safeRegOk`, the schema's initialization: a gap recorded in the report).

**Changes** (from `specs-ref`'s `New.lean`, over `bFresh`/`newPostK`/`hooksOk P W Pk`/`BParams`):
the vocabulary (one image by footprints, client-owned visible image and history); any file image
(`beFile p o`: a restart, a received snapshot's file); the panic disjunct replaced by the
environment premise `dbOpenOk` (the memory note: environment failures are premises); round 1: the
thread token for the run loop (no pool), the buckets (T4), the hooks' footprint (T1, T2), the crash
invariant and the `UnsafeNoFsync` mode (T4).

**Changes** (repair3-boot, the crash pass's request 1 to backend-schema): the file is taken through
the update `beOpenUpd` (was `beFile cfg.Path' o` in the precondition), fired at bbolt's open: the
ghost step before `bolt.Open` (`backend.go:233`) runs 4c's `fileHolds_alloc` on the file the update
hands over (in `beFileN`), allocates the history `beHist γ [I]` and its authority (with a share of
`boltState`, in `beFileN`) and commits with `beDurInv γ p` (`boltFile`), `beSynced γ` and the
history, which the client's crash state takes in place of the file. 4c's `Open` supports it: it
takes `boltFile γ ∗ boltClosed γ` and keeps the file in `boltFile`'s crash invariant throughout
(closed, then open; an error closes it again, excluded here by `dbOpenOk`). So a crash at any point
of `New` finds the file in the client's crash state, closed before the open and open after it
(`beFile_crash`, `beCrash`): the window `OpenBackend` recorded is gone. The history left `beNew`;
the client's `R γ` (the update's `COMM`) goes to its allocation step.

**Margin.** The configuration's batch interval and limit, the freelist type and the metrics are
not stated. **Scope** (filed, 4c's D13): `Mlock` off (`--experimental-memory-mlock` excluded: bbolt's
file model has no `mlock`). **Modes**: `UnsafeNoFsync` is recorded (`beSynced` only when off): with it
on, bbolt promises nothing after a crash, so no crash law; `NonBlockingDefrag` takes `safeRegOk`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.Api
public import Spec.go_uber_org.zap.Api
public import Perennial.ProgramLogic.Bounds

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

/-- **`New(cfg)`**: a backend over the file at `cfg.Path` holding `o` (none: a new, empty file),
taken from the client's crash state at the open (`beOpenUpd`), with the hooks `cfg.Hooks` (writing the cells `Fh`) and the buckets `Bs`; the client's allocation step gets
the fresh ghost state at the file's image and chooses the batch lock's resource `Pk γ`. The caller's
thread token runs the commit loop until `Close`. -/
def New.spec : Prop :=
  ∀ (cfg : go_etcd_io.etcd.server.v3.storage.backend.BackendConfig) (o : Option Image) (Bs : BktInfo → Prop) (Fh : Fp)
    (Pk K R : BeNames → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ envOk ∗ threadTok ∗ ⌜dbOpenOk cfg ∧ cfg.Mlock' = false ∧ bktsOk Bs⌝ ∗
      (⌜cfg.NonBlockingDefrag' = false⌝ ∨ safeRegOk) ∗
      (⌜cfg.Logger' = null⌝ ∨ Zap.isLogger cfg.Logger') ∗ beOpenUpd cfg.Path' o cfg.UnsafeNoFsync' R ∗
      (∀ γ : BeNames, R γ -∗ beNew γ (o.getD Image.empty) ={⊤}=∗
        Pk γ ∗ hookOk γ cfg.Hooks' Fh (Pk γ) ∗ commitOk γ (Pk γ) ∗ K γ) }}
    (App (Val (@! go_etcd_io.etcd.server.v3.storage.backend.New)) (Val #cfg))
  {{ (r : GoInterface), RET #r; ∃ (b : Loc) (γ : BeNames), ⌜r = beIface b⌝ ∗
      isBackend γ b cfg.Path' (Pk γ) ∗ K γ ∗ beHookFp γ Fh ∗ (□ ∀ bi, ⌜Bs bi⌝ -∗ beBkt γ bi) ∗
      beDurInv γ cfg.Path' ∗ (if cfg.UnsafeNoFsync' then iprop(True) else beSynced γ) }}

end spec

end Backend
end EtcdGrove
end Perennial
