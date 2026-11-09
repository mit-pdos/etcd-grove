/-
## `New(bcfg)` (`backend.go:166-168`; `newBackend`, `:199-261`): translated

**Users.** `serverstorage.OpenBackend` (2e, `storage/backend.go:72-97`, in a goroutine, the caller
waiting): `bootstrapBackend` (`bootstrap.go:240`), `OpenSnapshotBackend` (2d's `applySnapshot`),
`RecoverSnapshotBackend`. Snippets `examples/specreq/backend/commit.go` (`ReqReopen`,
`ReqHookWrites`), every snippet's setup (`openBackend`).

**Proof sketch.** `newBackend`: the options (`boltOpenOptions`, the package's initialized global:
`MAP_POPULATE`, 4c's `OptsM.ok` with `Mlock` off), the logger (`nil`: `zap.NewNop()`;
`newBoltLoggerZap`, a pointer-typed logger: 4c's logger contract), bbolt's `Open` of `cfg.Path`
(4c's `Open.spec` from `fileHolds` (the realization of `beFile p o`), `dbOpenOk` excluding its error,
which `lg.Panic`s: `isBolt`, `boltState (init D)` with `imgOf D = I`). The struct, `readTx` with an
empty buffer, `newBatchTxBuffered` (its first `Commit`: `pending = 0`, no hook yet: begins bbolt's
write transaction and the read transaction, `begin`), `b.hooks := cfg.Hooks`. The ghost state is
allocated at `I`: the history `[I]`, the batch image and the visible image (their authorities in
the batch lock's and `readTx.mu`'s invariants), `beReaderN` slots (`readTx.mu`'s reader count and
the interval wait group's budget, bounded by `beReaderN ≤ 2^30 - 2`), the open token, the hook at
`nil`, the delete right; the client's step turns them into `Pk γ` (which goes into the batch lock's
invariant), the two contracts (into `isBackend`), and `K γ`. `go b.run()` borrows a thread from
`envOk`'s pool.

**Changes** (from `specs-ref`'s `New.lean`, over `bFresh`/`newPostK`/`hooksOk P W Pk`/`BParams`):
the vocabulary (one image by footprints, client-owned visible image and history); any file image
(`beFile p o`: a restart, a received snapshot's file); the panic disjunct replaced by the
environment premise `dbOpenOk` (the memory note: environment failures are premises); no thread
token (the pool's).

**Margin.** The configuration's batch interval and limit, `NoSync`, the freelist type and the
metrics are not stated; with `UnsafeNoFsync` set, `beHist`'s crash meaning is void (4c's
`BoltSt.commit` promises nothing under `NoSync`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.Api
public import Spec.go_uber_org.zap.Api

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

/-- **`New(cfg)`**: a backend over the file at `cfg.Path` holding `o` (none: a new, empty file), with
the hooks `cfg.Hooks`; the client's allocation step gets the fresh ghost state at the file's image
and chooses the batch lock's resource `Pk γ`. -/
def New.spec : Prop :=
  ∀ (cfg : go_etcd_io.etcd.server.v3.storage.backend.BackendConfig) (o : Option Image) (Pk K : BeNames → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ envOk ∗ ⌜dbOpenOk cfg ∧ cfg.Mlock' = false⌝ ∗
      (⌜cfg.Logger' = null⌝ ∨ Zap.isLogger cfg.Logger') ∗ beFile cfg.Path' o ∗
      (∀ γ : BeNames, beNew γ (o.getD Image.empty) ={⊤}=∗
        Pk γ ∗ hookOk γ cfg.Hooks' (Pk γ) ∗ commitOk γ (Pk γ) ∗ K γ) }}
    (App (Val (@! go_etcd_io.etcd.server.v3.storage.backend.New)) (Val #cfg))
  {{ (r : GoInterface), RET #r; ∃ (b : Loc) (γ : BeNames), ⌜r = beIface b⌝ ∗
      isBackend γ b cfg.Path' (Pk γ) ∗ K γ }}

end spec

end Backend
end EtcdGrove
end Perennial
