/-
## `NewLessor(lg, b, cluster, cfg)` (`lessor.go:208`): names only (an assumed spec)

**Users.** `NewServer` (`server.go:344`, 2e): the server's logger, its backend (fresh, or a
restart's: the lease bucket of the last commit), its membership (`*RaftCluster`, for `Version()`),
`LessorConfig{MinLeaseTTL: ⌈3·ElectionTimeout⌉ s, CheckpointInterval, ExpiredLeasesRetryInterval,
CheckpointPersist}` from the server's configuration. Snippet `lessor.go` (every `Req*` starts from
it).

**Why it is true** (the code). `newLessor`: the intervals defaulted when `0`, `leaseRevokeRate`
(unexported, so `0` from any client) defaulted to 1000; the struct with fresh maps, notifier and
heap, `expiredC` (buffered, 16), `stopC`, `doneC`; `initAndRecover()` (as `Recover`'s: the bucket's
leases loaded with fresh objects, TTLs raised to `MinLeaseTTL`, `ForceCommit`); `go runLoop()` (every
500 ms: `revokeExpiredLeases` (when primary, the leases past their expiry: sent on `expiredC`
unless full or stopped) and `checkpointScheduledLeases` (when primary with a checkpointer, `cp(...)`
with the due checkpoints); returns on `stopC`, closing `doneC`). The ghost state: `γ`'s current
state and history (`lessorState γ 0 _`), each object's lock invariant, `lessorStop`'s close right.
**The expiry mode `exp`** is the caller's choice: `true` always; `false` only under the trusted
`leasesOutliveRun` (the run loop's time reasoning: no lease found expired, nothing sent).
Untranslated (the run loop's time, the float conversions of `scheduleCheckpointIfNeeded`), so
assumed. **The logger must be a real one** (`Zap.isLogger`): zap's zero `Logger` panics in
`scheduleCheckpointIfNeeded`'s `Debug` (`specs-ref`'s axiom sweep B3-2, `lessor-methods.md`).

**Changes** (from `specs-ref`'s `NewLessor.lean`, 166 lines: the grant guard `GA`, the monotone
mode, the tracked buckets `S`, `ckptEffectsOk`, `lg ≠ null`): the logger is `isLogger` (the sweep's
repair); the backend through 4a/4b's `beOk`, `beLeases` (any bucket: a restart's leases are loaded,
not only an empty bucket); the checkpointer's contract moved to `SetCheckpointer`; the grant guard
and the monotone mode gone (the lessor accepts any id; the expiry mode replaces the old
`leasesNoExpiry` gating).

**Margin.** `MinLeaseTTL`, the intervals and `CheckpointPersist` are any values (no premise: the
code accepts them); only the minimum is visible to the specs (`c.minTTL`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Lease

open Iris Iris.BI EtcdModel

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

/-- **A new lessor over backend `b`**: its state the leases of `b`'s lease bucket (fresh objects,
TTLs raised to `MinLeaseTTL`, no key attached, no deleter), the writer's token, the stop right; its
expiry mode `exp` (`false` only under the trusted `leasesOutliveRun`). -/
def NewLessor.spec : Prop :=
  ∀ (lg : Loc) (b cl : GoInterface) (cfg : go_etcd_io.etcd.server.v3.lease.LessorConfig)
    (B : Int → Option Int) (exp : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ Zap.isLogger lg ∗
      beOk b ∗ beLeases b B ∗ clusterOk cl ∗ ⌜exp = false → leasesOutliveRun⌝ }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.lease.NewLessor)) (Val #lg)) (Val #b))
      (Val #cl)) (Val #cfg))
  {{ (li : GoInterface), RET #li; ∃ (le : Loc) (γ : Names) (objs : Int → Loc),
      ⌜li = lessorIface le⌝ ∗
      isLessor le γ { minTTL := sint.Z cfg.MinLeaseTTL', expiry := exp } ∗
      lessorState γ 0 (LessorState.loaded { minTTL := sint.Z cfg.MinLeaseTTL', expiry := exp } b
        func.nil B objs (fun _ _ => False)) ∗
      lessorStop le }}

end spec
end Lease
end EtcdGrove
end Perennial
