/-
## `(*lessor).Checkpoint(id, remainingTTL)` (`lessor.go:367`)

**Users.** The applier's `LeaseCheckpoint` (`apply/backend.go:101`, 3a), for each checkpoint of a
committed `LeaseCheckpointRequest` (proposed by the leader's checkpointer), on the apply thread.

**Proof sketch.** `le.mu.Lock()`; a live lease: its `remainingTTL` field written (under `le.mu`:
not modelled); `shouldPersistCheckpoints()` (`le.cluster.Version()`: `clusterOk`; `greaterOrEqual`)
true: `persistTo(le.b)` (the token's `beOk ls.be`, the hook's contract as `Grant.spec`'s; 4b's `MustUnsafePutLease` rewrites the record with the
live TTL, which differs from the stored one only for a recovered lease raised to a larger minimum:
`ls.persist id`, the history appended); primary: `scheduleCheckpointIfNeeded` (the logger:
`isLessor`). Unlock. Always `nil`.

**Changes** (from `specs-ref`'s `lessor__Checkpoint.lean`): over the lessor's state, the backend
write through 4a/4b's provisional names. **Margin.** The remaining TTL (time) is not modelled; which
of the two outcomes (the cluster's version, `CheckpointPersist`).
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.lease.Api

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

/-- **Record a lease's checkpointed remaining TTL** (the writer): `nil`; the model's state unchanged
(the remaining TTL is time), `Pre` back; or, if persisted (a live lease), the lease's record
rewritten (`LessorState.persist`) under the batch lock whose hook ran, `Post`. -/
def lessor.Checkpoint.spec : Prop :=
  ∀ (le : Loc) (γ : Names) (c : Cfg) (n : Nat) (ls : LessorState) (id rem : w64)
    (Pk Pre Q Post : IProp GF) (f : GoFunc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ isLessor le γ c ∗
      lessorState γ n ls ∗ beHook ls.be Pk f ∗ Pre ∗ beHookRun ls.be Pk f Pre Q ∗
      (Q ={⊤}=∗ Pk ∗ Post) }}
    (App (App (Val (le @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.lease.lessor.ty @!!
      go!"Checkpoint")) (Val #id)) (Val #rem))
  {{ (err : GoInterface), RET #err; ⌜err = interface.nil⌝ ∗
      ((lessorState γ n ls ∗ Pre) ∨
       (⌜ls.leases (sint.Z id) ≠ none⌝ ∗ lessorState γ (n + 1) (ls.persist (sint.Z id)) ∗ Post)) }}

end spec
end Lease
end EtcdGrove
end Perennial
