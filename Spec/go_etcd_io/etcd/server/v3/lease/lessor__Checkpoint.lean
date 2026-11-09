/-
## `(*lessor).Checkpoint(id, remainingTTL)` (`lessor.go:367`)

**Users.** The applier's `LeaseCheckpoint` (`apply/backend.go:101`, 3a), for each checkpoint of a
committed `LeaseCheckpointRequest` (proposed by the leader's checkpointer), on the apply thread.

**Proof sketch.** `le.mu.Lock()`; a live lease: its `remainingTTL` field written (under `le.mu`:
not modelled); `shouldPersistCheckpoints()` (`le.cluster.Version()`: `clusterOk`; `greaterOrEqual`)
true: `persistTo(le.b)` (`beApplyTok ls.be`; 4b's `MustUnsafePutLease` rewrites the record with the
same id and TTL: `beLeases ls.be ls.bkt` unchanged in the model, which abstracts `RemainingTTL`);
primary: `scheduleCheckpointIfNeeded` (the logger: `isLessor`). Unlock. Always `nil`.

**Changes** (from `specs-ref`'s `lessor__Checkpoint.lean`): over the lessor's state (unchanged in
it), the backend write through 4a/4b's provisional names. **Margin.** The remaining TTL (time) is
not modelled: the step changes nothing a reader can see in the model.
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

/-- **Record a lease's checkpointed remaining TTL** (the writer): `nil`; the model's state unchanged
(the remaining TTL is time). -/
def lessor.Checkpoint.spec : Prop :=
  ∀ (le : Loc) (γ : Names) (c : Cfg) (n : Nat) (ls : LessorState) (id rem : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ isLessor le γ c ∗
      lessorState γ n ls ∗ beApplyTok ls.be }}
    (App (App (Val (le @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.lease.lessor.ty @!!
      go!"Checkpoint")) (Val #id)) (Val #rem))
  {{ (err : GoInterface), RET #err; ⌜err = interface.nil⌝ ∗ lessorState γ n ls ∗ beApplyTok ls.be }}

end spec
end Lease
end EtcdGrove
end Perennial
