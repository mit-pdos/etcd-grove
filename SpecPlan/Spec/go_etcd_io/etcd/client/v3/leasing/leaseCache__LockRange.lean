/-
`(*leaseCache).LockRange` (`cache.go`): `Lock` of every cached key in `[begin, end)`. Proof sketch:
write lock; the map iteration (Perennial's `range` over a map). Changes: from `specs-ref`'s `leaseCache__LockRange.lean`: over `lcAt`/`lcHeld` (was the cache's exact state transitions over a client part `X`); what the leasing contract's proofs need.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.client.v3.leasing.Internal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Leasing

open Iris Iris.BI EtcdModel EtcdWire ClientV3
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

/-- `lc.LockRange(begin, end)`: the waiter channels to close. -/
def leaseCache.LockRange.spec : Prop :=
  ∀ (lc : Loc) (γ : Cluster) (γL : LeasingNames) (b «end» : GoString),
  {{ lcAt (GF := GF) lc γ γL }}
    (App (App (Val (lc @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.leasing.leaseCache.ty @!! go!"LockRange")) (Val #b)) (Val #«end»))
  {{ (sl : GoSlice), RET #sl; ∃ cs : List GoChan, sl ↦* cs ∗ [∗list] c ∈ cs, waitCloser c }}

end spec

end Leasing
end EtcdGrove
end Perennial
