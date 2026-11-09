/-
`(*leaseCache).LockWriteOps` (`cache.go`): `Lock`/`LockRange` of each write's key or range.
Proof sketch: the callees' specs, the channels appended. Changes: from `specs-ref`'s `leaseCache__LockWriteOps.lean`: over `lcAt`/`lcHeld` (was the cache's exact state transitions over a client part `X`); what the leasing contract's proofs need.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.Internal

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

/-- `lc.LockWriteOps(ops)`: the waiter channels to close. -/
def leaseCache.LockWriteOps.spec : Prop :=
  ∀ (lc : Loc) (γ : Cluster) (γL : LeasingNames) (ops : GoSlice) (os : List OpM),
  {{ lcAt (GF := GF) lc γ γL ∗ opsAt ops os }}
    (App (Val (lc @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.leasing.leaseCache.ty @!! go!"LockWriteOps")) (Val #ops))
  {{ (sl : GoSlice), RET #sl; opsAt ops os ∗ ∃ cs : List GoChan, sl ↦* cs ∗ [∗list] c ∈ cs, waitCloser c }}

end spec

end Leasing
end EtcdGrove
end Perennial
