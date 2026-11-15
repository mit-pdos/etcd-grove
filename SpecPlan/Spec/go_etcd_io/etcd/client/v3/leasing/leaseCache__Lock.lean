/-
`(*leaseCache).Lock` (`cache.go`): gives `key`'s entry a fresh waiter channel (readers of the entry
wait for it), returned with the entry's revision; `nil` if not cached. Proof sketch: write lock; the
new channel's receive side kept in the entry (`waitRecv`), the close right returned. Changes: from `specs-ref`'s `leaseCache__Lock.lean`: over `lcAt`/`lcHeld` (was the cache's exact state transitions over a client part `X`); what the leasing contract's proofs need.
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

/-- `lc.Lock(key)`: the waiter channel to close, or `nil`. -/
def leaseCache.Lock.spec : Prop :=
  ∀ (lc : Loc) (γ : Cluster) (γL : LeasingNames) (key : GoString),
  {{ lcAt (GF := GF) lc γ γL }}
    (App (Val (lc @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.leasing.leaseCache.ty @!! go!"Lock")) (Val #key))
  {{ (wc : GoChan) (rev : w64), RET (PairV #wc #rev); ⌜wc = null⌝ ∨ waitCloser wc }}

end spec

end Leasing
end EtcdGrove
end Perennial
