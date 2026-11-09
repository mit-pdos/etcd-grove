/-
`(*leaseCache).notify` (`cache.go`): `key`'s entry and its waiter channel, or `nil`. Proof sketch:
read lock. Changes: from `specs-ref`'s `leaseCache__notify.lean`: over `lcAt`/`lcHeld` (was the cache's exact state transitions over a client part `X`); what the leasing contract's proofs need.
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

/-- `lc.notify(key)`. -/
def leaseCache.notify.spec : Prop :=
  ∀ (lc : Loc) (γ : Cluster) (γL : LeasingNames) (key : GoString),
  {{ lcAt (GF := GF) lc γ γL ∗ threadTok }}
    (App (Val (lc @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.leasing.leaseCache.ty @!! go!"notify")) (Val #key))
  {{ (li : Loc) (wc : GoChan), RET (PairV #li #wc); threadTok ∗ (⌜li = null⌝ ∨ waitRecv wc) }}

end spec

end Leasing
end EtcdGrove
end Perennial
