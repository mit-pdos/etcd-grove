/-
`(*leaseCache).NotifyOps` (`cache.go`): the waiter channels of the cached keys of `ops`' gets.
Proof sketch: `notify` of each (a reader slot each time). Changes: from `specs-ref`'s `leaseCache__NotifyOps.lean`: over `lcAt`/`lcHeld` (was the cache's exact state transitions over a client part `X`); what the leasing contract's proofs need.
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

/-- `lc.NotifyOps(ops)`: channels one may receive from. -/
def leaseCache.NotifyOps.spec : Prop :=
  ∀ (lc : Loc) (γ : Cluster) (γL : LeasingNames) (ops : GoSlice) (os : List OpM),
  {{ lcAt (GF := GF) lc γ γL ∗ opsAt ops os ∗ threadTok }}
    (App (Val (lc @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.leasing.leaseCache.ty @!! go!"NotifyOps")) (Val #ops))
  {{ (sl : GoSlice), RET #sl; opsAt ops os ∗ threadTok ∗
      ∃ cs : List GoChan, sl ↦* cs ∗ [∗list] c ∈ cs, waitRecv c }}

end spec

end Leasing
end EtcdGrove
end Perennial
