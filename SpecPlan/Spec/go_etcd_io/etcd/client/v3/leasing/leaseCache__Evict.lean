/-
`(*leaseCache).Evict` (`cache.go`): drops `key`'s entry, records its revocation time; its revision
or `0`. Proof sketch: write lock; `time.Now`. Changes: from `specs-ref`'s `leaseCache__Evict.lean`: over `lcAt`/`lcHeld` (was the cache's exact state transitions over a client part `X`); what the leasing contract's proofs need.
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

/-- `lc.Evict(key)`. -/
def leaseCache.Evict.spec : Prop :=
  ∀ (lc : Loc) (γ : Cluster) (γL : LeasingNames) (key : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ lcAt lc γ γL }}
    (App (Val (lc @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.leasing.leaseCache.ty @!! go!"Evict")) (Val #key))
  {{ (rev : w64), RET #rev; True }}

end spec

end Leasing
end EtcdGrove
end Perennial
