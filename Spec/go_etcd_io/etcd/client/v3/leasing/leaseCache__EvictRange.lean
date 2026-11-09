/-
`(*leaseCache).EvictRange` (`cache.go`): meant to drop every entry in `[key, end)`; drops `key`'s
for each (`issues/leasing-evictrange-key.md`). Proof sketch: write lock; map iteration; `inRange`.
Changes: from `specs-ref`'s `leaseCache__EvictRange.lean`: over `lcAt`/`lcHeld` (was the cache's exact state transitions over a client part `X`); what the leasing contract's proofs need.
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

/-- `lc.EvictRange(key, end)`. -/
def leaseCache.EvictRange.spec : Prop :=
  ∀ (lc : Loc) (γ : Cluster) (γL : LeasingNames) (key «end» : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ lcAt lc γ γL }}
    (App (App (Val (lc @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.leasing.leaseCache.ty @!! go!"EvictRange")) (Val #key)) (Val #«end»))
  {{ RET #(); True }}

end spec

end Leasing
end EtcdGrove
end Perennial
