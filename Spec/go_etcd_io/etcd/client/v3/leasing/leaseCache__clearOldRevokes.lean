/-
`(*leaseCache).clearOldRevokes` (`cache.go`): the goroutine `NewKV` starts; every second drops old
revocation times, until `ctx` is done. Proof sketch: `time.After`, write lock, map iteration and
delete. Changes: from `specs-ref`'s `leaseCache__clearOldRevokes.lean`: over `lcAt`/`lcHeld` (was the cache's exact state transitions over a client part `X`); what the leasing contract's proofs need.
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

/-- `lc.clearOldRevokes(ctx)`: runs until `ctx` is done. -/
def leaseCache.clearOldRevokes.spec : Prop :=
  ∀ (lc : Loc) (γ : Cluster) (γL : LeasingNames) (ctx : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ lcAt lc γ γL ∗ Context.ctxOk ctx }}
    (App (Val (lc @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.leasing.leaseCache.ty @!! go!"clearOldRevokes")) (Val #ctx))
  {{ RET #(); True }}

end spec

end Leasing
end EtcdGrove
end Perennial
