/-
`(*leaseCache).Get` (`cache.go`): `(nil, false)` for a bad op; else waits for the key's entry's
waiter and copies it for `op` (`(nil, true)` if not cached or the context ends). Proof sketch:
`isBadOp`, `notify`, the `select` (`waitRecv`, the context's `Done`), read lock, the entry (or the
frozen copy of an evicted one) `cachedRespAt` with its `cachedRespOk`/`etcdLb`; `leaseKey.get` (the
copy keeps `cachedRespOk`). Changes: from `specs-ref`'s `leaseCache__Get.lean`: over `lcAt`/`lcHeld` (was the cache's exact state transitions over a client part `X`); what the leasing contract's proofs need.
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

/-- `lc.Get(ctx, op)`: `ok` is "not a bad op"; a response, if any, fresh and shaped as a cached
response of the get's key at a revision reached. -/
def leaseCache.Get.spec : Prop :=
  ∀ (lc : Loc) (γ : Cluster) (γL : LeasingNames) (ctx : GoInterface) (op : go_etcd_io.etcd.client.v3.Op) (o : OpM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ lcAt lc γ γL ∗ Context.ctxOk ctx ∗ opAt op o ∗ threadTok }}
    (App (App (Val (lc @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.leasing.leaseCache.ty @!! go!"Get")) (Val #ctx)) (Val #op))
  {{ (resp : Loc) (ok : Bool), RET (PairV #resp #ok); threadTok ∗ ⌜ok = !isBadOpM o⌝ ∗
      (⌜resp = null⌝ ∨ (⌜ok = true⌝ ∗ ∃ (σ0 : State) (m : RangeRespM), etcdLb γ σ0 ∗
         rangeRespOwn resp (DFrac.own 1) m ∗ ⌜cachedRespOk o.key σ0 m⌝)) }}

end spec

end Leasing
end EtcdGrove
end Perennial
