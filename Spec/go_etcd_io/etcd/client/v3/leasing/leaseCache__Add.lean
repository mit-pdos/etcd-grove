/-
`(*leaseCache).Add` (`cache.go`): caches `resp` under `key` (waiter `closedCh`), raises the cache's
latest header, returns `leaseKey.get(op)` of it. Proof sketch: write lock (the entries map made:
`sessionReady`); the response and its facts into the invariant (`cachedRespOk`, `etcdLb`);
`closedCh` (`init.spec`); `leaseKey.get`. Changes: from `specs-ref`'s `leaseCache__Add.lean`: over `lcAt`/`lcHeld` (was the cache's exact state transitions over a client part `X`); what the leasing contract's proofs need.
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

/-- `lc.Add(key, resp, op)`: the response kept by the cache; a fresh copy for the get `op`
(`leaseGetM`). -/
def leaseCache.Add.spec : Prop :=
  ∀ (lc : Loc) (γ : Cluster) (γL : LeasingNames) (key : GoString) (resp : Loc) (m : RangeRespM) (σ0 : State)
    (op : go_etcd_io.etcd.client.v3.Op) (o : OpM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ lcAt lc γ γL ∗ sessionReady γL ∗ rangeRespOwn resp (DFrac.own 1) m ∗ etcdLb γ σ0 ∗
      ⌜cachedRespOk key σ0 m⌝ ∗ opAt op o }}
    (App (App (App (Val (lc @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.leasing.leaseCache.ty @!! go!"Add")) (Val #key)) (Val #resp)) (Val #op))
  {{ (ret : Loc), RET #ret; ∃ m' : RangeRespM, rangeRespOwn ret (DFrac.own 1) m' ∗ ⌜m' = leaseGetM o m⌝ }}

end spec

end Leasing
end EtcdGrove
end Perennial
