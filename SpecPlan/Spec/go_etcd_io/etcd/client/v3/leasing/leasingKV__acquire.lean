/-
`(*leasingKV).acquire` (`kv.go`): the acquisition transaction (`If(CreateRevision(pfx++key) = 0,
LeaseValue(key) = 0).Then(op, put pfx++key with the session's lease).Else(op, get pfx++key)`),
retried on `Unavailable`. Proof sketch: `waitSession` (`sessionReady`), `leaseID`; the transaction
is a `ProtoStep` (its only write is the lease key), fired from `protoUpd` with `etcdState_lb`'s
snapshot; `errors.As`, `status.FromError` (grpc's boundary, 2a). Called with `op = OpGet(key)` only.
Changes: from `specs-ref`'s `leasingKV__acquire.lean`: restated over `isLeasingKV`/`Internal.lean` (was the cache's log states and the history premise); weakened to what the leasing contract's proofs need.
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

/-- `acquire(ctx, key, OpGet(key))`: an error, or the owned reply: its first response the plain
get's at the reply's revision: `key`'s record there (`recAtHdr`: the only write is the lease key
`pfx ++ key ≠ key`, `pfx ≠ []`), shaped as a cached response (`cachedRespOk`). -/
def leasingKV.acquire.spec : Prop :=
  ∀ (lkv : Loc) (γ : Cluster) (who p : Principal) (pfx : Key) (γL : LeasingNames) (ctx : GoInterface) (key : GoString) (op : go_etcd_io.etcd.client.v3.Op),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ isLeasingKV lkv γ who pfx γL ∗ Context.ctxOk ctx ∗ ctxPrin who ctx p ∗ opAt op (opGetM key []) ∗ threadTok }}
    (App (App (App (Val (lkv @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.leasing.leasingKV.ty @!! go!"acquire")) (Val #ctx)) (Val #key)) (Val #op))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); threadTok ∗
      (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∨
       (⌜err = GoInterface.nil⌝ ∗ sessionReady γL ∗ ∃ (σ0 : State) (m : TxnRespM) (rm : RangeRespM)
          (r2 : ResponseOpM), etcdLb γ σ0 ∗ txnRespOwn resp (DFrac.own 1) m ∗
          ⌜m.responses = [.range rm, r2] ∧ cachedRespOk key σ0 { rm with hdr := some m.hdr } ∧
            recAtHdr key σ0 { rm with hdr := some m.hdr }⌝)) }}

end spec

end Leasing
end EtcdGrove
end Perennial
