/-
`(*leasingKV).revokeLeaseKvs` (`kv.go`): `revoke(ctx, key, OpGet(key))` of each lease key not of its
own session. Proof sketch: `leaseID` (`sessionReady`, from `isLeasingKV`'s callers having waited),
`strings.TrimPrefix`, `revoke` with an update from `protoUpd`. Changes: from `specs-ref`'s `leasingKV__revokeLeaseKvs.lean`: restated over `isLeasingKV`/`Internal.lean` (was the cache's log states and the history premise); weakened to what the leasing contract's proofs need.
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

/-- `revokeLeaseKvs(ctx, kvs)`: the key-values read-only, given back. -/
def leasingKV.revokeLeaseKvs.spec : Prop :=
  ∀ (lkv : Loc) (γ : Cluster) (who p : Principal) (pfx : Key) (γL : LeasingNames) (ctx : GoInterface) (kvs : GoSlice) (dq : DFrac) (ms : List KeyValueM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ isLeasingKV lkv γ who pfx γL ∗ sessionReady γL ∗ Context.ctxOk ctx ∗ ctxPrin who ctx p ∗ msgsOwn keyValueOwn kvs dq ms ∗ threadTok }}
    (App (App (Val (lkv @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.leasing.leasingKV.ty @!! go!"revokeLeaseKvs")) (Val #ctx)) (Val #kvs))
  {{ (rev : w64) (err : GoInterface), RET (PairV #rev #err); msgsOwn keyValueOwn kvs dq ms ∗ threadTok }}

end spec

end Leasing
end EtcdGrove
end Perennial
