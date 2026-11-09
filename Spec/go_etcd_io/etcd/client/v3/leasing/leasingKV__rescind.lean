/-
`(*leasingKV).rescind` (`kv.go`): evicts `key` and deletes its lease key (a guarded transaction,
retried until it succeeds or `ctx` is done). Proof sketch: `leaseCache.Evict`; each attempt's
transaction writes only the lease key (`ProtoStep`), fired from `protoUpd`. Changes: from `specs-ref`'s `leasingKV__rescind.lean`: restated over `isLeasingKV`/`Internal.lean` (was the cache's log states and the history premise); weakened to what the leasing contract's proofs need.
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

/-- `rescind(ctx, key, rev)`. -/
def leasingKV.rescind.spec : Prop :=
  ∀ (lkv : Loc) (γ : Cluster) (who p : Principal) (pfx : Key) (γL : LeasingNames) (ctx : GoInterface) (key : GoString) (rev : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ isLeasingKV lkv γ who pfx γL ∗ Context.ctxOk ctx ∗ ctxPrin who ctx p }}
    (App (App (App (Val (lkv @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.leasing.leasingKV.ty @!! go!"rescind")) (Val #ctx)) (Val #key)) (Val #rev))
  {{ RET #(); True }}

end spec

end Leasing
end EtcdGrove
end Perennial
