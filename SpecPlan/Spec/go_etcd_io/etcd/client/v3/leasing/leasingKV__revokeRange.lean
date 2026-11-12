/-
`(*leasingKV).revokeRange` (`kv.go`): reads the lease keys of `[pfx++begin, pfx++end)` and revokes
the others' (`revokeLeaseKvs`). Proof sketch: `kv.Get` (a read, from `protoUpd`), its key-values
read-only; `revokeLeaseKvs`. The bound it returns is not relied on by the contract's proofs.
Changes: from `specs-ref`'s `leasingKV__revokeRange.lean`: restated over `isLeasingKV`/`Internal.lean` (was the cache's log states and the history premise); weakened to what the leasing contract's proofs need.
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

/-- `revokeRange(ctx, begin, end)`. -/
def leasingKV.revokeRange.spec : Prop :=
  ∀ (lkv : Loc) (γ : Cluster) (who p : Principal) (pfx : Key) (γL : LeasingNames) (ctx : GoInterface) (b «end» : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ isLeasingKV lkv γ who pfx γL ∗ Context.ctxOk ctx ∗ ctxPrin who ctx p ∗ threadTok }}
    (App (App (App (Val (lkv @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.leasing.leasingKV.ty @!! go!"revokeRange")) (Val #ctx)) (Val #b)) (Val #«end»))
  {{ (rev : w64) (err : GoInterface), RET (PairV #rev #err); threadTok }}

end spec

end Leasing
end EtcdGrove
end Perennial
