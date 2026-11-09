/-
`(*leasingKV).Txn` (`client/v3/leasing/kv.go`).

Users: `leasingKV.Do` (a transaction `Op`); the integration tests (`lkv.Txn(ctx).If(...).Then(...)
.Else(...).Commit()`: `TestLeasingTxnOwnerGet`, `TestLeasingTxnOwnerIf`, `TestLeasingTxnAtomicCache`).
Snippet: `leasing/txn.go` (`ReqTxnCAS`).

Proof sketch: `lkv.kv.Txn(ctx)` (`kvAt_methods`: `KV.TxnTriple`, W0's `txnAt t γ who ctx
TxnSt.empty`); allocates the `txnLeasing{Txn: t, lkv, ctx}` (nil slices); `ltxnAt` of it (intended
realization: the fields, `isLeasingKV lkv`, the inner `txnAt` at the same state, the slices'
operations and comparisons read-only and their spare capacities owned).

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/leasing/leasingKV__Txn.lean`: over
`ltxnAt` (was `ownTxnLeasing` with the builder state `LTxnBuild`); W0's `TxnSt`.

Margin: none.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.Api

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

/-- `lkv.Txn` meets the leasing contract's `Txn` (`LKV.TxnTriple`). -/
def leasingKV.Txn.spec : Prop :=
  ∀ (lkv : Loc) (γ : Cluster) (who : Principal) (pfx : Key) (γL : LeasingNames),
  LKV.TxnTriple (lkv @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.leasing.leasingKV.ty @!! go!"Txn")
    (iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ isLeasingKV lkv γ who pfx γL)) γ who pfx

end spec

end Leasing
end EtcdGrove
end Perennial
