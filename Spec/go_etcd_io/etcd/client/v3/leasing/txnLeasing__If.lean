/-
`(*txnLeasing).If` (`client/v3/leasing/txn.go`).

Users: `leasingKV.Do` (a transaction `Op`'s comparisons); the integration tests. Snippet: `leasing/txn.go`.

Proof sketch: `txn.cs = append(txn.cs, cs...)` (its owned capacity; the comparisons copied, read-only);
`txn.Txn.If(cs...)` (W0's `Txn.IfTriple` on the inner `txnAt`, same premises); stores it back.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/leasing/txnLeasing__If.lean`: over
`ltxnAt` and W0's `TxnSt` (was `ownTxnLeasing`, `LTxnBuild`).

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

/-- `txn.If` of a leasing transaction (`LTxn.IfTriple`). -/
def txnLeasing.If.spec : Prop :=
  ∀ (txn : Loc) (γ : Cluster) (who : Principal) (pfx : Key) (γL : LeasingNames) (ctx : GoInterface),
  LTxn.IfTriple (GF := GF) (txn @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.leasing.txnLeasing.ty @!! go!"If")
    (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.leasing.txnLeasing.ty) #txn) γ who pfx γL ctx

end spec

end Leasing
end EtcdGrove
end Perennial
