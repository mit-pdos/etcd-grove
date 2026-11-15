/-
`(*txnLeasing).Else` (`client/v3/leasing/txn.go`).

Users: `leasingKV.Do`; the integration tests. Snippet: `leasing/txn.go`.

Proof sketch: `txn.opse = append(txn.opse, ops...)`; `txn.Txn.Else(ops...)` (W0's `Txn.ElseTriple`).

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/leasing/txnLeasing__Else.lean`: over
`ltxnAt` and W0's `TxnSt` (was `ownTxnLeasing`, `LTxnBuild`).

Margin: none.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.client.v3.leasing.Api

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

/-- `txn.Else` of a leasing transaction (`LTxn.ElseTriple`). -/
def txnLeasing.Else.spec : Prop :=
  ∀ (txn : Loc) (γ : Cluster) (who : Principal) (pfx : Key) (γL : LeasingNames) (ctx : GoInterface),
  LTxn.ElseTriple (GF := GF) (txn @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.leasing.txnLeasing.ty @!! go!"Else")
    (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.leasing.txnLeasing.ty) #txn) γ who pfx γL ctx

end spec

end Leasing
end EtcdGrove
end Perennial
