/-
`(*txnLeasing).Then` (`client/v3/leasing/txn.go`).

Users: `leasingKV.Do`; the integration tests. Snippet: `leasing/txn.go`.

Proof sketch: `txn.opst = append(txn.opst, ops...)`; `txn.Txn.Then(ops...)` (W0's `Txn.ThenTriple`: `toReqOps`).

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/leasing/txnLeasing__Then.lean`: over
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

/-- `txn.Then` of a leasing transaction (`LTxn.ThenTriple`). -/
def txnLeasing.Then.spec : Prop :=
  ∀ (txn : Loc) (γ : Cluster) (who : Principal) (pfx : Key) (γL : LeasingNames) (ctx : GoInterface),
  LTxn.ThenTriple (GF := GF) (txn @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.leasing.txnLeasing.ty @!! go!"Then")
    (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.leasing.txnLeasing.ty) #txn) γ who pfx γL ctx

end spec

end Leasing
end EtcdGrove
end Perennial
