/-
`(*txnLeasing).guard` (`txn.go`): `guardKeys` then `guardRanges`, appended. Proof sketch: the callees' specs; reads from `protoUpd`.
Changes: from `specs-ref`'s `txnLeasing__guard.lean`: restated over `isLeasingKV`/`Internal.lean` (was the cache's log states and the history premise); weakened to what the leasing contract's proofs need.
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

/-- `guard(ops)`: comparisons, or an error. -/
def txnLeasing.guard.spec : Prop :=
  ∀ (txn : Loc) (γ : Cluster) (who : Principal) (pfx : Key) (γL : LeasingNames) (ctx : GoInterface) (st : TxnSt) (ops : GoSlice) (os : List OpM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ ltxnAt (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.leasing.txnLeasing.ty) #txn) γ who pfx γL ctx st ∗ opsAt ops os ∗ threadTok }}
    (App (Val (txn @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.leasing.txnLeasing.ty @!! go!"guard")) (Val #ops))
  {{ (cs : GoSlice) (err : GoInterface), RET (PairV #cs #err); ltxnAt (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.leasing.txnLeasing.ty) #txn) γ who pfx γL ctx st ∗ opsAt ops os ∗ threadTok ∗
      (⌜err ≠ GoInterface.nil⌝ ∨ (⌜err = GoInterface.nil⌝ ∗ ∃ ms, cmpsAt cs ms)) }}

end spec

end Leasing
end EtcdGrove
end Perennial
