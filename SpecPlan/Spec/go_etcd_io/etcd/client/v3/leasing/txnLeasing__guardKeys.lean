/-
`(*txnLeasing).guardKeys` (`txn.go`): a `CreateRevision(pfx++key) < rev+1` comparison for each
single-key write. Proof sketch: `leaseCache.Rev` (a reader slot), W0's `Compare`. Changes: from `specs-ref`'s `txnLeasing__guardKeys.lean`: restated over `isLeasingKV`/`Internal.lean` (was the cache's log states and the history premise); weakened to what the leasing contract's proofs need.
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

/-- `guardKeys(ops)`: comparisons, in a slice whose spare capacity is owned (`guard` appends). -/
def txnLeasing.guardKeys.spec : Prop :=
  ∀ (txn : Loc) (γ : Cluster) (who : Principal) (pfx : Key) (γL : LeasingNames) (ctx : GoInterface) (st : TxnSt) (ops : GoSlice) (os : List OpM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ ltxnAt (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.leasing.txnLeasing.ty) #txn) γ who pfx γL ctx st ∗ opsAt ops os ∗ threadTok }}
    (App (Val (txn @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.leasing.txnLeasing.ty @!! go!"guardKeys")) (Val #ops))
  {{ (cs : GoSlice), RET #cs; ltxnAt (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.leasing.txnLeasing.ty) #txn) γ who pfx γL ctx st ∗ opsAt ops os ∗ threadTok ∗
      ∃ ms, cmpsAt cs ms ∗ ownSliceCap go_etcd_io.etcd.client.v3.Cmp cs (DFrac.own 1) }}

end spec

end Leasing
end EtcdGrove
end Perennial
