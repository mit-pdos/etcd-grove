/-
`(*txnLeasing).fallback` (`txn.go`): a get of the lease keys of each write. Proof sketch:
`OpGet(pfx++key, WithRange(lend))` (W0's `OpGet`, `WithRange`). Changes: from `specs-ref`'s `txnLeasing__fallback.lean`: restated over `isLeasingKV`/`Internal.lean` (was the cache's log states and the history premise); weakened to what the leasing contract's proofs need.
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

/-- `fallback(ops)`: gets (ranges) only. -/
def txnLeasing.fallback.spec : Prop :=
  ∀ (txn : Loc) (γ : Cluster) (who : Principal) (pfx : Key) (ctx : GoInterface) (st : TxnSt) (ops : GoSlice) (os : List OpM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ ltxnAt (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.leasing.txnLeasing.ty) #txn) γ who pfx ctx st ∗ opsAt ops os }}
    (App (Val (txn @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.leasing.txnLeasing.ty @!! go!"fallback")) (Val #ops))
  {{ (fb : GoSlice), RET #fb; ltxnAt (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.leasing.txnLeasing.ty) #txn) γ who pfx ctx st ∗ opsAt ops os ∗ ∃ (fos : List OpM) (rs : List RequestOp),
      opsAt fb fos ∗ ⌜OpM.toReqOps fos = some rs ∧ ∀ r ∈ rs, ∃ rr, r = RequestOp.range rr⌝ }}

end spec

end Leasing
end EtcdGrove
end Perennial
