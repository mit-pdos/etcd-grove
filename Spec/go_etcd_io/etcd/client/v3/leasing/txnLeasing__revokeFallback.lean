/-
`(*txnLeasing).revokeFallback` (`txn.go`): `revokeLeaseKvs` of each fallback get's key-values.
Proof sketch: each response a range (`GetResponseRange` non-nil); `revokeLeaseKvs`. Changes: from `specs-ref`'s `txnLeasing__revokeFallback.lean`: restated over `isLeasingKV`/`Internal.lean` (was the cache's log states and the history premise); weakened to what the leasing contract's proofs need.
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

/-- `revokeFallback(fbResps)`: the responses (ranges) read-only, given back. -/
def txnLeasing.revokeFallback.spec : Prop :=
  ∀ (txn : Loc) (γ : Cluster) (who : Principal) (pfx : Key) (ctx : GoInterface) (st : TxnSt) (sl : GoSlice) (dq : DFrac) (ms : List ResponseOpM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ ltxnAt (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.leasing.txnLeasing.ty) #txn) γ who pfx ctx st ∗ msgsOwn responseOpOwn sl dq ms ∗ ⌜∀ r ∈ ms, ∃ rm, r = ResponseOpM.range rm⌝ ∗
      threadTok }}
    (App (Val (txn @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.leasing.txnLeasing.ty @!! go!"revokeFallback")) (Val #sl))
  {{ (err : GoInterface), RET #err; ltxnAt (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.leasing.txnLeasing.ty) #txn) γ who pfx ctx st ∗ msgsOwn responseOpOwn sl dq ms ∗ threadTok }}

end spec

end Leasing
end EtcdGrove
end Perennial
