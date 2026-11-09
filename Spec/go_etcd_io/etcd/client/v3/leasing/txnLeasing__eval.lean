/-
`(*txnLeasing).eval` (`txn.go`): answers the transaction from the cache if every comparison's key
and the chosen branch's gets are cached. Proof sketch: `gatherOps` (`opsCapOk`, in `ltxnAt`), `NotifyOps` and the waits
(the context's `Done`), read lock, `leaseCache.evalCmp`, `evalOps` (`entryOk` of each with an `etcdLb`, the
latest of them: `etcdLb_ord`; `CachedRange1` of each as in `get`, the marks joined), `copyHeader` of the cache's header (reached).
Changes: from `specs-ref`'s `txnLeasing__eval.lean`: restated over `isLeasingKV`/`Internal.lean` (was the cache's log states and the history premise); weakened to what the leasing contract's proofs need.
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

/-- `eval()`: nothing (`nil`, `nil`: not answerable from the cache), the context's error, or a
cached answer (`CachedAns` at a state reached). -/
def txnLeasing.eval.spec : Prop :=
  ∀ (txn : Loc) (γ : Cluster) (who : Principal) (pfx : Key) (γL : LeasingNames) (ctx : GoInterface) (st : TxnSt),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ ltxnAt (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.leasing.txnLeasing.ty) #txn) γ who pfx γL ctx st ∗ threadTok }}
    (App (Val (txn @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.leasing.txnLeasing.ty @!! go!"eval")) (Val #()))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); ltxnAt (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.leasing.txnLeasing.ty) #txn) γ who pfx γL ctx st ∗ threadTok ∗
      (⌜resp = null ∧ err = GoInterface.nil⌝ ∨ ⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∨
       (∃ (σ0 : State) (res : Resp) (M : Key → Prop), etcdLb γ σ0 ∗ lkvMarks γL M ∗
          ⌜CachedAns who M (.txn st.req) σ0 res⌝ ∗ txnReplyL res resp err)) }}

end spec

end Leasing
end EtcdGrove
end Perennial
