/-
`(*txnLeasing).serverTxn` (`txn.go`): `If(guards).Then(OpTxn(cs, opst, opse)).Else(fallback)`, until
it commits or errs. Proof sketch: `waitSession`; `gatherOps` (`opsCapOk`) into the owned capacity of
`opst`; `OpTxn` (W0); `fallback`; `LockWriteOps` (closed by the deferred `closeAll`); loop: `guard`,
the inner `Commit` with an update from the caller's (success: the nested transaction's `Step`, a
pure fact of the model's nested `TxnRun`, the outer valid iff the nested is: `kvStep`'s `t.valid`; failure: reads only, abort); `commitToCache`; the nested
reply with the outer header (`txnReplyL`); or `revokeFallback` and retry. Changes: from `specs-ref`'s `txnLeasing__serverTxn.lean`: restated over `isLeasingKV`/`Internal.lean` (was the cache's log states and the history premise); weakened to what the leasing contract's proofs need.
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

/-- `serverTxn()`: as `LTxn.CommitTriple`, answered by a member. -/
def txnLeasing.serverTxn.spec : Prop :=
  ∀ (txn : Loc) (γ : Cluster) (who : Principal) (pfx : Key) (γL : LeasingNames) (ctx : GoInterface) (st : TxnSt) (Q : State → State → Resp → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ ltxnAt (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.leasing.txnLeasing.ty) #txn) γ who pfx γL ctx st ∗ lkvMarks γL (reqWrites (.txn st.req)) ∗ threadTok ∗ □ AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (r : Option Resp), lstep γL pfx who (.txn st.req) σ σ' r ∗ etcdState γ σ',
           COMM LQ Q σ σ' r }> }}
    (App (Val (txn @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.leasing.txnLeasing.ty @!! go!"serverTxn")) (Val #()))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); ltxnAt (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.leasing.txnLeasing.ty) #txn) γ who pfx γL ctx st ∗ threadTok ∗
      ((∃ σ σ' res, Q σ σ' res ∗ txnReplyL res resp err) ∨ ⌜resp = null ∧ err ≠ GoInterface.nil⌝) }}

end spec

end Leasing
end EtcdGrove
end Perennial
