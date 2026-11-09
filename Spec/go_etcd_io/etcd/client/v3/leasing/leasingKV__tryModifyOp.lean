/-
`(*leasingKV).tryModifyOp` (`kv.go`): locks `key`'s entry, commits `If(CreateRevision(pfx++key) <
rev+1).Then(op)`. Proof sketch: `leaseCache.Lock`; the inner `Commit` (W0's `Txn.CommitTriple`) with
an update built from the caller's: success fires `some res` (`Step` of the operation: the guard
held and the branch is the operation alone, a pure fact of the model), a guard's failure or an error
answer leaves the state, aborts; on error `Evict` and close the channel. The operation is a put or
a single-key delete (a range delete's request would keep `prevKv`, `execReq`). Changes: from `specs-ref`'s `leasingKV__tryModifyOp.lean`: restated over `isLeasingKV`/`Internal.lean` (was the cache's log states and the history premise); weakened to what the leasing contract's proofs need.
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

/-- `tryModifyOp(ctx, op)`: nothing (`nil`, `nil`: the guard failed, or an error), or the
operation committed: one firing's `Q`, the owned reply (`guardedReply`), the key's waiter channel to
close (`nil` if the key is not cached). -/
def leasingKV.tryModifyOp.spec : Prop :=
  ∀ (lkv : Loc) (γ : Cluster) (who : Principal) (pfx : Key) (γL : LeasingNames) (ctx : GoInterface) (op : go_etcd_io.etcd.client.v3.Op) (o : OpM) (rq : Req)
    (Q : State → State → Resp → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ isLeasingKV lkv γ who pfx γL ∗ Context.ctxOk ctx ∗ ctxPrin ctx who ∗ opAt op o ∗
      ⌜o.toReq = some rq ∧ (o.t = tPut ∨ (o.t = tDeleteRange ∧ o.rangeEnd.getD [] = []))⌝ ∗
      □ AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (r : Option Resp), ⌜LStep pfx who (rq) σ σ' r⌝ ∗ etcdState γ σ',
           COMM LQ Q σ σ' r }> }}
    (App (App (Val (lkv @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.leasing.leasingKV.ty @!! go!"tryModifyOp")) (Val #ctx)) (Val #op))
  {{ (resp : Loc) (wc : GoChan) (err : GoInterface), RET (PairV (PairV #resp #wc) #err);
      ⌜resp = null ∧ wc = null⌝ ∨
      (⌜err = GoInterface.nil⌝ ∗ ∃ σ σ' res m, Q σ σ' res ∗ txnRespOwn resp (DFrac.own 1) m ∗
        ⌜guardedReply res m⌝ ∗ (⌜wc = null⌝ ∨ waitCloser wc)) }}

end spec

end Leasing
end EtcdGrove
end Perennial
