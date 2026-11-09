/-
`(*leasingKV).revoke` (`kv.go`): `If(CreateRevision(pfx++key) < rev+1).Then(op).Else(OpPut(pfx++key,
"REVOKE", WithIgnoreLease()))`, then `waitRescind` if the guard failed. Proof sketch: the inner
`Commit`'s update from the caller's: success fires `some res` (the operation's `Step`); failure is
the `"REVOKE"` put, a `ProtoStep`, fired as `none` (why a write's update must accept protocol steps,
`Api.lean`'s header, 2.). `op` is a put, a single-key delete, or `OpGet(key)` (from
`revokeLeaseKvs`, with an update built from `protoUpd`). Changes: from `specs-ref`'s `leasingKV__revoke.lean`: restated over `isLeasingKV`/`Internal.lean` (was the cache's log states and the history premise); weakened to what the leasing contract's proofs need.
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

/-- `revoke(ctx, key, op)`: an error; or no error and the guard failed (`Succeeded` false); or the
operation committed (one firing's `Q`, the owned reply). -/
def leasingKV.revoke.spec : Prop :=
  ∀ (lkv : Loc) (γ : Cluster) (who : Principal) (pfx : Key) (γL : LeasingNames) (ctx : GoInterface) (key : GoString) (op : go_etcd_io.etcd.client.v3.Op) (o : OpM)
    (rq : Req) (Q : State → State → Resp → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ isLeasingKV lkv γ who pfx γL ∗ Context.ctxOk ctx ∗ ctxPrin ctx who ∗ opAt op o ∗
      ⌜o.toReq = some rq ∧ o.t ≠ tTxn ∧ o.rangeEnd.getD [] = []⌝ ∗ threadTok ∗ □ AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (r : Option Resp), ⌜LStep pfx who (rq) σ σ' r⌝ ∗ etcdState γ σ',
           COMM LQ Q σ σ' r }> }}
    (App (App (App (Val (lkv @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.leasing.leasingKV.ty @!! go!"revoke")) (Val #ctx)) (Val #key)) (Val #op))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); threadTok ∗
      (⌜err ≠ GoInterface.nil⌝ ∨
       (⌜err = GoInterface.nil⌝ ∗ ∃ m, txnRespOwn resp (DFrac.own 1) m ∗ ⌜m.succeeded = false⌝) ∨
       (⌜err = GoInterface.nil⌝ ∗ ∃ σ σ' res m, Q σ σ' res ∗ txnRespOwn resp (DFrac.own 1) m ∗
          ⌜guardedReply res m⌝)) }}

end spec

end Leasing
end EtcdGrove
end Perennial
