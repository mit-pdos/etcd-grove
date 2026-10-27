/-
`(*clientv3.kv).Do(ctx, op)` (`client/v3/kv.go`, translated for unit C1, the client meets the server). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.KVService

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3 client

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **What `kv.Do` needs of its `Op`** `o` on a `*kv` of etcd's KV `γ` (D44): a range (any sort
option, checked against `etcdserverpb`'s enumerations, `sortNamesOk` if there
is one) with the caller's persistent atomic read of `γ`'s state or, `Q` trivial, none; a put with
no lease or a delete whose range end is not `[0]` (what etcd's specs cover), with the caller's atomic update of `γ`'s state by it (`kvOpStep`), persistent if the
client's writes may be delivered more than once (`□?dup`), all of the request the server reads (`rangeWireOf o`, `putWireOf o`, `deleteWireOf o`); a transaction
(`OpTxn`, `Op.toTxnRequest`) is not specified here (`kv.Txn`'s builder sends one:
`txn.Commit`). -/
def doRunOk (γ : KVNames) (dup : Bool) (o : OpFull) (Q : KVState → IProp GF) : IProp GF :=
  iprop((⌜o.t = W64 1⌝ ∗ sortNamesIf o.base.sortSet ∗
      □ (⌜Q = fun _ => iprop(True)⌝ ∨ (⌜(rangeWireOf o).base.serializable = false⌝ ∗
        AU <{ ∃∃ (σ : KVState), etcdKV γ σ }> @ (⊤ \ ↑srvRaftN) \ ↑kvN, ∅
        <{ etcdKV γ σ, COMM □ Q σ }>))) ∨
    (⌜o.t = W64 2 ∧ (putWireOf o).leaseID = W64 0⌝ ∗
      □?dup (AU <{ ∃∃ (σ : KVState), etcdKV γ σ }> @ (⊤ \ ↑srvRaftN) \ ↑kvN, ∅
        <{ etcdKV γ (kvOpStep (.put (putWireOf o)) σ), COMM Q σ }>)) ∨
    (⌜o.t = W64 3 ∧ (deleteWireOf o).base.rangeEnd ≠ [W8 0]⌝ ∗
      □?dup (AU <{ ∃∃ (σ : KVState), etcdKV γ σ }> @ (⊤ \ ↑srvRaftN) \ ↑kvN, ∅
        <{ etcdKV γ (kvOpStep (.deleteRange (deleteWireOf o)) σ), COMM Q σ }>)))

/-- `kv.Do(ctx, op)` on a `*kv` of etcd's KV `γ` (`isKv`, D44), for an `Op` `op` modelled by `op_m`
that is a range, a put or a delete (`doRunOk`): the request `op.toRangeRequest()`,
`&pb.PutRequest{...}` or `&pb.DeleteRangeRequest{...}` through the retry client's `Range`, `Put`
or `DeleteRange`, with the client's call options; `doOut` with the reply's fields as functions of
the state the update fired at (`rangeStOk`, `putStOk`, `delStOk`). -/
abbrev kv.Do.spec : Prop :=
  ∀ (kv : Loc) (γ : KVNames) (dup : Bool) (ctx : GoInterfaceOk)
    (ctx_desc : context.ContextDesc (IProp GF)) (op : go_etcd_io.etcd.client.v3.Op) (op_m : OpFull)
    (Q : KVState → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ isKv kv γ dup ∗
      ctxOk ctx ctx_desc ∗ ctxErrClient ctx ctx_desc ∗ opFullAt op op_m ∗ doRunOk γ dup op_m Q }}
    (App (App (Val (kv @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!! go!"Do"))
      (Val #(GoInterface.ok ctx))) (Val #op))
  {{ (r : go_etcd_io.etcd.client.v3.OpResponse) (err : GoInterface), RET (PairV #r #err);
      doOut op_m (putStOk (putWireOf op_m) Q) (rangeStOk (rangeWireOf op_m) Q)
        (delStOk (deleteWireOf op_m) Q) r err }}

end spec

end EtcdGrove
end Perennial
