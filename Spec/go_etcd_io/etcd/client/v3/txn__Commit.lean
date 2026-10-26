/-
`(*clientv3.txn).Commit()` (`client/v3/kv.go`, translated for the vertical slice's unit V2). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.KVService

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3 client

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `t.Commit()` on a builder at `b` made from a `*kv` of etcd's KV `γ` (`txnKvIs`, `isKv`, D44): the
request `&pb.TxnRequest{Compare: cmps, Success: sus, Failure: fas}` (the transaction
`txnWireOf b.model` on the wire, of plain operations within the txn package's model) through the
`*kv`'s retry client's `Txn`, with the client's call options, with the caller's update of `γ`'s
state: none or a persistent atomic read if read-only; if writing (plain in the KV model, no range
end `[0]`), an atomic update by the transaction (`kvOpStep`); persistent
if the client's writes may be delivered more than once (`□?dup`): `nil` and the reply's message
`m` with the state `σ` the update fired at (`Q σ` if writing, `□ Q σ` if a linearizable read), the
reply's verdict, responses and revision as the run's at `σ`, `σ` a well-formed small log's state
(`kvLogOk`, D48), and so the state after a writing transaction's changes; or a client error (`kvErr`, through
`ContextError`) and no reply. The builder is spent (its slices are now the
request's). -/
abbrev txn.Commit.spec : Prop :=
  ∀ (txn_ptr : Loc) (addr : List GoString) (kv : Loc) (γ : KVNames) (dup : Bool)
    (ctx : GoInterfaceOk) (ctx_desc : context.ContextDesc (IProp GF)) (b : TxnBuild)
    (Q : KVState → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      txnObjAt txn_ptr addr ctx ctx_desc b ∗ txnKvIs txn_ptr kv ∗ isKv kv γ dup ∗
      ⌜TxnModel.plain b.model ∧ txnModelIn (txnWireOf b.model)⌝ ∗
      □?dup (⌜txn.txnReadonly (txnWireOf b.model) = true ∧ Q = fun _ => iprop(True)⌝ ∨
        (⌜txn.txnReadonly (txnWireOf b.model) = true ∧ txn.txnSerializable (txnWireOf b.model) = false⌝ ∗
          □ AU <{ ∃∃ (σ : KVState), etcdKV γ σ }> @ (⊤ \ ↑srvRaftN) \ ↑kvN, ∅
            <{ etcdKV γ σ, COMM □ Q σ }>) ∨
        (⌜txn.txnReadonly (txnWireOf b.model) = false ∧ txn.txnPlain (txnWireOf b.model) ∧ txnNoZeroEnd (txnWireOf b.model)⌝ ∗
          AU <{ ∃∃ (σ : KVState), etcdKV γ σ }> @ (⊤ \ ↑srvRaftN) \ ↑kvN, ∅
            <{ etcdKV γ (kvOpStep (.txn (txnWireOf b.model)) σ), COMM Q σ }>)) }}
    (App (Val (txn_ptr @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.txn.ty @!! go!"Commit"))
      (Val #()))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ (m : TxnRespM) (σ : KVState), txnRespMsg resp m ∗
        (if txn.txnReadonly (txnWireOf b.model) then
          (if txn.txnSerializable (txnWireOf b.model) then iprop(True) else iprop(□ Q σ)) else Q σ) ∗
        ⌜m.succeeded = (txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs (txnWireOf b.model)).1 ∧
          opRespsRel false ((txnWireOf b.model).branch m.succeeded) (txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs (txnWireOf b.model)).2.2 m.resps ∧
          m.hdr.revision = W64 ((if txn.txnReadonly (txnWireOf b.model) then σ.rev else
            (σ.commit (txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs (txnWireOf b.model)).2.1).rev : Nat) : Int) ∧
          σ.rev + 3 < 2 ^ 63 ∧ kvLogOk σ ∧
          (txn.txnReadonly (txnWireOf b.model) = false →
            kvLogOk (σ.commit (txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs (txnWireOf b.model)).2.1))⌝) ∨
      (⌜err ≠ GoInterface.nil ∧ resp = null⌝ ∗ kvErr err) }}

end spec

end EtcdGrove
end Perennial
