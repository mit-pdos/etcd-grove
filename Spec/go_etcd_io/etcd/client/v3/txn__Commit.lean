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

/-- `t.Commit()` on a builder at `b` made from a `*kv` of etcd's KV `γ` (`txnKvIs`, `isKv`, D43): the
request `&pb.TxnRequest{Compare: cmps, Success: sus, Failure: fas}` (the transaction
`txnWireOf b.model` on the wire, of plain operations within the txn package's model) through the
`*kv`'s retry client's `Txn`, with the client's call options, with the caller's update at `γ`
(`txnUpdK`: none or a read update if read-only, a write's if writing; persistent, or fired at
most once on a refusal-free client: `writeUpd`): the call's answer (`txnCallOut` of `txnStOk`, the
state `σ` the update fired at, the reply's verdict, responses and revision as the run's at `σ`;
the error through `ContextError`, a client error). The builder is spent (its slices are now the
request's). -/
abbrev txn.Commit.spec : Prop :=
  ∀ (tp : Loc) (addr : List GoString) (api : Loc) (γ : KVNames) (rf : Bool)
    (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (b : TxnBuild)
    (Q : KVState → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      txnObjAt tp addr ci cd b ∗ txnKvIs tp api ∗ isKv api γ rf ∗
      ⌜TxnModel.plain b.model ∧ txnModelIn (txnWireOf b.model)⌝ ∗
      writeUpd rf (txnUpdK γ (txnWireOf b.model) Q) }}
    (App (Val (tp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.txn.ty @!! go!"Commit"))
      (Val #()))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      txnCallOut (txnStOk (txnWireOf b.model) Q) resp err }}

end spec

end EtcdGrove
end Perennial
