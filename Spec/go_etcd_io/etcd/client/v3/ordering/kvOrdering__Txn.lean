/-
`(*kvOrdering).Txn(ctx)` (`client/v3/ordering/kv.go`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.ordering.InvOrdering

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ordering

open Iris Iris.BI go_etcd_io.etcd.client.v3.ordering

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.ordering.Assumptions]
variable [MutexCompositeLiteral]

/-- `kv.Txn(ctx)`: calls `kv.KV.Txn(ctx)` to obtain `innerTxn`, and allocates a `*txnOrdering`
builder initialized with empty `cmps`, `thenOps`, and `elseOps` slices (`slice.nil`). -/
abbrev kvOrdering.Txn.spec : Prop :=
  ∀ (kvp : Loc) (kv : go_etcd_io.etcd.client.v3.KV) (vf : OrderViolationFunc)
    (ctx : context.Context) (P : IProp GF) (Q : go_etcd_io.etcd.client.v3.Txn → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.ordering ∗
      isKvOrdering kvp kv vf ∗ P ∗
      {{ P }} (App (ifaceMethod kv go!"Txn") (Val #ctx))
      {{ (innerTxn : go_etcd_io.etcd.client.v3.Txn), RET #innerTxn; Q innerTxn }} }}
    (App (Val (kvp @!! go.GoType.PointerType kvOrdering.ty @!! go!"Txn")) (Val #ctx))
  {{ (txnp : Loc), RET #(interface.mkOk (go.GoType.PointerType txnOrdering.ty) #txnp);
      ∃ (innerTxn : go_etcd_io.etcd.client.v3.Txn) (csl tsl esl : GoSlice),
        Q innerTxn ∗
        ownTxnOrdering txnp kvp innerTxn ctx
          ⟨csl, tsl, esl, [], [], []⟩ }}

end spec

end ordering
end EtcdGrove
end Perennial
