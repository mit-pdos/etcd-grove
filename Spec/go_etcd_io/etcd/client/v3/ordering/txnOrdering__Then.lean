/-
`(*txnOrdering).Then(ops...)` (`client/v3/ordering/kv.go`). Lean-first (no Rocq counterpart).
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

/-- `txn.Then(ops...)`: locks `txn.mu`, sets `txn.thenOps = ops`, delegates `txn.Txn.Then(ops...)`,
and returns `txn` as a `clientv3.Txn` interface with updated `thenOps` state. -/
abbrev txnOrdering.Then.spec : Prop :=
  ∀ (txnp kvp : Loc) (innerTxn : go_etcd_io.etcd.client.v3.Txn)
    (ctx : context.Context) (st : TxnOrderingState)
    (tsl' : GoSlice) (ts' : List OpT) (P Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.ordering ∗
      ownTxnOrdering txnp kvp innerTxn ctx st ∗
      opsTAt tsl' ts' ∗ P ∗
      {{ P }} (App (ifaceMethod innerTxn go!"Then") (Val #tsl'))
      {{ (r : go_etcd_io.etcd.client.v3.Txn), RET #r; Q }} }}
    (App (Val (txnp @!! go.GoType.PointerType txnOrdering.ty @!! go!"Then")) (Val #tsl'))
  {{ RET #(interface.mkOk (go.GoType.PointerType txnOrdering.ty) #txnp);
      Q ∗ ownTxnOrdering txnp kvp innerTxn ctx { st with tsl := tsl', ts := ts' } }}

end spec

end ordering
end EtcdGrove
end Perennial
