/-
`(*clientv3.txn).Else(ops...)` (`client/v3/kv.go`, translated for the vertical slice's unit V2). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvTxnBuilder

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `t.Else(ops...)` (before nothing: once; else it panics) with operations `ts`, each a plain
operation or a nested transaction (`OpTxn`), whose transaction operations are `ops` (`OpT.txnOps`:
every get at revision `0`, every put one etcd accepts): their requests (`Op.toRequestOp`, nested
ones recursively) appended, `celse` set; returns the builder as a `Txn`. -/
abbrev txn.Else.spec : Prop :=
  ∀ (tp : Loc) (addr : List GoString) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (b : TxnBuild) (sl : GoSlice) (ts : List OpT) (ops : List TxnOp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ txnObjAt tp addr ci cd b ∗
      opsTAt sl ts ∗ ⌜OpT.txnOps ts = some ops ∧ b.celse = false⌝ }}
    (App (Val (tp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.txn.ty @!! go!"Else")) (Val #sl))
  {{ RET #(interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.txn.ty) #tp : GoInterface);
      txnObjAt tp addr ci cd { b with model := { b.model with elseOps := b.model.elseOps ++ ops }, celse := true } }}


end spec

end EtcdGrove
end Perennial
