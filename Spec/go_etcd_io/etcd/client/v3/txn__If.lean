/-
`(*clientv3.txn).If(cs...)` (`client/v3/kv.go`, translated for the vertical slice's unit V2). Lean-first (no Rocq counterpart).
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

/-- `t.If(cs...)` on a builder that has called none of `If`, `Then`, `Else` (else it panics): the
comparisons' clones appended (`Cmp.Clone`), `cif` set; returns the builder as a `Txn`. -/
abbrev txn.If.spec : Prop :=
  ∀ (tp : Loc) (addr : List GoString) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (b : TxnBuild) (sl : GoSlice) (ms : List CmpModel),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ txnObjAt tp addr ci cd b ∗
      cmpsAt sl ms ∗ ⌜b.cif = false ∧ b.cthen = false ∧ b.celse = false⌝ }}
    (App (Val (tp @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.txn.ty @!! go!"If")) (Val #sl))
  {{ RET #(interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.txn.ty) #tp : GoInterface);
      txnObjAt tp addr ci cd { b with model := { b.model with cmps := b.model.cmps ++ ms }, cif := true } }}

end spec

end EtcdGrove
end Perennial
