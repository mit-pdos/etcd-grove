/-
`txn.If(cs...)` (`client/v3/leasing/txn.go`). Lean-first (no Rocq counterpart); see `InvLeasingKV.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeasingKV

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace leasing

open Iris Iris.BI go_etcd_io.etcd.client.v3.leasing go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

/-- **`txn.If(cs...)`** (once, before `Then` and `Else`), comparisons with their operands set:
appends them to `txn.cs` and to the client's builder; returns `txn`. -/
abbrev txnLeasing.If.spec : Prop :=
  ∀ (txn lkv : Loc) (γ : LeasingNames) (pfx : GoString) (ctx : GoInterfaceOk)
    (cs : context.ContextDesc (IProp GF)) (b : LTxnBuild) (sl : GoSlice) (ms : List CmpModel),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ ownTxnLeasing txn lkv γ pfx ctx cs b ∗ cmpsSetAt sl ms ∗ ⌜b.cif = false ∧ b.cthen = false ∧ b.celse = false⌝ }}
    (App (Val (txn @!! go.GoType.PointerType txnLeasing.ty @!! go!"If")) (Val #sl))
  {{ RET #(GoInterface.ok (txnIface txn));
      ownTxnLeasing txn lkv γ pfx ctx cs { b with cmps := b.cmps ++ ms, cif := true } }}

end spec

end leasing
end EtcdGrove
end Perennial
