/-
`txn.guard(ops)` (`client/v3/leasing/txn.go`). Lean-first (no Rocq counterpart); see `InvLeasingKV.lean`.
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

/-- **`txn.guard(ops)`**: `guardKeys` then `guardRanges`: an error, or comparisons. The context
must be cancelable. -/
abbrev txnLeasing.guard.spec : Prop :=
  ∀ (txn lkv : Loc) (γ : LeasingNames) (pfx : GoString) (ctx : GoInterfaceOk)
    (cs : context.ContextDesc (IProp GF)) (dq : DFrac) (sl : GoSlice) (os : List OpFull),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ structFieldRef txnLeasing go!"lkv" txn ↦{dq} lkv ∗
      structFieldRef txnLeasing go!"ctx" txn ↦{dq} GoInterface.ok ctx ∗ isLeasingKV lkv γ pfx ∗ lkvReader lkv γ pfx ∗
      sessionReady γ ∗ context.isContext ctx cs ∗ context.isCancelCtxCtx ctx cs ∗ opsAt sl os }}
    (App (Val (txn @!! go.GoType.PointerType txnLeasing.ty @!! go!"guard")) (Val #sl))
  {{ (cmps : GoSlice) (err : GoInterface), RET (PairV #cmps #err);
      structFieldRef txnLeasing go!"lkv" txn ↦{dq} lkv ∗
      structFieldRef txnLeasing go!"ctx" txn ↦{dq} GoInterface.ok ctx ∗ lkvReader lkv γ pfx ∗
      (⌜err ≠ GoInterface.nil⌝ ∨ (⌜err = GoInterface.nil⌝ ∗ ∃ ms : List CmpModel, cmpsAt cmps ms)) }}

end spec

end leasing
end EtcdGrove
end Perennial
