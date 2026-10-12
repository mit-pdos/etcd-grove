/-
`lkv.deleteRange(ctx, op)` (`client/v3/leasing/kv.go`). Lean-first (no Rocq counterpart); see `InvLeasingKV.lean`.
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
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

/-- **`lkv.deleteRange(ctx, op)`** for a range delete `op` (`o`): until the context is done,
revokes the range's lease keys, locks the cached entries in range, and runs `deleteRangeRPC`.
Returns an error, or the delete of `o`'s range (`deleteCommitted`). The context must be
cancelable. -/
abbrev leasingKV.deleteRange.spec : Prop :=
  ∀ (lkv : Loc) (γ : LeasingNames) (pfx : GoString) (ctx : GoInterfaceOk)
    (cs : context.ContextDesc (IProp GF)) (opv : go_etcd_io.etcd.client.v3.Op) (o : OpFull)
    (lo : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ isLeasingKV lkv γ pfx ∗ lkvReader lkv γ pfx ∗ sessionReady γ ∗ context.isContext ctx cs ∗
      context.isCancelCtxCtx ctx cs ∗ opFullAt opv o ∗ etcdReached lo }}
    (App (App (Val (lkv @!! go.GoType.PointerType leasingKV.ty @!! go!"deleteRange")) (Val #(GoInterface.ok ctx))) (Val #opv))
  {{ (dr : Loc) (err : GoInterface), RET (PairV #dr #err); lkvReader lkv γ pfx ∗
      (⌜err ≠ GoInterface.nil ∧ dr = null⌝ ∨ (⌜err = GoInterface.nil⌝ ∗ deleteCommitted lo o dr)) }}

end spec

end leasing
end EtcdGrove
end Perennial
