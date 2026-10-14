/-
`lkv.waitRescind(ctx, key, rev)` (`client/v3/leasing/kv.go`; unit 5: specified here, proved with the monitors). Lean-first (no Rocq counterpart); see `InvLeasingKV.lean`.
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

/-- **`lkv.waitRescind(ctx, key, rev)`**: watches the lease key `pfx ++ key` from `rev + 1` until
a delete event or the watch's end, and returns `ctx.Err()`. An error, or `nil` after a delete event
(the lease key absent at a revision above `rev`, `leaseKeyDeleted`), **or `nil` with no promise**:
the watch channel closed without a delete event while `ctx` is not done (the watch was canceled,
e.g. its start revision compacted, or the client closed), so the lease key may still exist (a
finding, `STATUS.md`). The context must be cancelable (`WithCancel(ctx)`). -/
abbrev leasingKV.waitRescind.spec : Prop :=
  ∀ (lkv : Loc) (γ : LeasingNames) (pfx : GoString) (ctx : GoInterfaceOk)
    (cs : context.ContextDesc (IProp GF)) (key : GoString) (rev : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ isLeasingKV lkv γ pfx ∗ context.isContext ctx cs ∗ context.isCancelCtxCtx ctx cs ∗
      ⌜0 ≤ sint.Z rev ∧ sint.Z rev < 2 ^ 63 - 1⌝ }}
    (App (App (App (Val (lkv @!! go.GoType.PointerType leasingKV.ty @!! go!"waitRescind")) (Val #(GoInterface.ok ctx))) (Val #key)) (Val #rev))
  {{ (err : GoInterface), RET #err;
      ⌜err ≠ GoInterface.nil⌝ ∨ (⌜err = GoInterface.nil⌝ ∗ leaseKeyDeleted pfx key rev) ∨
      ⌜err = GoInterface.nil⌝ }}

end spec

end leasing
end EtcdGrove
end Perennial
