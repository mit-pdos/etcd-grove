/-
`lkv.delete(ctx, op)` (`client/v3/leasing/kv.go`). Lean-first (no Rocq counterpart); see `InvLeasingKV.lean`.
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

/-- **`lkv.delete(ctx, op)`** for a delete `op` (`o`): after `waitSession`, a range delete goes to
`deleteRange`; a key's delete is committed by `tryModifyOp` or `revoke` (both, if the key is not
cached: a finding) until one succeeds or the context is done, and deleted from the cache.
Returns an error, or the delete of `o`'s range (`deleteCommitted`). The context must be
cancelable. -/
abbrev leasingKV.delete.spec : Prop :=
  ∀ (lkv : Loc) (γ : LeasingNames) (pfx : GoString) (ctx : GoInterfaceOk)
    (cs : context.ContextDesc (IProp GF)) (opv : go_etcd_io.etcd.client.v3.Op) (o : OpFull)
    (lo : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ isLeasingKV lkv γ pfx ∗ lkvReader lkv γ pfx ∗ context.isContext ctx cs ∗ context.isCancelCtxCtx ctx cs ∗
      opFullAt opv o ∗ etcdReached lo ∗ ⌜o.t = W64 3⌝ }}
    (App (App (Val (lkv @!! go.GoType.PointerType leasingKV.ty @!! go!"delete")) (Val #(GoInterface.ok ctx))) (Val #opv))
  {{ (dr : Loc) (err : GoInterface), RET (PairV #dr #err); lkvReader lkv γ pfx ∗
      (⌜err ≠ GoInterface.nil ∧ dr = null⌝ ∨ (⌜err = GoInterface.nil⌝ ∗ deleteCommitted lo o dr)) }}

end spec

end leasing
end EtcdGrove
end Perennial
