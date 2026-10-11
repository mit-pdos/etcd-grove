/-
`lkv.revokeRange(ctx, begin, end)` (`client/v3/leasing/kv.go`). Lean-first (no Rocq counterpart); see `InvLeasingKV.lean`.
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

/-- **`lkv.revokeRange(ctx, begin, end)`**: gets the lease keys of `[pfx ++ begin, pfx ++ end)`
(the lease key of `begin` alone if `end` is empty) and revokes them (`revokeLeaseKvs`): an error,
or `nil` (the largest create revision is the guard of the caller's range delete, which is
correct whatever it is: no promise). -/
abbrev leasingKV.revokeRange.spec : Prop :=
  ∀ (lkv : Loc) (γ : LeasingNames) (pfx : GoString) (ctx : GoInterfaceOk)
    (cs : context.ContextDesc (IProp GF)) (b e : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ isLeasingKV lkv γ pfx ∗ lkvReader lkv γ pfx ∗ sessionReady γ ∗ context.isContext ctx cs ∗
      context.isCancelCtxCtx ctx cs }}
    (App (App (App (Val (lkv @!! go.GoType.PointerType leasingKV.ty @!! go!"revokeRange")) (Val #(GoInterface.ok ctx))) (Val #b)) (Val #e))
  {{ (maxRev : w64) (err : GoInterface), RET (PairV #maxRev #err); lkvReader lkv γ pfx }}

end spec

end leasing
end EtcdGrove
end Perennial
