/-
`lkv.Delete(ctx, key, opts...)` (`client/v3/leasing/kv.go`). Lean-first (no Rocq counterpart); see `InvLeasingKV.lean`.
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

/-- **`lkv.Delete(ctx, key, opts...)`**: `delete` of `OpDelete(key, opts...)`
(`o := opDeleteModel key gs`). The context must be cancelable. -/
abbrev leasingKV.Delete.spec : Prop :=
  ∀ (lkv : Loc) (γ : LeasingNames) (pfx : GoString) (ctx : GoInterfaceOk)
    (cs : context.ContextDesc (IProp GF)) (key : GoString) (sl : GoSlice)
    (gs : List (OpFull → OpFull)) (lo : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ isLeasingKV lkv γ pfx ∗ lkvReader lkv γ pfx ∗ context.isContext ctx cs ∗ context.isCancelCtxCtx ctx cs ∗
      optsAt sl gs ∗ etcdReached lo ∗
      ⌜¬ opDeletePanics key gs ∧ (opDeleteModel key gs).t = W64 3⌝ }}
    (App (App (App (Val (lkv @!! go.GoType.PointerType leasingKV.ty @!! go!"Delete")) (Val #(GoInterface.ok ctx))) (Val #key)) (Val #sl))
  {{ (dr : Loc) (err : GoInterface), RET (PairV #dr #err); lkvReader lkv γ pfx ∗
      (⌜err ≠ GoInterface.nil ∧ dr = null⌝ ∨
       (⌜err = GoInterface.nil⌝ ∗ deleteCommitted lo (opDeleteModel key gs) dr)) }}

end spec

end leasing
end EtcdGrove
end Perennial
