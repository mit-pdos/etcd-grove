/-
`lkv.Put(ctx, key, val, opts...)` (`client/v3/leasing/kv.go`). Lean-first (no Rocq counterpart); see `InvLeasingKV.lean`.
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

/-- **`lkv.Put(ctx, key, val, opts...)`**: `put` of `OpPut(key, val, opts...)` (`o := opPutModel key
val gs`, a put a transaction can run: `top`). The context must be cancelable. The operation's key
and range end are at most `2 ^ 27` bytes and its value `2 ^ 28` (`OpShape`: leasing's own requests
carry it with the prefixed key; "Leasing's sizes"). -/
abbrev leasingKV.Put.spec : Prop :=
  ∀ (lkv : Loc) (γ : LeasingNames) (pfx : GoString) (ctx : GoInterfaceOk)
    (cs : context.ContextDesc (IProp GF)) (key val : GoString) (sl : GoSlice)
    (gs : List (OpFull → OpFull)) (top : TxnOp) (lo : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ isLeasingKV lkv γ pfx ∗ lkvReader lkv γ pfx ∗ context.isContext ctx cs ∗ context.isCancelCtxCtx ctx cs ∗
      optsAt sl gs ∗ etcdReached lo ∗
      ⌜¬ (opPutModel key val gs).putPanics ∧ (opPutModel key val gs).t = W64 2 ∧
        txnOpOf (opPutModel key val gs) = some top ∧ OpShape (2 ^ 27) (2 ^ 27) (2 ^ 28) (opPutModel key val gs)⌝ }}
    (App (App (App (App (Val (lkv @!! go.GoType.PointerType leasingKV.ty @!! go!"Put")) (Val #(GoInterface.ok ctx))) (Val #key)) (Val #val)) (Val #sl))
  {{ (pr : Loc) (err : GoInterface), RET (PairV #pr #err); lkvReader lkv γ pfx ∗
      (⌜err ≠ GoInterface.nil ∧ pr = null⌝ ∨
       (⌜err = GoInterface.nil⌝ ∗ putCommitted γ lo (opPutModel key val gs) top pr)) }}

end spec

end leasing
end EtcdGrove
end Perennial
