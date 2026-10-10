/-
`lkv.Get(ctx, key, opts...)` (`client/v3/leasing/kv.go`). Lean-first (no Rocq counterpart); see `InvLeasingKV.lean`.
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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

/-- **`lkv.Get(ctx, key, opts...)`**: `get` of `OpGet(key, opts...)` (`o := opGetModel key gs`). -/
abbrev leasingKV.Get.spec : Prop :=
  ∀ (lkv : Loc) (γ : LeasingNames) (pfx : GoString) (ctx : GoInterfaceOk)
    (cs : context.ContextDesc (IProp GF)) (key : GoString) (sl : GoSlice)
    (gs : List (OpFull → OpFull)) (lo : w64) (q : Qp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ isLeasingKV lkv γ pfx ∗ lkvReader lkv γ pfx ∗ lkvReader lkv γ pfx ∗ context.isContext ctx cs ∗ optsAt sl gs ∗ etcdReached lo ∗
      ⌜¬ opGetPanics gs ∧ (opGetModel key gs).t = W64 1⌝ ∗ leasingOpen γ q ∗ threadTok }}
    (App (App (App (Val (lkv @!! go.GoType.PointerType leasingKV.ty @!! go!"Get")) (Val #(GoInterface.ok ctx))) (Val #key)) (Val #sl))
  {{ (ret : Loc) (err : GoInterface), RET (PairV #ret #err); lkvReader lkv γ pfx ∗ leasingOpen γ q ∗ threadTok ∗
      getOutcome γ pfx lo (opGetModel key gs) ret err (lkvReader lkv γ pfx) }}

end spec

end leasing
end EtcdGrove
end Perennial
