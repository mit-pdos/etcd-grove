/-
`(*clientv3.kv).Get(ctx, key, opts...)` (`client/v3/kv.go`, translated for unit C1, the client meets the server). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvKVConn

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `kv.Get(ctx, key, opts...)` on a `*kv` over a connection to `K`: `kv.Do` of
`OpGet(key, opts...)` (options with transformers `gs` that do not make `OpGet` panic nor set a
sort), the error through `ContextError`: `rangeCallOut` for the range the server reads
(`rangeWireOf`). -/
abbrev kv.Get.spec : Prop :=
  ∀ (api : Loc) (K : KVConn GF) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (key : GoString) (sl : GoSlice) (gs : List (OpFull → OpFull)) (Q : RangeRespM → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ kvObjAt api K ∗
      context.isContext ci cd ∗ ctxErrClient ci cd ∗ optsAt sl gs ∗
      ⌜¬ opGetPanics gs ∧ (opGetModel key gs).t = W64 1 ∧
        (opGetModel key gs).base.sortSet = false⌝ ∗
      rangeRunOk K (rangeWireOf (opGetModel key gs)) Q }}
    (App (App (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!!
        go!"Get")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #sl))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); rangeCallOut Q resp err }}

end spec

end EtcdGrove
end Perennial
