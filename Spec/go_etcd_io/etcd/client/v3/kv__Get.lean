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

/-- `kv.Get(ctx, key, opts...)` on a `*kv` over a connection to `addr` (`kvObjAt`): `OpGet(key,
opts...)` (options that do not panic, keep the range type, and may need a resource `R`, given
back: `optsAtRes`; any sort option, checked against `etcdserverpb`'s enumerations,
`sortNamesOk`: the vertical slice's unit V2; C1 required none), then `kv.Do`, the error through
`ContextError`: `rangeCallOut` for the range the server reads (`rangeWireOf`), for a spec `Spec`
registered for `Range` and the caller's `Q`. 

etcd#21330 (`pr-verify/etcd-21330`): the premise `emptyKeyIf` of `kv.Do`'s spec (the facts of
`rpctypes.ErrEmptyKey`, which `kv.Do` returns for an empty key, if the key is empty). -/
abbrev kv.Get.spec : Prop :=
  ∀ (api : Loc) (addr : GoString) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (key : GoString) (sl : GoSlice) (gs : List (OpFull → OpFull)) (R : IProp GF)
    (Spec : GrpcSpec (GF := GF) pbRangeRequest pbRangeResponse) (Q : RangeRespM → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ kvObjAt api addr ∗
      ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAtRes sl gs R ∗ R ∗
      sortNamesIf (opGetModel key gs).base.sortSet ∗ emptyKeyIf (opGetModel key gs).key ∗
      ⌜¬ opGetPanics gs ∧ (opGetModel key gs).t = W64 1⌝ ∗
      isGrpcRpc addr go!"/etcdserverpb.KV/Range" Spec ∗
      □ ▷ Spec (rangeWireOf (opGetModel key gs)) Q }}
    (App (App (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!!
        go!"Get")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #sl))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); R ∗ rangeCallOut Q resp err }}

end spec

end EtcdGrove
end Perennial
