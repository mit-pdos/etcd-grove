/-
`(*clientv3.kv).Delete(ctx, key, opts...)` (`client/v3/kv.go`, translated for the vertical slice's unit V2). Lean-first (no Rocq counterpart).
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

/-- `kv.Delete(ctx, key, opts...)` on a `*kv` over a connection to `addr` (the vertical slice's
unit V2): `kv.Do` of `OpDelete(key, opts...)` (options with transformers `gs` that do not make
`OpDelete` panic nor change the operation's type), the error through `ContextError`:
`deleteCallOut` for the delete the server reads (`deleteWireOf`), for a spec `Spec` registered for
`DeleteRange` and the caller's `Q`. 

etcd#21330 (`pr-verify/etcd-21330`): the premise `emptyKeyIf` of `kv.Do`'s spec (the facts of
`rpctypes.ErrEmptyKey`, which `kv.Do` returns for an empty key, if the key is empty). -/
abbrev kv.Delete.spec : Prop :=
  ∀ (api : Loc) (addr : GoString) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (key : GoString) (sl : GoSlice) (gs : List (OpFull → OpFull))
    (Spec : GrpcSpec (GF := GF) pbDeleteRangeRequest pbDeleteRangeResponse)
    (Q : DelRespM → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ kvObjAt api addr ∗
      ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAt sl gs ∗ emptyKeyIf (opDeleteModel key gs).key ∗
      ⌜¬ opDeletePanics key gs ∧ (opDeleteModel key gs).t = W64 3⌝ ∗
      isGrpcRpc addr go!"/etcdserverpb.KV/DeleteRange" Spec ∗
      □ ▷ Spec (deleteWireOf (opDeleteModel key gs)) Q }}
    (App (App (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!!
        go!"Delete")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #sl))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); deleteCallOut Q resp err }}

end spec

end EtcdGrove
end Perennial
