/-
`(*clientv3.kv).Put(ctx, key, val, opts...)` (`client/v3/kv.go`, translated for unit C1, the client meets the server). Lean-first (no Rocq counterpart).
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

/-- `kv.Put(ctx, key, val, opts...)` on a `*kv` over a connection to `K`: `kv.Do` of
`OpPut(key, val, opts...)` (options with transformers `gs` that do not make `OpPut` panic nor
change the operation's type), the
error through `ContextError`: `putCallOut` for the put the server reads (`putWireOf`). -/
abbrev kv.Put.spec : Prop :=
  ∀ (api : Loc) (K : KVConn GF) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (key val : GoString) (sl : GoSlice) (gs : List (OpFull → OpFull)) (Q : PutRespM → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ kvObjAt api K ∗
      context.isContext ci cd ∗ ctxErrClient ci cd ∗ optsAt sl gs ∗
      ⌜¬ (opPutModel key val gs).putPanics ∧ (opPutModel key val gs).t = W64 2⌝ ∗
      putRunOk K (putWireOf (opPutModel key val gs)) Q }}
    (App (App (App (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!!
        go!"Put")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #val)) (Val #sl))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); putCallOut Q resp err }}

end spec

end EtcdGrove
end Perennial
