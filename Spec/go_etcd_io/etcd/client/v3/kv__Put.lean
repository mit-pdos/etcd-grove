/-
`(*clientv3.kv).Put(ctx, key, val, opts...)` (`client/v3/kv.go`, translated for unit C1, the client meets the server). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.KVService

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3 client

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `kv.Put(ctx, key, val, opts...)` on a `*kv` of etcd's KV `γ` (`isKv`, D43: its members hidden):
`kv.Do` of `OpPut(key, val, opts...)` (options with transformers `gs` that do not make `OpPut`
panic nor change the operation's type), a put with no lease (etcd's `Put` spec covers no other)
that `γ`'s workload admits, with the caller's atomic update of `γ`'s state by the put the server
reads (`putWireOf`; `kvOpStep`), persistent if the client's writes may be delivered more than once
(`□?dup`); the error through `ContextError`:
`putCallOut` of `putStOk`, the state `σ` the update fired at (`Q σ`), the reply's revision `σ`'s
next and its previous key-value `σ`'s if asked. -/
abbrev kv.Put.spec : Prop :=
  ∀ (api : Loc) (γ : KVNames) (dup : Bool) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (key val : GoString) (sl : GoSlice)
    (gs : List (OpFull → OpFull)) (Q : KVState → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ isKv api γ dup ∗
      ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAt sl gs ∗
      ⌜¬ (opPutModel key val gs).putPanics ∧ (opPutModel key val gs).t = W64 2 ∧
        (putWireOf (opPutModel key val gs)).leaseID = W64 0 ∧ γ.wl.writes (.put (putWireOf (opPutModel key val gs)))⌝ ∗
      □?dup (AU <{ ∃∃ (σ : KVState), etcdKV γ σ }> @ (⊤ \ ↑srvRaftN) \ ↑kvN, ∅
        <{ etcdKV γ (kvOpStep (.put (putWireOf (opPutModel key val gs))) σ), COMM Q σ }>) }}
    (App (App (App (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!!
        go!"Put")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #val)) (Val #sl))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      putCallOut (putStOk (putWireOf (opPutModel key val gs)) Q) resp err }}

end spec

end EtcdGrove
end Perennial
