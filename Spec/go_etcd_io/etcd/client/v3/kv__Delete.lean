/-
`(*clientv3.kv).Delete(ctx, key, opts...)` (`client/v3/kv.go`, translated for the vertical slice's unit V2). Lean-first (no Rocq counterpart).
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

/-- `kv.Delete(ctx, key, opts...)` on a `*kv` of etcd's KV `γ` (`isKv`, D43): `kv.Do` of
`OpDelete(key, opts...)` (options with transformers `gs` that do not make `OpDelete` panic nor
change the operation's type), a delete whose range end is not `[0]` (etcd's `DeleteRange` spec
covers no other: `WithFromKey`'s), with the caller's update of the delete the server reads
(`deleteWireOf`) at `γ` (persistent, or fired at most once on a refusal-free client:
`writeUpd`); the error through `ContextError`: `deleteCallOut` of `delStOk`, the state `σ` the
update fired at (`Q σ`), the reply's count, previous key-values and revision as `σ`'s. -/
abbrev kv.Delete.spec : Prop :=
  ∀ (api : Loc) (γ : KVNames) (rf : Bool) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (key : GoString) (sl : GoSlice)
    (gs : List (OpFull → OpFull)) (Q : KVState → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ isKv api γ rf ∗
      ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAt sl gs ∗
      ⌜¬ opDeletePanics key gs ∧ (opDeleteModel key gs).t = W64 3 ∧
        (deleteWireOf (opDeleteModel key gs)).base.rangeEnd ≠ [W8 0]⌝ ∗
      writeUpd rf (kvOpAu1 γ (.deleteRange (deleteWireOf (opDeleteModel key gs))) Q) }}
    (App (App (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!!
        go!"Delete")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #sl))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      deleteCallOut (delStOk (deleteWireOf (opDeleteModel key gs)) Q) resp err }}

end spec

end EtcdGrove
end Perennial
