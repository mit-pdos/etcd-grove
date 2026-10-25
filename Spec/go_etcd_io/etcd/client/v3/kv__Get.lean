/-
`(*clientv3.kv).Get(ctx, key, opts...)` (`client/v3/kv.go`, translated for unit C1, the client meets the server). Lean-first (no Rocq counterpart).
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

/-- `kv.Get(ctx, key, opts...)` on a `*kv` of etcd's KV `γ` (`isKv`, D43): `OpGet(key, opts...)`
(options that do not panic, keep the range type, read at the latest revision, and may need a
resource `R`, given back: `optsAtRes`; any sort option, checked against `etcdserverpb`'s
enumerations, `sortNamesOk`), then `kv.Do`, with the caller's persistent atomic read of `γ`'s
state (a read may be answered by any member, and again) or, `Q` trivial, none; the error through
`ContextError`: `rangeCallOut` of `rangeStOk`, a state `σ` (the read update's, `□ Q σ`, if
linearizable) whose selection, count and revision are the reply's. -/
abbrev kv.Get.spec : Prop :=
  ∀ (api : Loc) (γ : KVNames) (dup : Bool) (ci : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (key : GoString) (sl : GoSlice)
    (gs : List (OpFull → OpFull)) (R : IProp GF) (Q : KVState → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ isKv api γ dup ∗
      ctxOk ci cd ∗ ctxErrClient ci cd ∗ optsAtRes sl gs R ∗ R ∗
      sortNamesIf (opGetModel key gs).base.sortSet ∗
      ⌜¬ opGetPanics gs ∧ (opGetModel key gs).t = W64 1 ∧
        (rangeWireOf (opGetModel key gs)).base.rev = W64 0⌝ ∗
      □ (⌜Q = fun _ => iprop(True)⌝ ∨ (⌜(rangeWireOf (opGetModel key gs)).base.serializable = false⌝ ∗
        AU <{ ∃∃ (σ : KVState), etcdKV γ σ }> @ (⊤ \ ↑srvRaftN) \ ↑kvN, ∅
        <{ etcdKV γ σ, COMM □ Q σ }>)) }}
    (App (App (App (Val (api @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!!
        go!"Get")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #sl))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      R ∗ rangeCallOut (rangeStOk (rangeWireOf (opGetModel key gs)) Q) resp err }}

end spec

end EtcdGrove
end Perennial
