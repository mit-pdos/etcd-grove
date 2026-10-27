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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `kv.Delete(ctx, key, opts...)` on a `*kv` of etcd's KV `γ` (`isKv`, D44): `kv.Do` of
`OpDelete(key, opts...)` (`opts`: the models of the Go options `opts...` (`WithPrevKV()`, ...), one transformer of the operation each, `optsAt`
ties the slice `opts_sl` of their closures to them; `[]` for none), options that do not make `OpDelete` panic nor change the
operation's type, a delete whose range end is not `[0]` (etcd's `DeleteRange` spec
covers no other: `WithFromKey`'s), with the caller's atomic update of
`γ`'s state by the delete the server reads (`deleteWireOf`; `kvOpStep`), persistent if the client's
writes may be delivered more than once (`□?dup`); the error through `ContextError`: `nil` and the reply's message `m` with
`Q σ` for the state `σ` the update fired at, the reply's count, previous key-values and revision as
`σ`'s, `σ` and the state after the delete well-formed small logs' states (`kvLogOk`, D48); or a client error (`kvErr`) and no
reply. -/
abbrev kv.Delete.spec : Prop :=
  ∀ (kv : Loc) (γ : KVNames) (dup : Bool) (ctx : GoInterfaceOk)
    (ctx_desc : context.ContextDesc (IProp GF)) (key : GoString) (opts_sl : GoSlice)
    (opts : List (OpFull → OpFull)) (Q : KVState → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ isKv kv γ dup ∗
      ctxOk ctx ctx_desc ∗ ctxErrClient ctx ctx_desc ∗ optsAt opts_sl opts ∗
      ⌜¬ opDeletePanics key opts ∧ (opDeleteModel key opts).t = W64 3 ∧
        (deleteWireOf (opDeleteModel key opts)).base.rangeEnd ≠ [W8 0]⌝ ∗
      □?dup (AU <{ ∃∃ (σ : KVState), etcdKV γ σ }> @ (⊤ \ ↑srvRaftN) \ ↑kvN, ∅
        <{ etcdKV γ (kvOpStep (.deleteRange (deleteWireOf (opDeleteModel key opts))) σ), COMM Q σ }>) }}
    (App (App (App (Val (kv @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!!
        go!"Delete")) (Val #(GoInterface.ok ctx))) (Val #key)) (Val #opts_sl))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ (m : DelRespM) (σ : KVState), delRespMsg resp m ∗ Q σ ∗
        ⌜m.deleted = W64 ((rangeIn σ.kvs (deleteWireOf (opDeleteModel key opts))).length : Int) ∧
          m.prevs = (if (deleteWireOf (opDeleteModel key opts)).base.prevKV then rangeIn σ.kvs (deleteWireOf (opDeleteModel key opts)) else []) ∧
          m.hdr.revision = W64 ((kvOpStep (.deleteRange (deleteWireOf (opDeleteModel key opts))) σ).rev : Int) ∧ σ.rev + 4 < 2 ^ 63 ∧
          kvLogOk σ ∧ kvLogOk (kvOpStep (.deleteRange (deleteWireOf (opDeleteModel key opts))) σ)⌝) ∨
      (⌜err ≠ GoInterface.nil ∧ resp = null⌝ ∗ kvErr err) }}

end spec

end EtcdGrove
end Perennial
