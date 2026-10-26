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
`kv.Do` of `OpPut(key, val, opts...)` (`opts`: the models of the Go options `opts...` (`WithPrevKV()`, ...), one transformer of the operation each, `optsAt`
ties the slice `opts_sl` of their closures to them; `[]` for none), options that do not make `OpPut` panic nor change
the operation's type, a put with no lease (etcd's `Put` spec covers no other),
with the caller's atomic update of `γ`'s state by the put the server
reads (`putWireOf`; `kvOpStep`), persistent if the client's writes may be delivered more than once
(`□?dup`); the error through `ContextError`:
`nil` and the reply's message `m` with `Q σ` for the state `σ` the update fired at, the reply's
revision `σ`'s next and its previous key-value the key's record in `σ`'s current store if asked,
`σ` and the state after the put well-formed small logs' states (`kvLogOk`, D47); or a client error (`kvErr`) and no reply. -/
abbrev kv.Put.spec : Prop :=
  ∀ (kv : Loc) (γ : KVNames) (dup : Bool) (ctx : GoInterfaceOk)
    (ctx_desc : context.ContextDesc (IProp GF)) (key val : GoString) (opts_sl : GoSlice)
    (opts : List (OpFull → OpFull)) (Q : KVState → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ isKv kv γ dup ∗
      ctxOk ctx ctx_desc ∗ ctxErrClient ctx ctx_desc ∗ optsAt opts_sl opts ∗
      ⌜¬ (opPutModel key val opts).putPanics ∧ (opPutModel key val opts).t = W64 2 ∧
        (putWireOf (opPutModel key val opts)).leaseID = W64 0⌝ ∗
      □?dup (AU <{ ∃∃ (σ : KVState), etcdKV γ σ }> @ (⊤ \ ↑srvRaftN) \ ↑kvN, ∅
        <{ etcdKV γ (kvOpStep (.put (putWireOf (opPutModel key val opts))) σ), COMM Q σ }>) }}
    (App (App (App (App (Val (kv @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!!
        go!"Put")) (Val #(GoInterface.ok ctx))) (Val #key)) (Val #val)) (Val #opts_sl))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ (m : PutRespM) (σ : KVState), putRespMsg resp m ∗ Q σ ∗
        ⌜m.hdr.revision = W64 ((σ.rev + 1 : Nat) : Int) ∧
          m.prev = (if (putWireOf (opPutModel key val opts)).base.prevKV then
            (σ.store.lookup (putWireOf (opPutModel key val opts)).key).map (KVRec.toKv (putWireOf (opPutModel key val opts)).key) else none) ∧
          σ.rev + 4 < 2 ^ 63 ∧ kvLogOk σ ∧
          kvLogOk (kvOpStep (.put (putWireOf (opPutModel key val opts))) σ)⌝) ∨
      (⌜err ≠ GoInterface.nil ∧ resp = null⌝ ∗ kvErr err) }}

end spec

end EtcdGrove
end Perennial
