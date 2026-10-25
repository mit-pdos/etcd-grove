/-
A context's `Value(requestid.requestIDKey{})` (`requestid.FromContext` reads the request ID stored
with `requestid.NewContext` via `context.WithValue`, PR etcd#21401): the trust boundary.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.requestid.Defs
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.TxnRange
public import Perennial.Proof.context

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : context.Assumptions]

/-- `ctx.Value(key)` on a context (`mvcc.txnCtx`, whose `Value` Perennial specifies only at
`&cancelCtxKey`) for a key of type `requestid.requestIDKey` (an empty struct, comparable):
returns `nil` or a `uint64` (the key's type is `requestid`'s unexported `requestIDKey`, which only
`requestid.NewContext` stores, with a `uint64`; `requestid.FromContext` type-asserts `val.(uint64)`
when `val != nil`). -/
abbrev context.ValueRequestID.spec : Prop :=
  ∀ (ctx key : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
  key.ty = go_etcd_io.etcd.server.v3.etcdserver.requestid.requestIDKey.ty →
  {{ mvcc.txnCtx ctx cd }}
    (App (Val #(methods ctx.ty go!"Value" ctx.v)) (Val #(GoInterface.ok key)))
  {{ (v : GoInterface), RET #v;
      ⌜v = GoInterface.nil ∨ ∃ id : w64, v = interface.mkOk go.uint64 #id⌝ }}

end spec

end EtcdGrove
end Perennial
