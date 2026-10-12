/-
A context's `Value(traceutil.StartTimeKey{})` (`EtcdServer.raftRequest` reads the request's start
time the server's `Put`/`Txn` stored with `context.WithValue`): the trust boundary. Lean-first (no
Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseApply
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

/-- `ctx.Value(key)` on a context (`context.isContext`, whose `Value` Perennial specifies only at
`&cancelCtxKey`) for a key of type `traceutil.StartTimeKey` (an empty struct, comparable):
returns `nil` or a `time.Time` (the key's type is `traceutil`'s, which only etcd's request path
stores, with `time.Now()`; the caller type-asserts it with `, ok`). -/
abbrev context.ValueStartTime.spec : Prop :=
  ∀ (ctx key : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
  key.ty = go_etcd_io.etcd.pkg.v3.traceutil.StartTimeKey.ty →
  {{ context.isContext ctx cd }}
    (App (Val #(methods ctx.ty go!"Value" ctx.v)) (Val #(GoInterface.ok key)))
  {{ (v : GoInterface), RET #v;
      ⌜v = GoInterface.nil ∨ ∃ t : time.Time, v = interface.mkOk _root_.Perennial.time.Time.ty #t⌝ }}

end spec

end EtcdGrove
end Perennial
