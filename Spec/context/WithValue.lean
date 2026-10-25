/-
`context.WithValue`: the trust boundary (Perennial translates `context` without `WithValue`'s body). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Base
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.TxnRange
public import Perennial.Proof.context
public import Proof.go_etcd_io.etcd.pkg.v3.traceutil.Defs
public import Code.go_etcd_io.etcd.client.v3

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- What a context's `Value(channelKeyContextKey{})` may return, for its channel key `o`
(`client/v3/channel_key.go`, PR #21765). -/
def clientv3.channelKeyValIs (v : GoInterface) : Option GoString → Prop
  | some k => v = interface.mkOk go.string #k
  | none => v = GoInterface.nil ∨ ∃ ii : GoInterfaceOk, v = GoInterface.ok ii ∧ ii.ty ≠ go.string

/-- The key `channelKeyContextKey{}`, as an `any`. -/
abbrev clientv3.channelKeyVal : GoInterface :=
  interface.mkOk go_etcd_io.etcd.client.v3.channelKeyContextKey.ty
    #(zero_val go_etcd_io.etcd.client.v3.channelKeyContextKey)

/-- **The context `ctx` carries the channel key `o`** (persistent; PR #21765): if `ctx = nil`,
`o = none`; if `ctx = ok c`, its `Value(channelKeyContextKey{})` returns `o` (`channelKeyValIs`). -/
def clientv3.ctxChannelKeyIs (ctx : GoInterface) (o : Option GoString) : IProp GF :=
  match ctx with
  | .nil => iprop(⌜o = none⌝)
  | .ok c => iprop(□ ∀ Φ : val → IProp GF,
      ▷ (∀ v : GoInterface, ⌜clientv3.channelKeyValIs v o⌝ -∗ Φ #v) -∗
        WP (App (Val #(methods c.ty go!"Value" c.v)) (Val #clientv3.channelKeyVal)) {{ Φ }})

instance clientv3.ctxChannelKeyIs_persistent (ctx : GoInterface) (o : Option GoString) :
    Persistent (clientv3.ctxChannelKeyIs (GF := GF) ctx o) := by
  unfold clientv3.ctxChannelKeyIs
  cases ctx <;> infer_instance

/-- The channel key selected by `channelKeyForRequest(ctx)` for a context carrying `o`:
`"default"` when `o` is `none`, `some ""`, or `some "default"`, and `k` when `o = some k`
for any other `k`. -/
def clientv3.reqChannelKey (o : Option GoString) : GoString :=
  let k := o.getD go!""
  if k = go!"" ∨ k = go!"default" then go!"default" else k

@[simp]
theorem clientv3.reqChannelKey_none : clientv3.reqChannelKey none = go!"default" := by
  simp [clientv3.reqChannelKey]

@[simp]
theorem clientv3.reqChannelKey_empty : clientv3.reqChannelKey (some go!"") = go!"default" := by
  simp [clientv3.reqChannelKey]

@[simp]
theorem clientv3.reqChannelKey_default :
    clientv3.reqChannelKey (some go!"default") = go!"default" := by
  simp [clientv3.reqChannelKey]

theorem clientv3.reqChannelKey_other (k : GoString) (h1 : k ≠ go!"") (h2 : k ≠ go!"default") :
    clientv3.reqChannelKey (some k) = k := by
  simp [clientv3.reqChannelKey, h1, h2]

theorem clientv3.ctxChannelKeyIs_nil :
    ⊢ clientv3.ctxChannelKeyIs (GF := GF) GoInterface.nil none := by
  unfold clientv3.ctxChannelKeyIs
  ipureintro; rfl

theorem clientv3.ctxChannelKeyIs_todo [context.Assumptions] :
    ⊢ clientv3.ctxChannelKeyIs (GF := GF)
      (GoInterface.ok (interface.mk context.todoCtx.ty #(zero_val context.todoCtx))) none := by
  unfold clientv3.ctxChannelKeyIs
  imodintro
  iintro %Φ HΦ
  wp_method_call
  wp_auto
  wp_method_call
  wp_auto
  iapply HΦ
  ipureintro; left; rfl

theorem clientv3.ctxChannelKeyIs_background [context.Assumptions] :
    ⊢ clientv3.ctxChannelKeyIs (GF := GF)
      (GoInterface.ok (interface.mk context.backgroundCtx.ty #(zero_val context.backgroundCtx)))
      none := by
  unfold clientv3.ctxChannelKeyIs
  imodintro
  iintro %Φ HΦ
  wp_method_call
  wp_auto
  wp_method_call
  wp_auto
  iapply HΦ
  ipureintro; left; rfl

end defs

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : context.Assumptions]

/-- `context.WithValue(parent, key, v)`: a context, not nil (a `valueCtx` over `parent`), for a
key of the auth store's two parameter types (as the backend's `Authenticate` passes),
`traceutil.StartTimeKey` (2026-10-12: the server's `Put` and `Txn`) or `traceutil.TraceKey{}`
(2026-10-14, unit P1b: `traceutil.EnsureTrace`) or clientv3's `keepAliveCtxKey{}` (2026-10-18, item
1, the client lease: `lessor.KeepAlive`) or `channelKeyContextKey{}` (PR #21765:
`clientv3.WithChannelKey`); all empty structs,
comparable (`WithValue` panics on a nil or incomparable key). A `valueCtx`'s `Deadline`, `Done`
and `Err` are its parent's, so for any description of the parent (`mvcc.txnCtx`, at a
descriptor `cd`) the context is described by `cd` with other values; in particular (2026-10-12,
the request path's unit 2: `processInternalRaftRequestOnce` takes a `context.WithTimeout` of it,
which needs `isContext`), a context (`context.isContext`) gives a context. Its trace
(`traceutil.ctxTraceIs`, unit P1b): `v`'s for the key `TraceKey{}` (`valueCtx.Value` returns `v`
at an equal key), else its parent's (a key of another type is not equal to `TraceKey{}`, so
`Value(TraceKey{})` asks the parent); and similarly its channel key (`clientv3.ctxChannelKeyIs`,
PR #21765) is `some k` for `channelKeyContextKey{}` with string `k`, else its parent's. -/
abbrev context.WithValue.spec : Prop :=
  ∀ (parent key : GoInterfaceOk) (v : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗
      ⌜key.ty = go_etcd_io.etcd.server.v3.auth.AuthenticateParamIndex.ty ∨
        key.ty = go_etcd_io.etcd.server.v3.auth.AuthenticateParamSimpleTokenPrefix.ty ∨
        key.ty = go_etcd_io.etcd.pkg.v3.traceutil.StartTimeKey.ty ∨
        key = ⟨go_etcd_io.etcd.pkg.v3.traceutil.TraceKey.ty,
          #(zero_val go_etcd_io.etcd.pkg.v3.traceutil.TraceKey)⟩ ∨
        key.ty = go_etcd_io.etcd.client.v3.keepAliveCtxKey.ty ∨
        key = ⟨go_etcd_io.etcd.client.v3.channelKeyContextKey.ty,
          #(zero_val go_etcd_io.etcd.client.v3.channelKeyContextKey)⟩⌝ }}
    (App (App (App (Val (@! context.WithValue)) (Val #(GoInterface.ok parent)))
      (Val #(GoInterface.ok key))) (Val #v))
  {{ (c : GoInterface), RET #c; ⌜c ≠ GoInterface.nil⌝ ∗
      □ (∀ cd : context.ContextDesc (IProp GF), mvcc.txnCtx parent cd -∗
        ∃ (c' : GoInterfaceOk) (vs : GMap GoInterface GoInterface), ⌜c = GoInterface.ok c'⌝ ∗
          mvcc.txnCtx c' { cd with Values := vs }) ∗
      □ (∀ cd : context.ContextDesc (IProp GF), context.isContext parent cd -∗
        ∃ (c' : GoInterfaceOk) (vs : GMap GoInterface GoInterface), ⌜c = GoInterface.ok c'⌝ ∗
          context.isContext c' { cd with Values := vs }) ∗
      ∃ (c' : GoInterfaceOk) (vs : GMap GoInterface GoInterface), ⌜c = GoInterface.ok c'⌝ ∗
        □ (∀ cd : context.ContextDesc (IProp GF), mvcc.txnCtx parent cd -∗
          mvcc.txnCtx c' { cd with Values := vs }) ∗
        □ (∀ cd : context.ContextDesc (IProp GF), context.isContext parent cd -∗
          context.isContext c' { cd with Values := vs }) ∗
        □ (∀ t : Loc, ⌜key.ty = go_etcd_io.etcd.pkg.v3.traceutil.TraceKey.ty ∧ t ≠ null ∧
            v = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.pkg.v3.traceutil.Trace.ty) #t⌝ -∗
          traceutil.ctxTraceIs c' (some t)) ∗
        □ (∀ o : Option Loc, ⌜key.ty ≠ go_etcd_io.etcd.pkg.v3.traceutil.TraceKey.ty⌝ -∗
          traceutil.ctxTraceIs parent o -∗ traceutil.ctxTraceIs c' o) ∗
        □ (∀ k : GoString, ⌜key.ty = go_etcd_io.etcd.client.v3.channelKeyContextKey.ty ∧
            v = interface.mkOk go.string #k⌝ -∗
          clientv3.ctxChannelKeyIs (GoInterface.ok c') (some k)) ∗
        □ (∀ o : Option GoString, ⌜key.ty ≠ go_etcd_io.etcd.client.v3.channelKeyContextKey.ty⌝ -∗
          clientv3.ctxChannelKeyIs (GoInterface.ok parent) o -∗
          clientv3.ctxChannelKeyIs (GoInterface.ok c') o) }}

end spec

end EtcdGrove
end Perennial
