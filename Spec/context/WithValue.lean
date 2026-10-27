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

open Iris Iris.BI 

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : context.Assumptions]

/-- `context.WithValue(parent, key, v)`: a context, not nil (a `valueCtx` over `parent`), for a
key of the auth store's two parameter types (as the backend's `Authenticate` passes),
`traceutil.StartTimeKey` (2026-10-12: the server's `Put` and `Txn`) or `traceutil.TraceKey{}`
(2026-10-14, unit P1b: `traceutil.EnsureTrace`) or clientv3's `keepAliveCtxKey{}` (2026-10-18, item
1, the client lease: `lessor.KeepAlive`); all empty structs,
comparable (`WithValue` panics on a nil or incomparable key). A `valueCtx`'s `Deadline`, `Done`
and `Err` are its parent's, so for any description of the parent (`mvcc.txnCtx`, at a
descriptor `cd`) the context is described by `cd` with other values; in particular (2026-10-12,
the request path's unit 2: `processInternalRaftRequestOnce` takes a `context.WithTimeout` of it,
which needs `isContext`), a context (`context.isContext`) gives a context. Its trace
(`traceutil.ctxTraceIs`, unit P1b): `v`'s for the key `TraceKey{}` (`valueCtx.Value` returns `v`
at an equal key), else its parent's (a key of another type is not equal to `TraceKey{}`, so
`Value(TraceKey{})` asks the parent); the two descriptions at the same values (a descriptor's
`Values` is read by no context predicate). -/
abbrev context.WithValue.spec : Prop :=
  ∀ (parent key : GoInterfaceOk) (v : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.context ∗
      ⌜key.ty = go_etcd_io.etcd.server.v3.auth.AuthenticateParamIndex.ty ∨
        key.ty = go_etcd_io.etcd.server.v3.auth.AuthenticateParamSimpleTokenPrefix.ty ∨
        key.ty = go_etcd_io.etcd.pkg.v3.traceutil.StartTimeKey.ty ∨
        key = ⟨go_etcd_io.etcd.pkg.v3.traceutil.TraceKey.ty,
          #(zero_val go_etcd_io.etcd.pkg.v3.traceutil.TraceKey)⟩ ∨
        key.ty = go_etcd_io.etcd.client.v3.keepAliveCtxKey.ty⌝ }}
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
          traceutil.ctxTraceIs parent o -∗ traceutil.ctxTraceIs c' o) }}

end spec

end EtcdGrove
end Perennial
