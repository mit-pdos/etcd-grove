/-
## `traceutil.Get(ctx)`

**Users.** `EtcdServer.doSerialize` (`v3_server.go:1036`), `txn.rangeLocked`/`txn.put`/`txn.txn`
helpers (`txn/range.go:60`, `put.go:49`, `txn.go:136`), `EnsureTrace`. Snippet: `examples/specreq/pkgleaves/trace.go`
(`ReqRequestTrace`: the trace the caller made is found again).

**Proof sketch.** `ctx.Value(TraceKey{})` (`ctxTraceIs`: the trace `o`), the type assertion
(comma-ok: no panic), the nil check; none: `TODO()`.

**Changes.** From `specs-ref`'s `Get.lean`; the empty case gives `traceEmpty t true`.

**Margin.** None.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.pkg.v3.traceutil.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace TraceUtil

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.traceutil.Assumptions]

/-- **The context's trace** (whose owner holds it), or a fresh empty one, the caller's. -/
def Get.spec : Prop :=
  ∀ (ctx : GoInterface) (o : Option Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil ∗ ctxTraceIs ctx o }}
    (App (Val (@! go_etcd_io.etcd.pkg.v3.traceutil.Get)) (Val #ctx))
  {{ (t : Loc), RET #t;
      match o with
      | some t' => iprop(⌜t = t'⌝)
      | none => iprop(traceOwn t ∗ traceEmpty t true) }}

end spec
end TraceUtil
end EtcdGrove
end Perennial
