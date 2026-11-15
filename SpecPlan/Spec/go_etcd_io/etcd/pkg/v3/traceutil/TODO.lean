/-
## `traceutil.TODO()`

**Users.** mvcc's views and range deleter (`kv_view.go:31,40,47`, `kvstore.go:117`), the server's
lessor recovery (`server.go:1087`), `Get` of a context without a trace. Snippet: `examples/specreq/pkgleaves/trace.go`
(`ReqMvccTodoTrace`).

**Proof sketch.** Allocates `&Trace{isEmpty: true}`: its fields slices are `nil` (`fieldsOwn` of
the nil slice), `lg` nil; `traceEmpty` is the `isEmpty` field's discarded points-to.

**Changes.** From `specs-ref`'s `TODO.lean` (`ownTrace t true`): the emptiness split off as the
persistent `traceEmpty`.

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

/-- **A fresh empty trace**, the caller's. -/
def TODO.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil }}
    (App (Val (@! go_etcd_io.etcd.pkg.v3.traceutil.TODO)) (Val #()))
  {{ (t : Loc), RET #t; traceOwn t ∗ traceEmpty t true }}

end spec
end TraceUtil
end EtcdGrove
end Perennial
