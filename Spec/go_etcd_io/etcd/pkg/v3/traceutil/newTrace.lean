/-
## `newTrace(op, lg, fields...)` (internal)

**Users.** `EnsureTrace`. **Proof sketch.** Allocates the struct with `time.Now()` (Perennial's
`time`); keeps the fields slice and the logger. **Changes.** From `specs-ref`'s `newTrace.lean`.
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Api

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

/-- A fresh non-empty trace keeping `fields` and the logger (nil or zap's). -/
def newTrace.spec : Prop :=
  ∀ (op : GoString) (lg : Loc) (fields : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil ∗ fieldsOwn fields ∗ (⌜lg = null⌝ ∨ Zap.isLogger lg) }}
    (App (App (App (Val (@! go_etcd_io.etcd.pkg.v3.traceutil.newTrace)) (Val #op)) (Val #lg))
      (Val #fields))
  {{ (t : Loc), RET #t; traceOwn t ∗ traceEmpty t false }}

end spec
end TraceUtil
end EtcdGrove
end Perennial
