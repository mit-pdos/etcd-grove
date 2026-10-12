/-
`(*traceutil.Trace).StepWithFunction`: the trust boundary (`pkg/v3/traceutil` is names-only).
Lean-first.

`t.StepWithFunction(f, msg, fields...)` disables the trace's steps, calls `f()`, enables them
and records one step (`trace.go`): for a trace not nil, it is `f()` as far as the caller sees,
a panic of `f` included (no `defer`: the panic propagates).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Base
public import GeneratedProof.go_etcd_io.etcd.pkg.v3.traceutil
public import Perennial.Proof.context

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.pkg.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `t.StepWithFunction(f, msg, fields...)` (a trace not nil) runs `f()`: whatever `f()`
ends with (`#()`, or a panic), it ends with. -/
abbrev traceutil.Trace.StepWithFunction.spec : Prop :=
  ∀ (t : Loc) (f : GoFunc) (msg : GoString) (fields : GoSlice) (Q : val → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil ∗ ⌜t ≠ null⌝ ∗
      WP (App (Val #f) (Val #())) {{ Q }} }}
    (App (App (App (Val (t @!! go.GoType.PointerType traceutil.Trace.ty @!! go!"StepWithFunction"))
      (Val #f)) (Val #msg)) (Val #fields))
  {{ (r : val), RET r; Q r }}

end spec

end EtcdGrove
end Perennial
