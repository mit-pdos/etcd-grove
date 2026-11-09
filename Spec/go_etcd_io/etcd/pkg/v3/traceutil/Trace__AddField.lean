/-
## `(*Trace).AddField(fields...)`

**Users.** The request path (`v3_server.go:128,430`), `txn` (`put.go:67`, `txn.go:52,74`), the read
loop (`read.go:128,131`). Snippets: `trace.go` (`ReqRequestTrace`, `ReqReadLoopTrace`).

**Proof sketch.** For each field, `updateFieldIfExist` (a store into the trace's fields) or an
append of a copy: the slice is only read.

**Changes.** From `specs-ref`'s `Trace__AddField.lean`. **Margin.** None.
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

/-- **Adds (or updates) fields**, read from the slice; the trace kept. -/
def Trace.AddField.spec : Prop :=
  ∀ (t : Loc) (fields : GoSlice) (fs : List go_etcd_io.etcd.pkg.v3.traceutil.Field) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil ∗ traceOwn t ∗ fields ↦*{dq} fs ∗ ⌜fieldsFmt fs⌝ }}
    (App (Val (t @!! go.GoType.PointerType go_etcd_io.etcd.pkg.v3.traceutil.Trace.ty @!! go!"AddField")) (Val #fields))
  {{ RET #(); traceOwn t ∗ fields ↦*{dq} fs }}

end spec
end TraceUtil
end EtcdGrove
end Perennial
