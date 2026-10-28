/-
`(*Trace).Step(msg, fields...)` (`k8s.io/utils/trace`, names-only): records a step for the trace's
`LogIfLong`. **A named hypothesis, boundary pending approval** (one of the reflector's `list`
callees; phase 4 of `notes/k8s-daemonset-plan.md`, fifth round): `?` in
`etc/link-lean-first-k8scache.txt`. Stated as the package's other boundary specs (`New`,
`LogIfLong`): it returns.
-/
module

public import GeneratedProof.k8s_io.utils.trace

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.utils.trace.Assumptions]

/-- `t.Step(msg, fields)`: returns. -/
abbrev trace.Trace.Step.spec : Prop :=
  ∀ (t : Loc) (msg : GoString) (fields : GoSlice),
  {{ (True : IProp GF) }}
    (App (App (Val (t @!! go.GoType.PointerType k8s_io.utils.trace.Trace.ty @!! go!"Step"))
      (Val #msg)) (Val #fields))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
