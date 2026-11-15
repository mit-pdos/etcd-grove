/-
## `(*Trace).IsEmpty()`

**Users.** `EnsureTrace`. **Proof sketch.** A load of `isEmpty`, which `traceEmpty` holds
read-only for good: no ownership of the trace is needed (its owner may be stepping it meanwhile:
the field is never written after creation).

**Changes.** From `specs-ref`'s `Trace__IsEmpty.lean` (`ownTrace t e`): only the persistent
`traceEmpty`. **Margin.** None.
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

/-- **Whether the trace is empty**: its `traceEmpty` flag. -/
def Trace.IsEmpty.spec : Prop :=
  ∀ (t : Loc) (e : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil ∗ traceEmpty t e }}
    (App (Val (t @!! go.GoType.PointerType go_etcd_io.etcd.pkg.v3.traceutil.Trace.ty @!! go!"IsEmpty")) (Val #()))
  {{ RET #e; True }}

end spec
end TraceUtil
end EtcdGrove
end Perennial
