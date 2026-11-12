/-
## `(*Trace).updateFieldIfExist(f)` (internal)

**Users.** `AddField`. **Proof sketch.** A loop over the fields, a store on a match.
**Changes.** From `specs-ref`'s `Trace__updateFieldIfExist.lean`.
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

/-- Updates the field of `f`'s key if there is one; whether it did. -/
def Trace.updateFieldIfExist.spec : Prop :=
  ∀ (t : Loc) (f : go_etcd_io.etcd.pkg.v3.traceutil.Field),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil ∗ traceOwn t ∗ ⌜fieldsFmt [f]⌝ }}
    (App (Val (t @!! go.GoType.PointerType go_etcd_io.etcd.pkg.v3.traceutil.Trace.ty @!! go!"updateFieldIfExist")) (Val #f))
  {{ (b : Bool), RET #b; traceOwn t }}

end spec
end TraceUtil
end EtcdGrove
end Perennial
