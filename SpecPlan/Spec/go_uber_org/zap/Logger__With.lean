/-
`(*zap.Logger).With`: the trust boundary.
Users: the server's components (a logger with fixed fields).
Proof sketch: none (trust boundary, `Api.lean`'s header).
Changes: new (verify round, A1-completeness S1: a specced caller uses it and no spec existed).
Margin: the fields are not modelled.
-/
module

public import SpecPlan.Spec.go_uber_org.zap.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Zap

open Iris Iris.BI go_uber_org

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `l.With(fields...)`: a logger (`isLogger`). -/
def Logger.With.spec : Prop :=
  ∀ (l : Loc) (fields : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap ∗ isLogger l }}
    (App (Val (l @!! go.GoType.PointerType zap.Logger.ty @!! go!"With")) (Val #fields))
  {{ (l' : Loc), RET #l'; isLogger l' }}

end spec

end Zap
end EtcdGrove
end Perennial
