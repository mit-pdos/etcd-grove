/-
`(*zap.Logger).Named`: the trust boundary.
Users: `newClient` (`client.go:401`: the default logger named), the server's components.
Proof sketch: none (trust boundary, `Api.lean`'s header).
Changes: new (verify round, A1-completeness S1: a specced caller uses it and no spec existed).
Margin: the name is not modelled.
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

/-- `l.Named(s)`: a logger (`isLogger`: a derivation of one of zap's). -/
def Logger.Named.spec : Prop :=
  ∀ (l : Loc) (s : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap ∗ isLogger l }}
    (App (Val (l @!! go.GoType.PointerType zap.Logger.ty @!! go!"Named")) (Val #s))
  {{ (l' : Loc), RET #l'; isLogger l' }}

end spec

end Zap
end EtcdGrove
end Perennial
