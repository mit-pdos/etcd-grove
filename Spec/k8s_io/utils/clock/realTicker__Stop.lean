/-
`(*clock.realTicker).Stop()` (`k8s.io/utils/clock`, names-only here: the trust boundary; it is
`r.ticker.Stop()`). Lean-first.
-/
module

public import Spec.k8s_io.utils.clock.RealClock__NewTicker

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `r.Stop()`: returns. -/
abbrev clock.realTicker.Stop.spec : Prop :=
  ∀ (p : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.clock ∗ clock.realTickerOk p }}
    (App (Val (p @!! go.GoType.PointerType k8s_io.utils.clock.realTicker.ty @!! go!"Stop")) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
