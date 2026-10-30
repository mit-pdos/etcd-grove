/-
`clock.RealClock.Since(ts)` (`k8s.io/utils/clock`, names-only here: the trust boundary; it is
`time.Since(ts)`). Lean-first; for the controller expectations' `isExpired`.
**A named hypothesis, boundary pending approval** (phase 5 of `notes/k8s-daemonset-plan.md`).
-/
module

public import Proof.k8s_io.utils.clock.Init
public import Perennial.Proof.time

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

/-- `RealClock{}.Since(t)`: some duration (the clock is not modeled). -/
abbrev clock.RealClock.Since.spec : Prop :=
  ∀ (c : k8s_io.utils.clock.RealClock) (t : time.Time),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.clock }}
    (App (Val (c @!! k8s_io.utils.clock.RealClock.ty @!! go!"Since")) (Val #t))
  {{ (d : w64), RET #d; True }}

end spec

end EtcdGrove
end Perennial
