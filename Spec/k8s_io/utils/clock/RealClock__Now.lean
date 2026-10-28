/-
`clock.RealClock.Now()` (`k8s.io/utils/clock`, names-only here: the trust boundary; it is
`time.Now()`). Lean-first; for client-go's delaying queue.
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

/-- `RealClock{}.Now()`: some time. -/
abbrev clock.RealClock.Now.spec : Prop :=
  ∀ (c : k8s_io.utils.clock.RealClock),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.clock }}
    (App (Val (c @!! k8s_io.utils.clock.RealClock.ty @!! go!"Now")) (Val #()))
  {{ (t : time.Time), RET #t; True }}

end spec

end EtcdGrove
end Perennial
