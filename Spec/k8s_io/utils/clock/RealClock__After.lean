/-
`clock.RealClock.After(d)` (`k8s.io/utils/clock`: `time.After(d)`, translated with its body). The
reflector's `watch` waits on it to back off, the compactor's loop between compactions. Stated as
Perennial's `time.After.spec_pkgInit` gives: a channel some goroutine sends a time on (a `isChanBag`
with no resource). Proved in `Proof/k8s_io/utils/clock/RealClock__After.lean`.
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

/-- `RealClock{}.After(d)`: a channel some time is sent on. -/
abbrev clock.RealClock.After.spec : Prop :=
  ∀ (c : k8s_io.utils.clock.RealClock) (d : time.Duration),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.clock }}
    (App (Val (c @!! k8s_io.utils.clock.RealClock.ty @!! go!"After")) (Val #d))
  {{ (ch : Loc) (γ : ChanNames), RET #ch; isChanBag (V := time.Time) γ ch (fun _ => iprop(True)) }}

end spec

end EtcdGrove
end Perennial
