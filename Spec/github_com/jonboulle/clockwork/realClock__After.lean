/-
`(*realClock).After(d)` (`clockwork.go`: `time.After(d)`). Lean-first.
-/
module

public import Proof.github_com.jonboulle.clockwork.Defs

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

/-- `rc.After(d)`: for a persistent `P` and a bound `clockLb realClock n` the caller holds, the real
clock's reading `T ≥ n` at the call, a stamp of `P` at `T`, and a channel whose values come only once
the clock has reached `T + d` (`clockwork.clockOk`'s `After`). -/
abbrev clockwork.realClock.After.spec : Prop :=
  ∀ (rc : Loc) (d : time.Duration) (P : IProp GF) (n : Int),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.jonboulle.clockwork ∗ □ P ∗
        clockwork.clockLb clockwork.realClock n }}
      (App (Val (rc @!! go.GoType.PointerType github_com.jonboulle.clockwork.realClock.ty @!! go!"After"))
        (Val #d))
    {{ (ch : Loc) (γ : ChanNames), RET #ch; ∃ T : Int, ⌜n ≤ T⌝ ∗
        clockwork.stampAt clockwork.realClock iprop(□ P) T ∗
        isChanBag γ ch (V := time.Time) (fun _ => clockwork.clockLb clockwork.realClock (T + sint.Z d)) }}

end spec

end EtcdGrove
end Perennial
