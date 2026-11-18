/-
`time.Unix(sec, nsec)`, of Go's `time` package (not translated in Perennial's `time`: no body, so
the call cannot be stepped): returns some `Time`. `client/v3`'s package initializer calls it
(`watch.go`: `zeroTime = time.Unix(0, 0)`; item 8, 2026-10-17). A trust-boundary axiom, true of
Go's `time.Unix` (it never panics).
-/
module

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
variable [package_sem : time.Assumptions]

/-- `time.Unix(sec, nsec)`: some `Time`. -/
abbrev time.Unix.spec : Prop :=
  ∀ sec nsec : w64,
  {{ (True : IProp GF) }}
    (App (App (Val (@! time.Unix)) (Val #sec)) (Val #nsec))
  {{ (t : time.Time), RET #t; True }}

end spec

end EtcdGrove
end Perennial
