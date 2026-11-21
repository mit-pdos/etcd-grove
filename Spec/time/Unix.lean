/-
`time.Unix(sec, nsec)`, of Go's `time` package: returns some `Time`. `client/v3`'s package
initializer calls it (`watch.go`: `zeroTime = time.Unix(0, 0)`; item 8, 2026-10-17). Proved
(`Proof/time/Unix.lean`) over Perennial's translation of Go's (2026-11-20; until then a
trust-boundary axiom, with no premise). It reads the package variable `time.Local`, so it needs
`time`'s `isPkgInit` (the initializer that calls it has it).
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
  {{ isPkgInit (PROP := IProp GF) pkg_id.time }}
    (App (App (Val (@! time.Unix)) (Val #sec)) (Val #nsec))
  {{ (t : time.Time), RET #t; True }}

end spec

end EtcdGrove
end Perennial
