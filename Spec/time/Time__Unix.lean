/-
`time.Time.Unix`, of Go's `time` package: returns some `int64` (the seconds since the epoch;
unmodelled). The compaction job's deferred `dbCompactionLast.Set(float64(time.Now().Unix()))` calls
it (2026-10-13, unit 5c). Proved (`Proof/time/Time__Unix.lean`) over Perennial's translation of Go's
(2026-11-20; until then a trust-boundary axiom).
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

/-- `t.Unix()`: some `int64`. -/
abbrev time.Time.Unix.spec : Prop :=
  ∀ t : time.Time,
  {{ (True : IProp GF) }}
    (App (Val #(methods time.Time.ty go!"Unix" #t)) (Val #()))
  {{ (n : w64), RET #n; True }}

end spec

end EtcdGrove
end Perennial
