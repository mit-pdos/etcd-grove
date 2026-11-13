/-
`time.Time.Format`, of Go's `time` package (not translated in Perennial's `time`: no body, so the
call cannot be stepped): returns some string (the formatted time; unmodelled). The WAL's
`cleanupWAL` names the broken directory with `time.Now().Format("20060102.150405.999999")`
(wal.go:299; any name is safe for the proof). A trust-boundary axiom (`Proof/time/
Time__Format.lean`), true of Go's `Time.Format` (it never panics: `appendFormat` handles every
layout and every `Time`). WAL leaf specs, 2026-11-13; Lean-first.
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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : time.Assumptions]

/-- `t.Format(layout)`: some string. -/
abbrev time.Time.Format.spec : Prop :=
  ∀ (t : time.Time) (layout : GoString),
  {{ (True : IProp GF) }}
    (App (Val #(methods time.Time.ty go!"Format" #t)) (Val #layout))
  {{ (s : GoString), RET #s; True }}

end spec

end EtcdGrove
end Perennial
