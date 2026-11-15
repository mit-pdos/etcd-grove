/-
`time.Time.Format("20060102.150405.999999")`, the layout of the WAL's `cleanupWAL` (S/wal.go, the
broken directory's name, `fmt.Sprintf("%s.broken.%v", w.dir, time.Now().Format(...))`): **a hypothesis**
of `cleanupWAL`'s proof, not proved here and not an axiom; pending the user (plan §10; ledger
2026-11-14, "`time.Time.Format.spec` ... its result unconstrained"). The trust-boundary axiom
`time.Time.Format.spec` (`Spec/time/Time__Format.lean`) says nothing of the result, so the target of
the cleanup's rename could hold `/` (a path under another directory) and no `os.Rename` spec covers it.

Go's output for this layout (`time/format.go`, `appendFormat`): `2006` is `stdLongYear`,
`appendInt(b, year, 4)` (at least four digits, a `-` before a negative year); `01`, `02`, `15`, `04`,
`05` are two-digit fields (`appendInt(b, x, 2)`); `.999999` is `stdFracSecond9` of six digits,
`appendNano` with trailing zeros dropped and the `.` too when all are. Every byte is a digit, `.` or
`-`. The length is at most 22 for a year in `[0, 9999]` (`yyyymmdd.hhmmss.ffffff`), longer for other
years, which a `time.Time` can hold: the statement below claims no bound (the name's length does not
matter to the proof: `fsExt`'s `rename(2)` model admits any valid name, failing or not; a name past
255 bytes, whose `rename(2)` Linux fails with `ENAMETOOLONG`, is among the model's failures with no
effect). Lean-first.
-/
module

public import Perennial.Proof.time

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

/-- The bytes `Time.Format` writes for a layout of numeric fields: the digits, `.` and `-`. -/
def timeStampChars : GoString := go!"0123456789.-"

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : time.Assumptions]

/-- **`t.Format("20060102.150405.999999")`**: a string of digits, `.` and `-` only (see the file
header). -/
abbrev time.Time.Format.specBroken : Prop :=
  ∀ (t : time.Time),
  {{ (True : IProp GF) }}
    (App (Val #(methods time.Time.ty go!"Format" #t)) (Val #(go!"20060102.150405.999999")))
  {{ (s : GoString), RET #s; ⌜∀ c ∈ s, c ∈ timeStampChars⌝ }}

end spec

end EtcdGrove
end Perennial
