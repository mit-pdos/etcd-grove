/-
`time.Time.Format("20060102.150405.999999")`, the layout of the WAL's `cleanupWAL` (S/wal.go, the
broken directory's name, `fmt.Sprintf("%s.broken.%v", w.dir, time.Now().Format(...))`). **A
trust-boundary axiom** since 2026-11-22 (`Proof/time/Time__FormatBroken.lean`, the user's approval;
review `notes/axiom-review/time-format-broken.md`); until then a hypothesis of `cleanupWAL`'s proof
(ledger 2026-11-14, "`time.Time.Format.spec` ... its result unconstrained", and 2026-11-22). Perennial's
`time` has no `Format` (names-only), and the general trust-boundary `time.Time.Format.spec`
(`Spec/time/Time__Format.lean`) says nothing of the result, so the target of the cleanup's rename
could hold `/` (a path under another directory), which no `os.Rename` spec covers.

What the WAL uses of the result, and all this spec claims: no byte `/` and no NUL, so that
`w.dir + ".broken." + s` is a name in the WAL's directory (`brokenName_nameOk`, `BrokenName.lean`); no
panic; no other effect (the frame). Go's output for this layout (`time/format.go`, `appendFormat`) is
much more specific, and implies it: `2006` is `stdLongYear`, `appendInt(b, year, 4)` (at least four
digits, a `-` before a negative year); `01`, `02`, `15`, `04`, `05` are two-digit fields
(`appendInt(b, x, 2)`); `.999999` is `stdFracSecond9` of six digits, `appendNano` with trailing zeros
dropped and the `.` too when all are; the layout's literal `.`s are copied. Every byte is a digit, `.`
or `-`. The length is not claimed (unbounded years; `fsExt`'s `rename(2)` model admits any valid name,
a name past 255 bytes among its failures with no effect). Lean-first.
-/
module

public import Perennial.Proof.time

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

/-- **A timestamp the WAL can put in a name**: no `/` (byte 47) and no NUL (byte 0). -/
def timeStampOk (s : GoString) : Prop := (47 : w8) ∉ s ∧ (0 : w8) ∉ s

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : time.Assumptions]

/-- **`t.Format("20060102.150405.999999")`**: a string with no `/` and no NUL (see the file
header). -/
abbrev time.Time.Format.specBroken : Prop :=
  ∀ (t : time.Time),
  {{ (True : IProp GF) }}
    (App (Val #(methods time.Time.ty go!"Format" #t)) (Val #(go!"20060102.150405.999999")))
  {{ (s : GoString), RET #s; ⌜timeStampOk s⌝ }}

end spec

end EtcdGrove
end Perennial
