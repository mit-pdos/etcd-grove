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

**Soundness rests on the `Location` being read-only.** `Format` reads `*t.loc` (`Location.lookup`, the
zone and transition tables, to compute the calendar fields). In Go, a write to that `Location` racing
with `Format` tears it (a `zone` slice from one value, a `tx` slice from another) and `Format` panics,
`index out of range` in `Location.lookup` (`zoneinfo.go:200`): the review's `TestRacyLocation` (a
`Location` of the program's own, `time.Date(..., loc)`) and `TestRacyLocal` (`*time.Local = ...`,
`time.Unix`'s `Time`), `/shared/tmp/coord-03/review-timefmt/` (copied into
`notes/axiom-review/time-format-broken.md`). Until 2026-11-22 the precondition was `True`, which held only
because no model program could get a `Time` whose `Location` it can write (no spec of `In`, `Date`,
`FixedZone`, `LoadLocation`); now the precondition says so: `t.loc` is `nil` (`UTC`, `&utcLoc`) or the
value `l` of the global `time.Local` (`&localLoc`), and `globalAddr time.Local ↦□ l` (from `time`'s
`isPkgInit`, `Perennial/Proof/time/Base.lean`, `isInit`). `time`'s initializer (`time.initialize'.wp_proof`)
makes `Local` (and `UTC`) read-only and discards the points-to of `localLoc` and `utcLoc`, so no program
can write the `Location` `Format` reads. `time.Now()`'s `Time` meets it (`time.Now.specLoc`,
`Spec/time/NowLoc.lean`). (A future spec giving a program the points-to of `localLoc` or `utcLoc`, or a
writable `Local`, would make this axiom unsound; ledger 2026-11-22.)
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

/-- **`t.Format("20060102.150405.999999")`** of a `Time` whose location is `nil` (UTC) or the value `l`
of the read-only global `time.Local`: a string with no `/` and no NUL (see the file header). -/
abbrev time.Time.Format.specBroken : Prop :=
  ∀ (t : time.Time) (l : Loc),
  {{ (globalAddr time.Local ↦□ l : IProp GF) ∗ ⌜t.loc' = Loc.null ∨ t.loc' = l⌝ }}
    (App (Val #(methods time.Time.ty go!"Format" #t)) (Val #(go!"20060102.150405.999999")))
  {{ (s : GoString), RET #s; ⌜timeStampOk s⌝ }}

end spec

end EtcdGrove
end Perennial
