/-
**The `log` calls go-craq makes** (dsv-fix6; until then the statement premise `LogHyp`, H6 of
notes/dsv-craq.md). go-craq's node logs through a `*log.Logger` (`log.Default()`, its `Printf` and
`Println`: no body in Perennial's trusted `log` model), the coordinator and the store through the
package-level `log.Printf`/`log.Println` (bodies in the model: they do nothing, so their specs are
proved here, over the same argument condition). The three `*Logger` specs are trust-boundary axioms
(`Craq/LogAx.lean`); `LogSpecs` is the class the proofs take them in, made from the axioms by the
kit's statement proof (`examples/craqnet/TopLevelRobustness.lean`), not a premise.

**What `fmt` does with an operand** (Go's `fmt/print.go`): under every verb it calls `Format` of an
operand implementing `fmt.Formatter`; under `%#v` `GoString` of a `fmt.GoStringer`; under the other
verbs `Error()`/`String()` of an `error`/`fmt.Stringer`; else it prints by kind, dereferencing a
top-level pointer to a struct and visiting the struct's fields (calling the same methods of an
exported field's value, and of an interface field's dynamic value). The dsv-fix4 review
(`notes/axiom-review/dsv-fix4/log-logger.md`) refuted the old condition, which admitted any type
without `Error`/`String` (so one with a `Format` or `GoString`) and any `errAny` error. `argOk` admits
only the operands go-craq passes, each of a shape whose formatting calls no method but an error's
`Error()` and reads only memory the caller holds:
* `nil`;
* `fmt.ArgWf` (Perennial's: a predeclared basic type, or a named integer or string type without
  formatting methods);
* a `*store.Item` (`Version uint64, Committed bool, Value []byte, Key string`; no methods) whose
  `Key`, `Version`, `Value` and `Value`'s bytes are persistent (`%+v`/`%#v` print them all). Its
  `Committed`, a `bool` that the store writes under its own lock, is read without permission: a
  racy read of one byte observes some written value (Go's memory model) and cannot panic;
* a `*transport.NodeMeta` (`IsHead, IsTail bool; Prev, Next, Tail string`; no methods) with a
  fraction of its points-to, given back;
* an error with `models_lab.errPlain` (`Net/Proof/models_lab/ErrFmt.lean`): its `Error()` (a WP),
  no `Format`/`GoString`, and one of the net world's shapes with the memory `%#v` reads persistent.
-/
module

public import Perennial.Proof.log
public import Perennial.Proof.log.Printf
public import Perennial.Proof.fmt.Base
public import Net.Proof.models_lab.Errors
public import Net.Proof.models_lab.ErrFmt
public import Dsverify.Proof.github_com.despreston.go_craq.store.Base
public import Dsverify.Proof.github_com.despreston.go_craq.transport.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

namespace github_com.despreston.go_craq

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [store.Assumptions] [transport.Assumptions]

/-- A `log` operand go-craq passes (the file header): `nil`, `fmt.ArgWf`, a `*store.Item` with its
`Key`, `Version`, `Value` and bytes persistent, a `*transport.NodeMeta` with a fraction of its
points-to, or an `errPlain` error. -/
def argOk (v : GoInterface) : IProp GF :=
  iprop(⌜v = interface.nil⌝ ∨
    ⌜∃ ii, v = interface.ok ii ∧ fmt.ArgWf ii⌝ ∨
    (∃ (p : Loc) (k : GoString) (ver : w64) (sl : GoSlice) (x : GoString),
      ⌜v = interface.mkOk (go.GoType.PointerType store.Item.ty) #p⌝ ∗
      structFieldRef store.Item go!"Key" p ↦□ k ∗ structFieldRef store.Item go!"Version" p ↦□ ver ∗
      structFieldRef store.Item go!"Value" p ↦□ sl ∗ sl ↦*□ x) ∨
    (∃ (p : Loc) (dq : DFrac) (m : transport.NodeMeta),
      ⌜v = interface.mkOk (go.GoType.PointerType transport.NodeMeta.ty) #p⌝ ∗ p ↦{dq} m) ∨
    models_lab.errPlain v)

/-- Arguments `fmt` formats without a method are `argOk`. -/
theorem argOks_of_wf (xs : List GoInterface) (h : fmt.ArgsWf xs) :
    ⊢ [∗list] x ∈ xs, argOk (GF := GF) x := by
  induction xs with
  | nil => exact BI.BigSepL.bigSepL_nil_intro (P := iprop(emp))
  | cons a l ih =>
    have ha : ⊢ argOk (GF := GF) a := by
      unfold argOk
      cases a with
      | nil => ileft; ipureintro; rfl
      | ok ii => iright; ileft; ipureintro; exact ⟨ii, rfl, h ii List.mem_cons_self⟩
    have hl := ih (fun ii hi => h ii (List.mem_cons_of_mem _ hi))
    refine Entails.trans ?_ (BI.BigSepL.bigSepL_cons (Φ := fun _ x => argOk (GF := GF) x)).2
    iintro -
    isplitl []
    · iapply ha
    · iapply hl

end defs

/-- `l` is `log`'s standard logger (`std`, what `log.Default()` returns): opaque, no law, so a
proof has it only from `LogDefault.spec`. A `*Logger` made otherwise (`new(log.Logger)`, whose
`out` is nil) panics in `Printf`/`Println` (`notes/axiom-review/dsv-fix6/log-logger-2.md`). -/
opaque StdLogger : Loc → Prop

/-- A `Printf` format whose every directive is, in Go's order (`fmt/print.go`, `doPrintf`), `%`, flags
`[+-# 0]*`, width `[0-9]*`, optionally `.` and precision `[0-9]*`, then one of the verbs `v s q x X d %`:
no `*`, no `%[n]`, no trailing `%`. The state: `0` text, `1` flags, `2` width, `3` precision. Under
other verbs (`%t`, `%e`, or a flag read as the verb after the width, `%1+v`) `fmt` reprints a pointer at
depth ≥ 1 through `badVerb` at depth 0, dereferencing it, which `errLeaf`'s pointers do not allow
(`notes/axiom-review/dsv-fix6/log-logger-3.md`, `log-logger-4.md`). -/
def FmtVerbsOk.go : Nat → List w8 → Bool
  | 0, [] => true
  | _, [] => false
  | 0, c :: r => if c = 37 then FmtVerbsOk.go 1 r else FmtVerbsOk.go 0 r
  | st, c :: r =>
    if c ∈ ([118, 115, 113, 120, 88, 100, 37] : List w8) then FmtVerbsOk.go 0 r
    else if st = 1 ∧ c ∈ ([43, 45, 35, 32, 48] : List w8) then FmtVerbsOk.go 1 r
    else if c ∈ ([48, 49, 50, 51, 52, 53, 54, 55, 56, 57] : List w8) then
      FmtVerbsOk.go (if st = 3 then 3 else 2) r
    else if c = 46 ∧ st ≠ 3 then FmtVerbsOk.go 3 r
    else false

/-- See `FmtVerbsOk.go`. -/
def FmtVerbsOk (msg : GoString) : Prop := FmtVerbsOk.go 0 msg = true

instance (msg : GoString) : Decidable (FmtVerbsOk msg) :=
  inferInstanceAs (Decidable (FmtVerbsOk.go 0 msg = true))

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {hlc : HasLC} (GF : BundledGFunctors) [HeapGS hlc GF]
variable [go.Semantics] [log.Assumptions] [store.Assumptions] [transport.Assumptions]

/-- `log.Default()` returns the standard logger, not nil (`log.go`: `std`, set once by the
package's initializer and never reassigned). -/
abbrev LogDefault.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.log }}
    (App (Val (@! log.Default)) (Val #()))
  {{ (l : Loc), RET #l; ⌜l ≠ null ∧ StdLogger l⌝ }}

/-- `l.Printf(format, args...)` on the standard logger (`StdLogger l`; a nil or zero `*Logger`
panics), a format `FmtVerbsOk` allows and operands `argOk` allows, which it gives back. A `Logger` is safe for concurrent use: no ownership of it. -/
abbrev LoggerPrintf.spec : Prop :=
  ∀ (l : Loc) (msg : GoString) (arg : GoSlice) (xs : List GoInterface) (dq : DFrac), StdLogger l → FmtVerbsOk msg →
  {{ isPkgInit (PROP := IProp GF) pkg_id.log ∗ arg ↦*{dq} xs ∗ [∗list] x ∈ xs, argOk x }}
    (App (App (Val (l @!! go.GoType.PointerType log.Logger.ty @!! go!"Printf")) (Val #msg))
      (Val #arg))
  {{ RET #(); arg ↦*{dq} xs ∗ [∗list] x ∈ xs, argOk x }}

/-- `l.Println(args...)` on the standard logger and operands `argOk` allows, given back. -/
abbrev LoggerPrintln.spec : Prop :=
  ∀ (l : Loc) (arg : GoSlice) (xs : List GoInterface) (dq : DFrac), StdLogger l →
  {{ isPkgInit (PROP := IProp GF) pkg_id.log ∗ arg ↦*{dq} xs ∗ [∗list] x ∈ xs, argOk x }}
    (App (Val (l @!! go.GoType.PointerType log.Logger.ty @!! go!"Println")) (Val #arg))
  {{ RET #(); arg ↦*{dq} xs ∗ [∗list] x ∈ xs, argOk x }}

end specs

/-- The `*Logger` specs the proofs take (an instance argument; made from the axioms of
`Craq/LogAx.lean` by the statement's proof). -/
class LogSpecs [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext] {hlc : HasLC}
    (GF : BundledGFunctors) [HeapGS hlc GF] [go.Semantics] [log.Assumptions] [store.Assumptions]
    [transport.Assumptions] : Prop where
  wp_Default : LogDefault.spec GF
  wp_Logger_Printf : LoggerPrintf.spec GF
  wp_Logger_Println : LoggerPrintln.spec GF

/-! `log.Printf` and `log.Println` have bodies in Perennial's trusted model
(`Perennial/TrustedCode/log.lean`: they do nothing), so their specs are proved, not assumed, over the
same argument condition (the model is faithful only for operands whose formatting runs no code and
reads only memory the caller holds: `argOk`'s). -/

section printf
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [package_sem : log.Assumptions] [store.Assumptions]
  [transport.Assumptions]

/-- `log.Printf(format, args...)` on arguments `argOk` allows. -/
theorem LogSpecs.wp_Printf (msg : GoString) (arg : GoSlice) (xs : List GoInterface) (dq : DFrac) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.log ∗ arg ↦*{dq} xs ∗ [∗list] x ∈ xs, argOk x }}
      (App (App (Val (@! log.Printf)) (Val #msg)) (Val #arg))
    {{ RET #(); arg ↦*{dq} xs ∗ [∗list] x ∈ xs, argOk x }} := by
  wp_start as ⟨Hsl, Hok⟩
  wp_end

/-- `log.Println(args...)` on arguments `argOk` allows. -/
theorem LogSpecs.wp_Println (arg : GoSlice) (xs : List GoInterface) (dq : DFrac) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.log ∗ arg ↦*{dq} xs ∗ [∗list] x ∈ xs, argOk x }}
      (App (Val (@! log.Println)) (Val #arg))
    {{ RET #(); arg ↦*{dq} xs ∗ [∗list] x ∈ xs, argOk x }} := by
  wp_start as ⟨Hsl, Hok⟩
  wp_end

end printf

end github_com.despreston.go_craq

end Perennial


example : Perennial.github_com.despreston.go_craq.FmtVerbsOk go!"a %s: %#v %+v %-5.2d %05x %.3q %%\n" := by decide
example : ¬ Perennial.github_com.despreston.go_craq.FmtVerbsOk go!"%1+v" := by decide
example : ¬ Perennial.github_com.despreston.go_craq.FmtVerbsOk go!"%1.2.v" := by decide
example : ¬ Perennial.github_com.despreston.go_craq.FmtVerbsOk go!"%.5 s" := by decide
example : ¬ Perennial.github_com.despreston.go_craq.FmtVerbsOk go!"%t" := by decide
example : ¬ Perennial.github_com.despreston.go_craq.FmtVerbsOk go!"%" := by decide
