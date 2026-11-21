/-
`fmt.Errorf`: the trust boundary, for arguments that are not all of predeclared basic types.
Perennial's `fmt.wp_Errorf` covers only arguments of predeclared basic types (`fmt.ArgsWf`: Go
calls the `Error()`/`String()` methods of other arguments, which Perennial's model does not);
etcd's callers pass errors (`%w` of `ErrUnsupportedRequest`) and `time.Duration`s (`%v`).
Lean-first (no Rocq counterpart). Also defines `fmt.argsOk`, the arguments' condition shared
with `fmt.Printf` (`Spec/fmt/Printf.lean`).
-/
module

public import Perennial.Proof.fmt
public import Perennial.Proof.errors.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

/-! ## A format's directives (premise fixes 6, D)

Bytes are `w8`: `%` is 37, `#` 35, `+` 43, `-` 45, `0` 48, space 32, `.` 46, `*` 42, `[` 91,
digits 48 to 57, `v` 118, `s` 115, `x` 120, `X` 88, `q` 113, `w` 119. -/

/-- One directive of a format string that consumes an argument: its verb and whether it is `%#v`
or `%#w` (Go syntax: `GoString()` if the argument has one, else reflection; premise fixes 6, D;
`%#w` since fmt-soundness, 2026-11-18, `notes/fmt-sharpw.md`: Go's `doPrintf` has `case 'w'` fall
through to `case 'v'`, which sets `sharpV` from `#`, so `Errorf`'s `%#w` of an error calls its
`GoString()` or reflects; under `Printf`/`Sprintf` `%#w` is a bad verb and calls no method, so
counting it as `sharpV` only excludes more). -/
structure fmt.Directive where
  verb : w8
  sharpV : Bool
  deriving DecidableEq, Repr

/-- Where `fmt.fmtDirectivesAux` is inside a directive, after its `%`: reading the flags, the
width, or the precision (after the `.`); for the width and the precision, how many digits of the
run have been read (klog-args-fix, 2026-11-14: a run of more than `fmt.maxNumDigits` is refused). -/
inductive fmt.DirPhase where
  | flags | width (n : Nat) | prec (n : Nat)
  deriving DecidableEq, Repr

/-- The longest width or precision digit run the parser accepts: 7 (klog-args-fix, the axiom
review's MAJOR, 2026-11-14). Go's `parsenum` (go1.27.3 `fmt/print.go:350-362`) checks
`tooLarge(num)` (`num > 1e6`) before adding each digit and gives up past it: `doPrintf` then writes
`%!(NOVERB)`, stops, and prints every argument as `EXTRA` under `%v`, calling its `String()`/
`Error()`, whatever its directive (`examples/premisefix/klogargs/fmtparse_test.go`). Before the
`k`-th digit the value read has `k - 1` digits, at most `10^6 - 1` for `k ≤ 7`, so a run of at most
7 digits never trips it; a longer one may (`%.00000001d` would not, but is refused too:
conservative, rejecting more formats is sound). -/
def fmt.maxNumDigits : Nat := 7

/-- `fmt.fmtDirectives`' parser, structurally recursive over the bytes: `st = none` in literal
text, `st = some (sharp, ph)` inside a directive, `sharp` saying whether the `#` flag was read and
`ph` what is being read (Go's `doPrintf`). A `.` starts the precision only if a byte follows it, as
in Go (`if i+1 < end && format[i] == '.'`, go1.27.3 `fmt/print.go:1100`); a trailing `.` is the verb
and consumes an argument (fmt soundness, 2026-11-18, the third attack's R1: until then `"x%."` parsed
to no directive, its argument counted as `EXTRA` under `%v`; checked against Go by the differential
test `notes/fmt-third-attack.md`). -/
def fmt.fmtDirectivesAux : Option (Bool × fmt.DirPhase) → GoString → Option (List fmt.Directive)
  | _, [] => some []
  | none, b :: bs =>
    if b = W8 37 then fmt.fmtDirectivesAux (some (false, .flags)) bs
    else fmt.fmtDirectivesAux none bs
  | some (sharp, ph), b :: bs =>
    -- `b` as the verb: `*` or `[` (a `*` width or precision, an argument index) is not admitted;
    -- `%%` consumes no argument; any other verb consumes one.
    let verb : Option (List fmt.Directive) :=
      if b = W8 42 ∨ b = W8 91 then none
      else if b = W8 37 then fmt.fmtDirectivesAux none bs
      else (⟨b, sharp && (decide (b = W8 118) || decide (b = W8 119))⟩ :: ·) <$>
        fmt.fmtDirectivesAux none bs
    let digit : Prop := 48 ≤ b.toNat ∧ b.toNat ≤ 57
    match ph with
    | .flags =>
      if b = W8 35 then fmt.fmtDirectivesAux (some (true, .flags)) bs
      else if b = W8 43 ∨ b = W8 45 ∨ b = W8 48 ∨ b = W8 32 then
        fmt.fmtDirectivesAux (some (sharp, .flags)) bs
      else if digit then fmt.fmtDirectivesAux (some (sharp, .width 1)) bs
      else if b = W8 46 ∧ bs ≠ [] then fmt.fmtDirectivesAux (some (sharp, .prec 0)) bs
      else verb
    | .width n =>
      if digit then
        (if n < fmt.maxNumDigits then fmt.fmtDirectivesAux (some (sharp, .width (n + 1))) bs
         else none)
      else if b = W8 46 ∧ bs ≠ [] then fmt.fmtDirectivesAux (some (sharp, .prec 0)) bs
      else verb
    | .prec n =>
      if digit then
        (if n < fmt.maxNumDigits then fmt.fmtDirectivesAux (some (sharp, .prec (n + 1))) bs
         else none)
      else verb

/-- The directives of a format string that consume an argument, in order (premise fixes 6, D):
each `%`, then flags among `+ - # 0 space`, then decimal width, then `.` and decimal precision,
then the verb; `%%` (after any flags, width, precision) and a trailing `%` consume none. `none`
when a directive has a `*` width or precision or an argument index `[n]`, which these specs do not
admit, or a width or precision of more than `fmt.maxNumDigits` digits (Go gives up on it). Decidable: the callers' formats are literals. -/
def fmt.fmtDirectives (format : GoString) : Option (List fmt.Directive) :=
  fmt.fmtDirectivesAux none format

/-! Tests of `fmt.fmtDirectives`. -/

example : fmt.fmtDirectives go!"%w: Limit(%d) not supported" =
    some [⟨W8 119, false⟩, ⟨W8 100, false⟩] := by decide
example : fmt.fmtDirectives go!"%%d %5.2f %#v" = some [⟨W8 102, false⟩, ⟨W8 118, true⟩] := by
  decide
example : fmt.fmtDirectives go!"%#x %+v %-08.3s %.q % d" =
    some [⟨W8 120, false⟩, ⟨W8 118, false⟩, ⟨W8 115, false⟩, ⟨W8 113, false⟩,
      ⟨W8 100, false⟩] := by decide
example : fmt.fmtDirectives go!"%#w %w %+w" =
    some [⟨W8 119, true⟩, ⟨W8 119, false⟩, ⟨W8 119, false⟩] := by decide
example : fmt.fmtDirectives go!"x%." = some [⟨W8 46, false⟩] := by decide
example : fmt.fmtDirectives go!"x%5." = some [⟨W8 46, false⟩] := by decide
example : fmt.fmtDirectives go!"%.5.d" = some [⟨W8 46, false⟩] := by decide
example : fmt.fmtDirectives go!"%*d" = none := by decide
example : fmt.fmtDirectives go!"%5.*d" = none := by decide
example : fmt.fmtDirectives go!"%[1]d" = none := by decide
example : fmt.fmtDirectives go!"abc%" = some [] := by decide
example : fmt.fmtDirectives go!"%5%%s" = some [⟨W8 115, false⟩] := by decide
example : fmt.fmtDirectives go!"unexpected conf type %d" = some [⟨W8 100, false⟩] := by rfl
example : fmt.fmtDirectives go!"%1234567d|%.9999999d" =
    some [⟨W8 100, false⟩, ⟨W8 100, false⟩] := by decide
example : fmt.fmtDirectives go!"rev %99999999d" = none := by decide
example : fmt.fmtDirectives go!"rev %.99999999d" = none := by decide
example : fmt.fmtDirectives go!"%000000000005d" = some [⟨W8 100, false⟩] := by decide

/-- The verbs under which `fmt` calls an argument's `Error()`/`String()` (`handleMethods`):
`v s x X q`. -/
def fmt.methodVerbs : List w8 := [W8 118, W8 115, W8 120, W8 88, W8 113]

/-- `Errorf`'s: the method verbs and `w` (`%w` of an `error` is formatted as `%v`). -/
def fmt.errorfVerbs : List w8 := fmt.methodVerbs ++ [W8 119]

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.fmt.Assumptions]

/-- The signature `() string` of `Error` and `String`, as goose writes it in method sets (in
`Spec/fmt/ErrorOk.lean` until fmt soundness 2, 2026-11-18). -/
def noArgStringSig : go.signature := go.signature.Signature [] false [go.string]

/-- Method `m` of the interface value `ii`, called with no arguments, returns some string,
needing nothing (persistently: `fmt` may call it any number of times). For `Error()` this is
what Perennial's `errors.wp_New` and `fmt.wp_Errorf` give of the errors they return. -/
def fmt.stringMethodSpec (ii : GoInterfaceOk) (m : GoString) : IProp GF :=
  iprop(□ ∀ Φ : val → IProp GF, ▷ (∀ s : GoString, Φ #s) -∗
    WP (App (Val #(methods ii.ty m ii.v)) (Val #())) {{ Φ }})

theorem fmt.stringMethodSpec_unfold (ii : GoInterfaceOk) (m : GoString) :
    fmt.stringMethodSpec (GF := GF) ii m = iprop(□ ∀ Φ : val → IProp GF, ▷ (∀ s : GoString, Φ #s) -∗
      WP (App (Val #(methods ii.ty m ii.v)) (Val #())) {{ Φ }}) := rfl

instance fmt.stringMethodSpec_persistent (ii : GoInterfaceOk) (m : GoString) :
    Persistent (fmt.stringMethodSpec (GF := GF) ii m) := by
  unfold fmt.stringMethodSpec; infer_instance

/-- One argument of `Errorf`/`Printf` that Go formats without panicking or touching memory the
caller owns: `nil`; a value of a predeclared basic type (`fmt.ArgWf`: Go calls no method of
it); a value without a `Format` method whose `Error()` has `fmt.stringMethodSpec`; or a value with
neither a `Format` nor an `Error` method whose `String()` has it (Go calls `Error()` for `%w`, and
`Error()` or `String()` for `%v`/`%s` of an `error`/`Stringer`, but `Format` in place of either
when the type has one, and `Error()` in place of `String()` for an `error`: premise-fixes-4,
2026-11-10, the round-2 premise attack's `fmt-argOk-error-over-string-and-formatter`,
`examples/premisefix/fmtarg`; until then the disjuncts did not exclude `Format` and `Error`; a
panic in the method would be recovered by `fmt`, but the method's effects are what the spec rules
out). The method is Go's `Error() string`/`String() string` (`noArgStringSig`: fmt soundness 2,
2026-11-18, the third attack's R3: Go's `handleMethods` switches on `case error`/`case Stringer`, by
signature; a method `Error() int` is no `error`, `fmt` calls nothing and reflects into the value,
while `fmt.stringMethodSpec` of it held vacuously; `/shared/tmp/fmtfix-attack3/badsig`). What `fmt`
needs of an argument under a method verb (`v s x X q`, and `w` in `Errorf`) other than
`%#v`/`%#w`; `fmt.argOkAt` asks it only there (premise fixes 6, D), and under `w` only its `Error()`
disjunct. -/
def fmt.argOk : GoInterface → IProp GF
  | .nil => iprop(True)
  | .ok ii => iprop(⌜_root_.Perennial.fmt.ArgWf ii⌝ ∨
      (fmt.stringMethodSpec ii go!"Error" ∗
        ⌜methodSet ii.ty !! go!"Format" = none ∧ methodSet ii.ty !! go!"Error" = some noArgStringSig⌝) ∨
      (fmt.stringMethodSpec ii go!"String" ∗
        ⌜methodSet ii.ty !! go!"Format" = none ∧ methodSet ii.ty !! go!"Error" = none ∧
          methodSet ii.ty !! go!"String" = some noArgStringSig⌝))

/-- **One argument under the directive `d`**, the method verbs being `mv`: `nil` or `fmt.ArgWf`
under any directive; under a verb that is not a method verb, also a value of a type whose
underlying type is an integer type and that has no `Format` method (Go prints it as an integer by
reflection, calling no method: `%d` of raft's `ConfChangeType`, which has `String()`); and
`fmt.argOk` (its `Error()`/`String()` disjuncts) only under a method verb that is not `%#v`/`%#w` (`d.sharpV`),
and under `w` only for a type with `Error() string` (fmt soundness 2, 2026-11-18, the third attack's
R2: `Errorf`'s `%w` of a value that is no `error` is a bad verb, and `fmt` reflects into it; a
`String()` alone does not help; `/shared/tmp/fmtfix-attack3/wstringer`). -/
def fmt.argOkAtBase (mv : List w8) (d : fmt.Directive) : GoInterface → IProp GF
  | .nil => iprop(True)
  | .ok ii => iprop(⌜_root_.Perennial.fmt.ArgWf ii⌝ ∨
      ⌜d.verb ∉ mv ∧ _root_.Perennial.fmt.IsIntType (underlying ii.ty) ∧
        methodSet ii.ty !! go!"Format" = none⌝ ∨
      (⌜d.verb ∈ mv ∧ d.sharpV = false ∧
        (d.verb = W8 119 → methodSet ii.ty !! go!"Error" = some noArgStringSig)⌝ ∗
        fmt.argOk (.ok ii)))

/-- **A slice argument** under `%v` or `%s` (no `#`), the method verbs being `mv` (2026-11-20, the
user's request: `fmt.Errorf("... %v ...", sets.List(decisions))` of conditional authorization's
union authorizer, and `Sprintf` of the same; until then no slice was admitted): the argument's
dynamic type is an unnamed slice type `[]T` of a non-interface element type `T` (so the slice type
has no methods), its value a slice `sl` read-only for good (`sl ↦*□ xs`: nothing writes it any more,
so formatting it touches nothing the caller owns), and every element, as a value of type `T`, is
`fmt.argOkAtBase` the same directive (no nesting).

Why Go then calls nothing but the elements' admitted methods (go1.27.3, `src/fmt/print.go`):
`printArg` (line 674) finds no simple case for a slice other than `[]byte`, so it calls
`handleMethods` on it (line 746), which finds nothing (an unnamed slice type has no methods: no
`Formatter`, `error`, `Stringer`), then `printValue(reflect.ValueOf(arg), verb, 0)` (line 749).
`printValue`'s `reflect.Slice` case (line 856): under `%s` a slice of a `uint8`-kind element type is
printed as bytes (line 861, no method called); otherwise it writes `[`, then for each element
`p.printValue(f.Index(i), verb, depth+1)` (line 889), then `]` (`%#v` takes the other branch,
line 878, excluded here). At depth 1 `printValue` (line 756; its check, line 758) takes `value.Interface()` (the element,
of dynamic type `T`: `T` is no interface type, so no `reflect.Interface` indirection) and calls
`handleMethods(arg, value, verb)` (line 760) with the same verb: exactly what `fmt.argOkAtBase`
admits of a top-level argument under that verb (`Format` excluded, `Error()`/`String()` with their
WPs; an `fmt.ArgWf` value has no method and is printed by kind, line 764 on). A `nil` slice prints
`[]`. A method's panic is recovered by `catchPanic`, but the WPs admitted rule it out anyway. -/
def fmt.sliceArgOk (mv : List w8) (d : fmt.Directive) (ii : GoInterfaceOk) : IProp GF :=
  iprop(⌜d.verb ∈ mv ∧ (d.verb = W8 118 ∨ d.verb = W8 115) ∧ d.sharpV = false⌝ ∗
    ∃ (T : go.GoType) (V : Type) (_ : ZeroVal V) (_ : TypedPointsto (GF := GF) V)
      (_ : IntoValTyped (GF := GF) V T) (sl : GoSlice) (xs : List V),
      ⌜ii.ty = go.GoType.SliceType T ∧ ii.v = #sl ∧ go.isInterfaceType (underlying T) = false⌝ ∗
      sl ↦*□ xs ∗ [∗list] x ∈ xs, fmt.argOkAtBase mv d (interface.mkOk T #x))

/-- **One argument under the directive `d`**, the method verbs being `mv`: `nil` or `fmt.ArgWf`
under any directive; under a verb that is not a method verb, also a value of a type whose
underlying type is an integer type and that has no `Format` method (Go prints it as an integer by
reflection, calling no method: `%d` of raft's `ConfChangeType`, which has `String()`); and
`fmt.argOk` (its `Error()`/`String()` disjuncts) only under a method verb that is not `%#v`/`%#w` (`d.sharpV`),
and under `w` only for a type with `Error() string` (fmt soundness 2, 2026-11-18, the third attack's
R2: `Errorf`'s `%w` of a value that is no `error` is a bad verb, and `fmt` reflects into it; a
`String()` alone does not help; `/shared/tmp/fmtfix-attack3/wstringer`); and (2026-11-20) a slice
of such arguments under `%v`/`%s` (`fmt.sliceArgOk`). The first three disjuncts are
`fmt.argOkAtBase`'s. -/
def fmt.argOkAt (mv : List w8) (d : fmt.Directive) : GoInterface → IProp GF
  | .nil => iprop(True)
  | .ok ii => iprop(⌜_root_.Perennial.fmt.ArgWf ii⌝ ∨
      ⌜d.verb ∉ mv ∧ _root_.Perennial.fmt.IsIntType (underlying ii.ty) ∧
        methodSet ii.ty !! go!"Format" = none⌝ ∨
      (⌜d.verb ∈ mv ∧ d.sharpV = false ∧
        (d.verb = W8 119 → methodSet ii.ty !! go!"Error" = some noArgStringSig)⌝ ∗
        fmt.argOk (.ok ii)) ∨
      fmt.sliceArgOk mv d ii)

/-- An argument `fmt.argOkAtBase` its directive is `fmt.argOkAt` it. -/
theorem fmt.argOkAt_of_base {mv : List w8} {d : fmt.Directive} {a : GoInterface} :
    fmt.argOkAtBase (GF := GF) mv d a ⊢ fmt.argOkAt mv d a := by
  cases a with
  | nil => unfold fmt.argOkAt; iintro _; itrivial
  | ok ii =>
    unfold fmt.argOkAtBase fmt.argOkAt
    iintro (H | H | H)
    · ileft; iexact H
    · iright; ileft; iexact H
    · iright; iright; ileft; iexact H

/-- A read-only slice of arguments each `fmt.argOkAtBase` a `%v`/`%s` directive is `fmt.argOkAt`
it (`fmt.sliceArgOk`). -/
theorem fmt.argOkAt_slice {mv : List w8} {d : fmt.Directive} {T : go.GoType} {V : Type}
    [ZeroVal V] [TypedPointsto (GF := GF) V] [IntoValTyped (GF := GF) V T]
    (sl : GoSlice) (xs : List V)
    (hd : d.verb ∈ mv ∧ (d.verb = W8 118 ∨ d.verb = W8 115) ∧ d.sharpV = false)
    (hT : go.isInterfaceType (underlying T) = false) :
    sl ↦*□ xs ∗ ([∗list] x ∈ xs, fmt.argOkAtBase (GF := GF) mv d (interface.mkOk T #x)) ⊢
      fmt.argOkAt mv d (interface.mkOk (go.GoType.SliceType T) #sl) := by
  iintro ⟨#Hs, Hxs⟩
  unfold fmt.argOkAt fmt.sliceArgOk
  iright; iright; iright
  isplitr
  · ipureintro; exact hd
  · iexists T, V, inferInstance, inferInstance, inferInstance, sl, xs
    isplitr
    · ipureintro; exact ⟨rfl, rfl, hT⟩
    isplitr
    · iexact Hs
    · iexact Hxs

/-- The arguments under the directives: one each, in order; those left over are printed under
`%v` (`EXTRA`). -/
def fmt.argsOkAt (mv : List w8) : List fmt.Directive → List GoInterface → IProp GF
  | _, [] => iprop(True)
  | d :: ds, a :: xs => iprop(fmt.argOkAt mv d a ∗ fmt.argsOkAt mv ds xs)
  | [], a :: xs => iprop(fmt.argOkAt mv ⟨W8 118, false⟩ a ∗ fmt.argsOkAt mv [] xs)

/-- **The arguments `xs` of the format `format`**, the method verbs being `mv` (premise fixes 6,
D: until then every argument was `fmt.argOk`, whatever its verb): the format's directives parse
(`fmt.fmtDirectives`), and each argument is `fmt.argOkAt` its directive. -/
def fmt.argsOk (mv : List w8) (format : GoString) (xs : List GoInterface) : IProp GF :=
  iprop(∃ ds : List fmt.Directive, ⌜fmt.fmtDirectives format = some ds⌝ ∗ fmt.argsOkAt mv ds xs)

/-- `fmt.argsOk` from the format's directives (premise fixes 6, D). -/
theorem fmt.argsOk_intro {mv : List w8} {format : GoString} {ds : List fmt.Directive}
    {xs : List GoInterface} (h : fmt.fmtDirectives format = some ds) :
    fmt.argsOkAt (GF := GF) mv ds xs ⊢ fmt.argsOk mv format xs := by
  unfold fmt.argsOk
  iintro H
  iexists ds
  isplitr
  · ipureintro; exact h
  · iexact H

/-- A read-only `[]string` is `fmt.argOkAt` a `%v`/`%s` directive (`fmt.sliceArgOk`: strings have
no methods). -/
theorem fmt.argOkAt_strSlice {mv : List w8} {d : fmt.Directive} (sl : GoSlice) (ss : List GoString)
    (hd : d.verb ∈ mv ∧ (d.verb = W8 118 ∨ d.verb = W8 115) ∧ d.sharpV = false) :
    sl ↦*□ ss ⊢ fmt.argOkAt (GF := GF) mv d (interface.mkOk (go.GoType.SliceType go.string) #sl) := by
  iintro #Hs
  iapply (fmt.argOkAt_slice (T := go.string) (V := GoString) sl ss hd (by
    rw [go.is_underlying]; rfl))
  isplitr; · iexact Hs
  have key : ∀ (i : Nat) (x : GoString), ss[i]? = some x →
      iprop(□ (True : IProp GF)) ⊢ fmt.argOkAtBase mv d (interface.mkOk go.string #x) := by
    intro i x _
    iintro -
    unfold fmt.argOkAtBase
    ileft
    ipureintro
    exact (show _root_.Perennial.fmt.ArgsWf [interface.mkOk go.string #x] from
      .cons_string _ _ .nil) _ (List.mem_singleton_self _)
  iapply (BigSepL.bigSepL_intro (P := iprop(□ (True : IProp GF))) key)
  imodintro; itrivial

/-- An argument that is `fmt.argOk` is `fmt.argOkAt` a method-verb directive other than `%#v`/`%#w`
and `%w` (premise fixes 6, D; `%w` excluded since fmt soundness 2: under it, `fmt.argOkAt_of_error`). -/
theorem fmt.argOkAt_of_argOk {mv : List w8} {d : fmt.Directive} {a : GoInterface} :
    ⌜d.verb ∈ mv ∧ d.sharpV = false ∧ d.verb ≠ W8 119⌝ ∗ fmt.argOk (GF := GF) a ⊢
      fmt.argOkAt mv d a := by
  cases a with
  | nil => unfold fmt.argOkAt; iintro _; itrivial
  | ok ii =>
    unfold fmt.argOkAt
    iintro ⟨%h, H⟩
    iright; iright; ileft
    isplitr
    · ipureintro; exact ⟨h.1, h.2.1, fun hw => absurd hw h.2.2⟩
    · iexact H

/-- An argument whose `Error()` has `fmt.stringMethodSpec`, of a type with `Error() string` and no
`Format`, is `fmt.argOkAt` any method-verb directive other than `%#v`/`%#w`, `%w` included (fmt
soundness 2, 2026-11-18). -/
theorem fmt.argOkAt_of_error {mv : List w8} {d : fmt.Directive} {ii : GoInterfaceOk} :
    ⌜d.verb ∈ mv ∧ d.sharpV = false⌝ ∗ fmt.stringMethodSpec (GF := GF) ii go!"Error" ∗
      ⌜methodSet ii.ty !! go!"Format" = none ∧ methodSet ii.ty !! go!"Error" = some noArgStringSig⌝ ⊢
      fmt.argOkAt mv d (.ok ii) := by
  unfold fmt.argOkAt fmt.argOk
  iintro ⟨%h, #H, %hm⟩
  iright; iright; ileft
  isplitr
  · ipureintro; exact ⟨h.1, h.2, fun _ => hm.2⟩
  · iright; ileft
    isplitr
    · iexact H
    · ipureintro; exact hm

/-- An integer argument of a named type without `Format` is `fmt.argOkAt` a directive whose verb
is not a method verb (premise fixes 6, D). -/
theorem fmt.argOkAt_int {mv : List w8} {d : fmt.Directive} {ii : GoInterfaceOk} :
    ⌜d.verb ∉ mv ∧ _root_.Perennial.fmt.IsIntType (underlying ii.ty) ∧
      methodSet ii.ty !! go!"Format" = none⌝ ⊢ fmt.argOkAt (GF := GF) mv d (.ok ii) := by
  unfold fmt.argOkAt
  iintro %h
  iright; ileft; ipureintro; exact h

/-- No argument is `fmt.argsOkAt` any directives (premise fixes 6, D). -/
theorem fmt.argsOkAt_nil {mv : List w8} {ds : List fmt.Directive} :
    ⊢ fmt.argsOkAt (GF := GF) mv ds [] := by
  cases ds <;> (unfold fmt.argsOkAt; itrivial)

/-- The argument of a one-element `fmt.ArgsWf` list is `fmt.ArgWf`. -/
theorem fmt.argWf_of_argsWf {ii : GoInterfaceOk}
    (h : _root_.Perennial.fmt.ArgsWf [interface.ok ii]) : _root_.Perennial.fmt.ArgWf ii :=
  h ii (List.mem_singleton_self _)

/-- **`fmt.Errorf(format, args...)`** returns a non-nil error whose `Error()` returns some
string, for arguments that are `fmt.argsOk` under the format's verbs; the arguments' slice comes
back. (2026-11-04) Its
dynamic type has `Error() string` and no `Format` method (Go's `*fmt.wrapError`,
`*fmt.wrapErrors` and `*errors.errorString`: `Error` and `Unwrap`, or `Error` alone), so that
the error is one `fmt` formats by its `Error()` (`fmtErrorOk`, `fmtErrorOk_of_errorf`); (batch 37.9,
user-approved 2026-11-04) it is a pointer error (`IsPointerError`: all three types are pointers to
structs, and Go returns a fresh one). -/
abbrev fmt.Errorf.spec : Prop :=
  ∀ (format : GoString) (args_sl : GoSlice) (xs : List GoInterface) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ args_sl ↦*{dq} xs ∗ fmt.argsOk fmt.errorfVerbs format xs }}
    (App (App (Val (@! _root_.Perennial.fmt.Errorf)) (Val #format)) (Val #args_sl))
  {{ (err : GoInterfaceOk), RET #(interface.ok err);
      args_sl ↦*{dq} xs ∗ fmt.stringMethodSpec err go!"Error" ∗
      ⌜methodSet err.ty !! go!"Format" = none ∧
        methodSet err.ty !! go!"Error" = some (go.signature.Signature [] false [go.string])⌝ ∗
      ⌜_root_.Perennial.errors.IsPointerError err⌝ }}

end spec

section methods
variable [GooseExts] [GoSemanticsFunctions]

/-- A method absent from a type's method set, from the type's `go.MethodSetIs` (premise-fixes-4: for
`fmt.argOk`'s method facts). -/
theorem fmt.methodSet_none (t : go.GoType) {ms : List (GoString × Option go.signature)}
    [go.MethodSetIs t ms] (m : GoString) (h : go.methodSetLookup ms m = none) :
    methodSet t !! m = none := by
  have := go.MethodSetIs.method_set_is (t := t) m
  rw [h] at this
  exact this

/-- A method's signature in a type's method set, from the type's `go.MethodSetIs` (fmt soundness 2:
for `fmt.argOk`'s `noArgStringSig` facts). -/
theorem fmt.methodSet_some (t : go.GoType) {ms : List (GoString × Option go.signature)}
    [go.MethodSetIs t ms] (m : GoString) (sig : go.signature)
    (h : go.methodSetLookup ms m = some sig) : methodSet t !! m = some sig := by
  have := go.MethodSetIs.method_set_is (t := t) m
  rw [h] at this
  exact this

end methods

/-- Proves `methodSet t !! m = none` (or a conjunction of such) for a type `t` with a
`go.MethodSetIs` instance (premise-fixes-4). -/
macro "fmt_method_none" : tactic => `(tactic| (
  repeat' apply And.intro
  all_goals (apply Perennial.EtcdGrove.fmt.methodSet_none; first | rfl | decide |
    simp [go.methodSetLookup])))

/-- Proves a conjunction of `methodSet t !! m = none` and `methodSet t !! m = some noArgStringSig`
facts for a type `t` with a `go.MethodSetIs` instance (fmt soundness 2). -/
macro "fmt_method_facts" : tactic => `(tactic| (
  repeat' apply And.intro
  all_goals (first
    | (apply Perennial.EtcdGrove.fmt.methodSet_none; first | rfl | decide |
        simp [go.methodSetLookup])
    | (apply Perennial.EtcdGrove.fmt.methodSet_some; first | rfl | decide |
        simp [go.methodSetLookup, Perennial.EtcdGrove.noArgStringSig]))))

/-- Proves the pure part of `fmt.argOkAt`'s method-verb disjunct, `d.verb ∈ mv ∧ d.sharpV = false ∧
(d.verb = W8 119 → methodSet t !! "Error" = some noArgStringSig)`, for a literal directive: under a
verb other than `w` by evaluation, under `w` from a hypothesis or the type's method set (fmt
soundness 2). -/
macro "fmt_verb_ok" : tactic => `(tactic| (
  refine ⟨by decide, by decide, ?_⟩
  first
    | (intro hw; exact absurd hw (by decide))
    | (intro _; first | assumption | (apply And.right; assumption) | fmt_method_facts)))

/-- Turns a goal `fmt.argsOk mv format xs` of a literal format into `fmt.argsOkAt` its directives,
unfolded over the argument list: one `fmt.argOkAt mv d a` per argument (premise fixes 6, D). -/
macro "fmt_args_intro" : tactic => `(tactic| (
  try rw [show sint.nat (W64 (0 + 1)) = 1 by rfl]
  try simp only [List.set_cons_succ, List.set_cons_zero]
  iapply Perennial.EtcdGrove.fmt.argsOk_intro (by rfl)
  try simp only [Perennial.EtcdGrove.fmt.argsOkAt]))

/-- Turns a goal `fmt.argOkAt mv d a`, `d` a method verb of `mv` other than `%#v`/`%#w`, into
`fmt.argOk a`, or the same goal with `fmt.argOkAt` unfolded into its `fmt.argOk` disjunct
(premise fixes 6, D). -/
macro "fmt_arg_method" : tactic => `(tactic| (
  first
    | (iapply Perennial.EtcdGrove.fmt.argOkAt_of_argOk; isplitr; (ipureintro; decide))
    | (iright; iright; ileft; isplitr; (ipureintro; fmt_verb_ok))))

/-- Proves `fmt.argsOk mv format xs` of a literal format and a literal argument list (as
`wp_slice_literal` builds it): the format's directives by evaluation (premise fixes 6, D), then
each argument: `nil`, a `string` or an `int`/`int64`/`uint64` by `fmt.ArgWf`; under a verb that is
not a method verb, an integer of a named type without `Format` (its underlying type from a
`go.IsUnderlying` instance); under a method verb other than `%#v`/`%#w`, any other argument by a
hypothesis in the context giving its `Error()` or `String()` method's `fmt.stringMethodSpec`, and
a pure one (or the type's method set) its method facts (no `Format`, the method `() string`; for
`String()`, no `Error` either; premise-fixes-4, fmt soundness 2), or by a hypothesis `fmt.argOk a`
(not under `%w`). -/
macro "fmt_args_ok" : tactic => `(tactic| (
  fmt_args_intro
  try simp only [Perennial.EtcdGrove.fmt.argOkAt, Perennial.EtcdGrove.fmt.argOk]
  repeat' (first
    | isplitr
    | itrivial
    | (ileft; ipureintro; apply Perennial.EtcdGrove.fmt.argWf_of_argsWf
       first
        | exact .cons_string _ _ .nil
        | exact .cons_int _ _ _ (.int64 _) .nil
        | exact .cons_int _ _ _ (.int _) .nil
        | exact .cons_int _ _ _ (.uint64 _) .nil)
    | (iright; ileft; ipureintro
       refine ⟨by decide, ?_, by fmt_method_none⟩
       rw [go.is_underlying]; simp [_root_.Perennial.fmt.IsIntType])
    | (iright; iright; ileft; isplitr; (ipureintro; fmt_verb_ok))
    | (iapply Perennial.EtcdGrove.fmt.argOkAt_of_argOk; isplitr; (ipureintro; decide); iassumption)
    | (iright; ileft; isplitr; iassumption; ipureintro; assumption)
    | (iright; ileft; isplitr; iassumption; ipureintro; exact ‹_ ∧ _›)
    | (iright; ileft; isplitr; iassumption; ipureintro; fmt_method_facts)
    | (iright; iright; isplitr; iassumption; ipureintro; assumption)
    | (iright; iright; isplitr; iassumption; ipureintro; fmt_method_facts))))

end EtcdGrove
end Perennial
