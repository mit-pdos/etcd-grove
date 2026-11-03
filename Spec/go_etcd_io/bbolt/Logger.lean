/-
bbolt's logger contract (D20', `notes/bbolt-spec-decisions.md`): `boltLogger l`, what a
`bolt.Logger` bbolt may call must do with the arguments bbolt passes it. **Exposed**: the
backend's trusted `newBoltLoggerZap` asserts it of etcd's zap logger, so its meaning is part of
what that axiom claims. Part of the API (`etc/api/bbolt.txt`).
-/
module

public import GeneratedProof.go_etcd_io.bbolt
public import Perennial.Proof.ProofPrelude
public import Perennial.Proof.fmt.Base
public import Spec.fmt.ErrorOk
public import GooseLang.Ext.OsFs.Specs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section vocab
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
/- The vocabulary is over OsFs's semantics (round 11: the default `osFs_semantics`, D22): each
predicate takes the instance in its signature (round 10), and the laws, which use the
predicates, take this section variable. -/
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-! ### The logger contract (round 7, D20': a method contract that lends each argument's resources
for the call, restricted to the format strings and argument kinds whose formatting by Go's `fmt`
calls exactly the methods it names. Round 6's D20 is in `notes/bbolt-spec-decisions.md`.) -/

/-- The logging methods bbolt calls (`Debugf` 18 sites, `Errorf` 49 (round 7 count; 3 of them in
the unspecified `MoveBucket`), `Infof` 2, `Warningf` 1, in v1.5.0 and at the fork; never
`Fatal*`/`Panic*` nor the non-`f` forms). -/
def boltLogMethods : List GoString := [go!"Debugf", go!"Errorf", go!"Infof", go!"Warningf"]

/-- The verbs bbolt's format strings use once the fork logs errors with `%v` instead of `%w`
(D20', upstream `main`'s change): `s v q d t x`. -/
def logVerbs : List w8 := [W8 115, W8 118, W8 113, W8 100, W8 116, W8 120]

/-- The verbs of a format string, in order, when every directive is a bare `%c` with `c` in
`logVerbs` (no flag, width, precision or argument index; so no `%w`, `%p`, `%#v`), `%%` being a
literal percent; `none` otherwise. Decidable: bbolt's formats are literals. -/
def fmtVerbs : GoString → Option (List w8)
  | [] => some []
  | c :: rest =>
    if c = W8 37 then
      match rest with
      | [] => none
      | d :: rest' =>
        if d = W8 37 then fmtVerbs rest'
        else if d ∈ logVerbs then (fmtVerbs rest').map (d :: ·) else none
    else fmtVerbs rest

/-- The verbs under which `fmt` calls an argument's `Error()`/`String()` (`handleMethods`, for
`v s x X q`); under any other verb it prints the value by reflection. -/
def methodVerbs : List w8 := [W8 115, W8 118, W8 113, W8 120]

/-- Method `m` of `ii`, called with no argument, returns some string given `R`, which it gives
back (persistently: `fmt` may call it more than once). -/
def stringMethodWith (R : IProp GF) (ii : GoInterfaceOk) (m : GoString) : IProp GF :=
  iprop(□ ∀ Φ : val → IProp GF, R -∗ ▷ (∀ s : GoString, R -∗ Φ #s) -∗
    WP (App (Val #(methods ii.ty m ii.v)) (Val #())) {{ Φ }})

/-- **One argument, under the verb `v`, given the lent resources `R`** (round 7: Go's precedence,
`fmt/print.go` `handleMethods`; round 8: by signature, and errors through `fmtErrorOk`). One of:
- `nil`, or a value `fmt` formats with no method and no pointee (`fmt.ArgWf`: the basic types
  and method-free named integers), under any verb;
- an **error** under a method verb (`fmtErrorOk`: `Error() string`, no `Format`; `fmt` checks
  `error` before `Stringer`, so `String` is never called);
- a **Stringer** under a method verb: `String() string`, no `Format`, and no `Error() string`
  (so Go's `case error` does not match), and `String()` returns given `R` (`os.FileMode`,
  `*Options`);
- a **`[]byte`** (a key, `%q`/`%s`; `fmt` formats it directly) whose bytes `R` lends.
`GoString` is never called (no `%#v`: `fmtVerbs`), and `%w` is excluded, so no argument is printed
by reflection through a pointer. -/
def logArgOk (R : IProp GF) (v : w8) : GoInterface → IProp GF
  | .nil => iprop(True)
  | .ok ii => iprop(⌜_root_.Perennial.fmt.ArgWf ii⌝ ∨
      (⌜v ∈ methodVerbs⌝ ∗ fmtErrorOk (.ok ii)) ∨
      (⌜methodSet ii.ty !! go!"Format" = none ∧
          methodSet ii.ty !! go!"Error" ≠ some noArgStringSig ∧
          methodSet ii.ty !! go!"String" = some noArgStringSig ∧ v ∈ methodVerbs⌝ ∗
        stringMethodWith R ii go!"String") ∨
      (∃ (s : GoSlice) (b : GoString),
        ⌜ii.ty = go.GoType.SliceType go.byte ∧ ii.v = #s⌝ ∗
        □ (R -∗ ∃ dq : DFrac, s ↦*{dq} b ∗ (s ↦*{dq} b -∗ R))))

/-- **`l` is a `bolt.Logger` bbolt may call** (round 7, D20'). Persistently, from any goroutine:
each of `boltLogMethods`, called with a format `fmtS` whose verbs are `vs` (`fmtVerbs`, one per
argument) and arguments `xs` each `logArgOk R` under its verb, with `R`, returns, giving back the
argument slice and `R`; it keeps no argument (it formats before returning). For the backend's zap
logger (`newBoltLoggerZap`, trusted) this is true of zap's standard cores: `SugaredLogger`'s
`Debugf`/`Errorf`/`Infof`/`Warnf` format with `fmt.Sprintf` synchronously (or not at all at a
disabled level), never panic or exit at these levels, and are safe for concurrent use; a
user-supplied `zapcore.Core` that panics in `Write` is outside it. The nil logger is not a
`boltLogger`: bbolt then uses its own `discardLogger`, a no-op on the fork (D20'). -/
def boltLogger (l : GoInterface) : IProp GF :=
  match l with
  | .nil => iprop(False)
  | .ok li => iprop(□ ∀ (m : GoString) (fmtS : GoString) (vs : List w8) (args : GoSlice)
      (xs : List GoInterface) (dq : DFrac) (R : IProp GF),
      ⌜m ∈ boltLogMethods ∧ fmtVerbs fmtS = some vs ∧ vs.length = xs.length⌝ -∗
      {{ args ↦*{dq} xs ∗ ([∗list] p ∈ vs.zip xs, logArgOk R p.1 p.2) ∗ R }}
        (App (App (Val #(methods li.ty m li.v)) (Val #fmtS)) (Val #args))
      {{ RET #(); args ↦*{dq} xs ∗ R }})

instance boltLogger_persistent (l : GoInterface) : Persistent (boltLogger (GF := GF) l) := by
  unfold boltLogger; split <;> infer_instance

end vocab

end bbolt
end EtcdGrove
end Perennial
