/-
`fmtErrorOk err`: `err` is an error value Go's `fmt` formats by calling its `Error()`, needing
nothing. A `fmt`-level predicate shared by the specs of loggers and formatters (first used by
bbolt's logger contract, `Spec/go_etcd_io/bbolt/Logger.lean`), beside `fmt.argOk`
(`Spec/fmt/Errorf.lean`). Lean-first (no Rocq counterpart).
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Proof.fmt.Base
public import Spec.fmt.Errorf

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **`err` is an error value `fmt` formats by calling its `Error()`, needing nothing** (round 8,
review 7 M4: the shared `fmt`-level predicate; it belongs in the repository's `Spec/fmt/`, beside
`fmt.argOk`). Its dynamic type has `Error() string` (Go's `case error`, by signature) and no
`Format`, and `Error()` returns some string needing nothing, persistently. Producers: a law for
`errors.New`'s `*errorString` (`errors.wp_New_errorString`, whose type facts are goose's method
sets); `fmt.Errorf.spec`'s post, restated to give it (`*fmt.wrapError`/`*errorString`); the
OsFs-backed `os`/`syscall`/`unix` specs' error posts (`*fs.PathError`, `syscall.Errno`), once
their `Error` methods are translated (D20' infrastructure). Persistent. -/
def fmtErrorOk : GoInterface → IProp GF
  | .nil => iprop(False)
  | .ok ii => iprop(⌜methodSet ii.ty !! go!"Format" = none ∧
      methodSet ii.ty !! go!"Error" = some noArgStringSig⌝ ∗ fmt.stringMethodSpec ii go!"Error")

instance fmtErrorOk_persistent (err : GoInterface) : Persistent (fmtErrorOk (GF := GF) err) := by
  cases err <;> unfold fmtErrorOk <;> infer_instance

/-- **`err` is `nil` or `fmtErrorOk`** (2026-11-04): what the error posts of the OsFs-backed `os`
specs say of the error they return (`Spec/os/File__{Stat,Truncate,Sync,ReadAt,WriteAt}.lean`). -/
def fmtErrorOkOrNil : GoInterface → IProp GF
  | .nil => iprop(True)
  | .ok ii => fmtErrorOk (.ok ii)

instance fmtErrorOkOrNil_persistent (err : GoInterface) :
    Persistent (fmtErrorOkOrNil (GF := GF) err) := by
  cases err <;> unfold fmtErrorOkOrNil <;> infer_instance

theorem fmtErrorOkOrNil_ne (err : GoInterface) (h : err ≠ GoInterface.nil) :
    fmtErrorOkOrNil (GF := GF) err ⊢ fmtErrorOk err := by
  cases err with
  | nil => exact absurd rfl h
  | ok ii => exact .rfl

theorem fmtErrorOkOrNil_of (err : GoInterface) : fmtErrorOk (GF := GF) err ⊢ fmtErrorOkOrNil err := by
  cases err with
  | nil => unfold fmtErrorOkOrNil; iintro -; itrivial
  | ok ii => exact .rfl

/-- `fmt.Errorf`'s error (`fmt.Errorf.spec`'s post) is `fmtErrorOk`. -/
theorem fmtErrorOk_of_errorf (err : GoInterfaceOk)
    (h : methodSet err.ty !! go!"Format" = none ∧
      methodSet err.ty !! go!"Error" = some (go.signature.Signature [] false [go.string])) :
    fmt.stringMethodSpec (GF := GF) err go!"Error" ⊢ fmtErrorOk (.ok err) := by
  iintro #H
  unfold fmtErrorOk
  isplitr
  · ipureintro; exact h
  · iexact H

/-- A `fmtErrorOkOrNil` error is `fmt.argOk` (fmt soundness 2). -/
theorem fmt.argOk_of_fmtErrorOkOrNil (err : GoInterface) :
    fmtErrorOkOrNil (GF := GF) err ⊢ fmt.argOk err := by
  cases err with
  | nil => unfold fmt.argOk; iintro -; itrivial
  | ok ii =>
    unfold fmtErrorOkOrNil fmtErrorOk fmt.argOk
    iintro ⟨%h, #H⟩
    iright; ileft
    isplitr
    · iexact H
    · ipureintro; exact h

/-- A `fmtErrorOkOrNil` error is `fmt.argOkAt` any method-verb directive other than `%#v`/`%#w`,
`%w` included (fmt soundness 2). -/
theorem fmt.argOkAt_of_fmtErrorOkOrNil [_root_.Perennial.fmt.Assumptions] {mv : List w8} {d : fmt.Directive} (err : GoInterface) :
    ⌜d.verb ∈ mv ∧ d.sharpV = false⌝ ∗ fmtErrorOkOrNil (GF := GF) err ⊢ fmt.argOkAt mv d err := by
  cases err with
  | nil => unfold fmt.argOkAt; iintro -; itrivial
  | ok ii =>
    unfold fmtErrorOkOrNil fmtErrorOk
    iintro ⟨%hd, %h, #H⟩
    iapply fmt.argOkAt_of_error
    isplitr
    · ipureintro; exact hd
    isplitr
    · iexact H
    · ipureintro; exact h

/-! ### Errors whose message has at most `B` bytes

What a caller that collects error messages needs (the WAL's `closeAll` joins its files' `Close`
messages with `strings.Join`, whose spec bounds the output: `File__CloseLe.lean`). -/

/-- `stringMethodSpec` whose result has at most `B` bytes. -/
def stringMethodSpecLe (ii : GoInterfaceOk) (m : GoString) (B : Nat) : IProp GF :=
  iprop(□ ∀ Φ : val → IProp GF, ▷ (∀ s : GoString, ⌜s.length ≤ B⌝ -∗ Φ #s) -∗
    WP (App (Val #(methods ii.ty m ii.v)) (Val #())) {{ Φ }})

instance stringMethodSpecLe_persistent (ii : GoInterfaceOk) (m : GoString) (B : Nat) :
    Persistent (stringMethodSpecLe (GF := GF) ii m B) := by
  unfold stringMethodSpecLe; infer_instance

theorem stringMethodSpecLe_unfold (ii : GoInterfaceOk) (m : GoString) (B : Nat) :
    stringMethodSpecLe (GF := GF) ii m B = iprop(□ ∀ Φ : val → IProp GF,
      ▷ (∀ s : GoString, ⌜s.length ≤ B⌝ -∗ Φ #s) -∗
      WP (App (Val #(methods ii.ty m ii.v)) (Val #())) {{ Φ }}) := rfl

theorem stringMethodSpec_of_le (ii : GoInterfaceOk) (m : GoString) (B : Nat) :
    stringMethodSpecLe (GF := GF) ii m B ⊢ fmt.stringMethodSpec ii m := by
  unfold stringMethodSpecLe
  rw [fmt.stringMethodSpec_unfold]
  iintro #H
  imodintro
  iintro %Φ HΦ
  iapply H
  inext
  iintro %s -
  iapply HΦ

theorem stringMethodSpecLe_mono (ii : GoInterfaceOk) (m : GoString) {B B' : Nat} (h : B ≤ B') :
    stringMethodSpecLe (GF := GF) ii m B ⊢ stringMethodSpecLe ii m B' := by
  unfold stringMethodSpecLe
  iintro #H
  imodintro
  iintro %Φ HΦ
  iapply H
  inext
  iintro %s %hs
  iapply HΦ
  ipureintro; omega

/-- **`fmtErrorOk` with a message of at most `B` bytes**: `Error()` returns at most `B` bytes. -/
def fmtErrorOkLe (B : Nat) : GoInterface → IProp GF
  | .nil => iprop(False)
  | .ok ii => iprop(⌜methodSet ii.ty !! go!"Format" = none ∧
      methodSet ii.ty !! go!"Error" = some noArgStringSig⌝ ∗ stringMethodSpecLe ii go!"Error" B)

instance fmtErrorOkLe_persistent (B : Nat) (err : GoInterface) :
    Persistent (fmtErrorOkLe (GF := GF) B err) := by
  cases err <;> unfold fmtErrorOkLe <;> infer_instance

/-- `nil`, or `fmtErrorOkLe B`. -/
def fmtErrorOkOrNilLe (B : Nat) : GoInterface → IProp GF
  | .nil => iprop(True)
  | .ok ii => fmtErrorOkLe B (.ok ii)

instance fmtErrorOkOrNilLe_persistent (B : Nat) (err : GoInterface) :
    Persistent (fmtErrorOkOrNilLe (GF := GF) B err) := by
  cases err <;> unfold fmtErrorOkOrNilLe <;> infer_instance

theorem fmtErrorOk_of_le (B : Nat) (err : GoInterface) :
    fmtErrorOkLe (GF := GF) B err ⊢ fmtErrorOk err := by
  cases err with
  | nil => unfold fmtErrorOkLe; iintro %h; exact h.elim
  | ok ii =>
    unfold fmtErrorOkLe fmtErrorOk
    iintro ⟨%h, #H⟩
    isplitr
    · ipureintro; exact h
    · iapply stringMethodSpec_of_le $$ H

theorem fmtErrorOkOrNil_of_le (B : Nat) (err : GoInterface) :
    fmtErrorOkOrNilLe (GF := GF) B err ⊢ fmtErrorOkOrNil err := by
  cases err with
  | nil => unfold fmtErrorOkOrNil; iintro -; itrivial
  | ok ii => exact fmtErrorOk_of_le B (.ok ii)

theorem fmtErrorOkLe_mono {B B' : Nat} (h : B ≤ B') (err : GoInterface) :
    fmtErrorOkLe (GF := GF) B err ⊢ fmtErrorOkLe B' err := by
  cases err with
  | nil => unfold fmtErrorOkLe; iintro %h; exact h.elim
  | ok ii =>
    unfold fmtErrorOkLe
    iintro ⟨%hm, #H⟩
    isplitr
    · ipureintro; exact hm
    · iapply stringMethodSpecLe_mono _ _ h $$ H

theorem fmtErrorOkOrNilLe_mono {B B' : Nat} (h : B ≤ B') (err : GoInterface) :
    fmtErrorOkOrNilLe (GF := GF) B err ⊢ fmtErrorOkOrNilLe B' err := by
  cases err with
  | nil => unfold fmtErrorOkOrNilLe; iintro -; itrivial
  | ok ii => exact fmtErrorOkLe_mono h (.ok ii)

theorem fmtErrorOkOrNil_nil : ⊢ fmtErrorOkOrNil (GF := GF) GoInterface.nil := by
  unfold fmtErrorOkOrNil; iintro; itrivial

end defs

end EtcdGrove
end Perennial
