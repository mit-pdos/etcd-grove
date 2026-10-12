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

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.fmt.Assumptions]

/-- Method `m` of the interface value `ii`, called with no arguments, returns some string,
needing nothing (persistently: `fmt` may call it any number of times). For `Error()` this is
what Perennial's `errors.wp_New` and `fmt.wp_Errorf` give of the errors they return. -/
def fmt.stringMethodSpec (ii : GoInterfaceOk) (m : GoString) : IProp GF :=
  iprop(□ ∀ Φ : val → IProp GF, ▷ (∀ s : GoString, Φ #s) -∗
    WP (App (Val #(methods ii.ty m ii.v)) (Val #())) {{ Φ }})

/-- One argument of `Errorf`/`Printf` that Go formats without panicking or touching memory the
caller owns: `nil`; a value of a predeclared basic type (`fmt.ArgWf`: Go calls no method of
it); or a value whose `Error()` or `String()` method has `fmt.stringMethodSpec` (Go calls
`Error()` for `%w`, and `Error()` or `String()` for `%v`/`%s` of an `error`/`Stringer`; a
panic in it would be recovered by `fmt`, but the method's effects are what the spec rules
out). The types are assumed not to implement `fmt.Formatter` (nor `fmt.GoStringer` under
`%#v`), whose methods Go would call instead; the callers' are `errors.New`'s `*errorString`,
`fmt.Errorf`'s errors and `time.Duration`, which do not. -/
def fmt.argOk : GoInterface → IProp GF
  | .nil => iprop(True)
  | .ok ii => iprop(⌜_root_.Perennial.fmt.ArgWf ii⌝ ∨ fmt.stringMethodSpec ii go!"Error" ∨
      fmt.stringMethodSpec ii go!"String")

/-- Every argument is `fmt.argOk`. -/
def fmt.argsOk : List GoInterface → IProp GF
  | [] => iprop(True)
  | a :: xs => iprop(fmt.argOk a ∗ fmt.argsOk xs)

/-- An argument of a predeclared basic type is `fmt.argOk`. -/
theorem fmt.argOk_of_ArgWf (ii : GoInterfaceOk) (h : _root_.Perennial.fmt.ArgWf ii) :
    ⊢ fmt.argOk (GF := GF) (interface.ok ii) := by
  simp only [fmt.argOk]
  iintro
  ileft
  ipureintro
  exact h

/-- An error whose `Error()` returns a known string (as `errors.wp_New` gives) is
`fmt.argOk`. -/
theorem fmt.argOk_of_Error (err : GoInterfaceOk) (msg : GoString) :
    iprop(□ ∀ Φ : val → IProp GF, ▷ Φ #msg -∗
        WP (App (Val #(methods err.ty go!"Error" err.v)) (Val #())) {{ Φ }}) ⊢
      fmt.argOk (GF := GF) (interface.ok err) := by
  simp only [fmt.argOk]
  iintro #H
  iright; ileft
  unfold fmt.stringMethodSpec
  imodintro
  iintro %Φ HΦ
  iapply H
  inext
  iapply HΦ

/-- **`fmt.Errorf(format, args...)`** returns a non-nil error whose `Error()` returns some
string, for arguments that are `fmt.argsOk`; the arguments' slice comes back. -/
abbrev fmt.Errorf.spec : Prop :=
  ∀ (format : GoString) (args_sl : GoSlice) (xs : List GoInterface) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ args_sl ↦*{dq} xs ∗ fmt.argsOk xs }}
    (App (App (Val (@! _root_.Perennial.fmt.Errorf)) (Val #format)) (Val #args_sl))
  {{ (err : GoInterfaceOk), RET #(interface.ok err);
      args_sl ↦*{dq} xs ∗ fmt.stringMethodSpec err go!"Error" }}

end spec

end EtcdGrove
end Perennial
