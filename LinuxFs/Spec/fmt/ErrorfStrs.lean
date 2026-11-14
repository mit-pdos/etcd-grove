/-
`fmt.Errorf(format, args...)` whose arguments are basic values, `[]string`s or `io/fs.FileMode`s:
what `fileutil.CheckDirPermission` (`%q` of the directory, of its mode and of the expected one) and
`fileutil.CreateDirAll` (`%q` of the directory and of the names it found) pass. Perennial's
`fmt.Errorf.spec` admits only basic arguments (`fmt.ArgsWf`) and arguments whose `Error()`/`String()`
has a spec; a `[]string` is neither, and `FileMode.String` is not translated (`LinuxFs/Code/io/fs.toml`).

Proved in `LinuxFs/Proof/fmt/ErrorfStrs.lean` over Perennial's model of `Errorf` (`errors.New(format)`,
the arguments ignored), as `fmt.ErrorfErrs.wp_proof` is. Why the model may be used for these
arguments: it departs from Go only in not formatting them, and Go's formatting of them calls nothing
that could panic or have an effect: a `[]string` under `%q`/`%v` is printed element by element (Go's
`printValue` over the slice, each string quoted; strings have no methods), reading the slice, which the
caller holds a fraction of (given back); a `FileMode` has a `String()` method (`io/fs/fs.go`), which
`fmt` calls under `%q`/`%v`: it writes at most 13 + 1 + 9 = 23 bytes into its own `[32]byte` and returns
`string(buf[:w])`, never panicking and touching nothing else. Go then returns an `*errors.errorString`
(no `%w`), non-nil, whose `Error()` returns a string (`errOk`): all the post says. (`wal-leaf5`.)
Lean-first.
-/
module

public import LinuxFs.Spec.fmt.ErrorfErrs
public import LinuxFs.Code.io.fs

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

/-- **An argument `fmt` formats without calling anything unsafe** (see the file header): `nil`, a
basic value (`fmt.ArgWf`), an `io/fs.FileMode`, or a `[]string` whose contents the caller holds a
fraction of. -/
def fmt.strArgOk : GoInterface → IProp GF
  | .nil => iprop(True)
  | .ok ii => iprop(⌜fmt.ArgWf ii ∨ (ii.ty = _root_.Perennial.io.fs.FileMode.ty ∧ ∃ m : w32, ii.v = #m)⌝ ∨
      ∃ (sl : GoSlice) (q : DFrac) (vs : List GoString),
        ⌜ii.ty = go.GoType.SliceType go.string ∧ ii.v = #sl⌝ ∗ sl ↦*{q} vs)

/-- See the file header. -/
abbrev fmt.ErrorfStrs.spec : Prop :=
  ∀ (format : GoString) (args_sl : GoSlice) (args : List GoInterface) (dq : DFrac),
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ args_sl ↦*{dq} args ∗
        [∗list] a ∈ args, fmt.strArgOk a }}
      (App (App (Val (@! _root_.Perennial.fmt.Errorf)) (Val #format)) (Val #args_sl))
    {{ (err : GoInterfaceOk), RET #(interface.ok err); args_sl ↦*{dq} args ∗
        ([∗list] a ∈ args, fmt.strArgOk a) ∗ errOk err }}

end spec

end EtcdGrove
end Perennial
