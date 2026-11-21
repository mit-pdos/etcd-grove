/-
`fmt.Sprintf` with a `*clientv3.Client` argument: the trust boundary, for the one call shape
`clientv3`'s `dial` makes, `Sprintf("%s://%p/%s", resolver.Schema, c, authority(ep))` (item 5,
client construction). Perennial's `fmt.wp_Sprintf` admits arguments of predeclared basic types
only (`fmt.ArgsWf`: Go calls the `Error()`/`String()`/`Format`/`GoString` methods of other
arguments, which its model does not); a pointer is not one. A spec of its own, so that
`Sprintf`'s other callers do not rest on it. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.fmt.Errorf
public import Code.go_etcd_io.etcd.client.v3

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section defs
variable [GooseExts] [go_gctx : GoGlobalContext] [GoSemanticsFunctions]

/-- An argument of `Sprintf` under the directive `d` that Go formats without calling any method or
reading any memory: `nil`, a value of a predeclared basic type (`fmt.ArgWf`), or a `*clientv3.Client`
under a `%p` (`d.verb` is `p`, byte 112): Go's `printArg` formats `%p` first, by the pointer's
address alone (go1.27.3 `fmt/print.go:686-693`, before `handleMethods`). Under any other verb Go
prints a non-nil pointer to a struct by its fields (`printValue`, `print.go:902-911`), reading the
client's memory and calling the `String`/`Error` methods of the values in its exported fields
(`print.go:756-763`), which the precondition does not own: the spec admitted that until 2026-11-20
(`notes/axiom-review/sprintfclientptr.md`, `examples/axiomcx/sprintfclientptr`). -/
def fmt.SprintfClientArgOkAt (d : fmt.Directive) : GoInterface → Prop
  | .nil => True
  | .ok ii => _root_.Perennial.fmt.ArgWf ii ∨
      (ii.ty = go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty ∧ d.verb = W8 112)

/-- The arguments under the directives: one each, in order; those left over are printed under
`%v` (`%!(EXTRA ...)`), as `fmt.argsOkAt` has them. -/
def fmt.SprintfClientArgsAt : List fmt.Directive → List GoInterface → Prop
  | _, [] => True
  | d :: ds, a :: xs => fmt.SprintfClientArgOkAt d a ∧ fmt.SprintfClientArgsAt ds xs
  | [], a :: xs => fmt.SprintfClientArgOkAt ⟨W8 118, false⟩ a ∧ fmt.SprintfClientArgsAt [] xs

/-- **The arguments `xs` of the format `format`**: the format's directives parse
(`fmt.fmtDirectives`: no `*` width or precision, no argument index, so that each directive consumes
the next argument), and each argument is `fmt.SprintfClientArgOkAt` its directive. -/
def fmt.SprintfClientArgsOk (format : GoString) (xs : List GoInterface) : Prop :=
  ∃ ds, fmt.fmtDirectives format = some ds ∧ fmt.SprintfClientArgsAt ds xs

end defs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.fmt.Assumptions]

/-- `fmt.Sprintf(format, args...)` with arguments `fmt.SprintfClientArgsOk` (basic values, and
`*clientv3.Client`s under `%p` only) returns a string `s` with `fmt.SprintfOut format xs s`, as
Perennial's `fmt.wp_Sprintf` states it (`%p` is a directive the model does not interpret: the rest
of the output is arbitrary), and gives the arguments' slice back. At the trust boundary
(`Proof/fmt/SprintfClientPtr.lean`). (2026-11-20, prove-reflectfmt: the premise was
`∀ a ∈ xs, fmt.SprintfClientArgOk a`, any directive.) -/
abbrev fmt.SprintfClientPtr.spec : Prop :=
  ∀ (format : GoString) (args : GoSlice) (xs : List GoInterface) (dq : DFrac),
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ args ↦*{dq} xs ∗
        ⌜fmt.SprintfClientArgsOk format xs⌝ }}
      (App (App (Val #(functions _root_.Perennial.fmt.Sprintf [])) (Val #format)) (Val #args))
    {{ (s : GoString), RET #s; args ↦*{dq} xs ∗ ⌜_root_.Perennial.fmt.SprintfOut format xs s⌝ }}

end spec

end EtcdGrove
end Perennial
