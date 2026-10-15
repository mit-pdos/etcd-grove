/-
`fmt.Sprintf` with arguments of methodless named types (`fmt.methodlessNamedTypes`): the trust
boundary, for the one call shape `Mutex.tryAcquire` and `Election.Campaign` make,
`Sprintf("%s%x", pfx, s.Lease())` with a `LeaseID`. Perennial's `fmt.wp_Sprintf` admits
arguments of predeclared basic types only (`fmt.ArgsWf`: Go calls the `Error()`/`String()`/
`Format` methods of other arguments, which its model of `Sprintf` does not); a named type is not
one, even with a basic underlying type. A spec of its own (as `errors.IsDeadlineExceeded` is
`errors.Is`'s at one target), so that `Sprintf`'s callers that need only Perennial's
(`newRaft`, `Spec/fmt/Sprintf.lean`) do not rest on it. Lean-first (no Rocq counterpart).
-/
module

public import Perennial.Proof.fmt

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section defs
variable [ext : FfiSyntax] [go_gctx : GoGlobalContext] [GoSemanticsFunctions]

/-- The named types (Go paths) whose underlying type is a predeclared basic type and that have
no methods, so neither `Error`, `String`, `Format` nor `GoString`: Go's `fmt` formats a value of
one by its kind, as it formats the underlying type, calling nothing. The model does not record a
type's methods (`methodSet` is unconstrained), so this is a list, checked against the Go source:

* `go.etcd.io/etcd/client/v3.LeaseID`: `type LeaseID int64` (`client/v3/lease.go`), with no
  methods (`concurrency.Mutex.tryAcquire` and `Election.Campaign` format it with `%x`). -/
def fmt.methodlessNamedTypes : List GoString := [go!"go.etcd.io/etcd/client/v3.LeaseID"]

/-- An argument of `Sprintf` that Go formats without calling any method: `nil`, a value of a
predeclared basic type (`fmt.ArgWf`), or a value of one of `fmt.methodlessNamedTypes`, whose
underlying type is basic. -/
def fmt.SprintfArgOk : GoInterface → Prop
  | .nil => True
  | .ok ii => _root_.Perennial.fmt.ArgWf ii ∨
      ((∃ n, ii.ty = go.GoType.Named n [] ∧ n ∈ fmt.methodlessNamedTypes) ∧
        _root_.Perennial.fmt.IsBasicType (underlying ii.ty))

end defs

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.fmt.Assumptions]

/-- `fmt.Sprintf(format, args...)` with every argument `fmt.SprintfArgOk` returns a string `s`
with `fmt.SprintfOut format xs s`, as Perennial's `fmt.wp_Sprintf` states it (an argument of a
named type is formatted as an unknown directive: the rest of the output is arbitrary), and gives
the arguments' slice back. At the trust boundary (`fmt.SprintfNamed.wp_proof`,
`Proof/fmt/SprintfNamed.lean`). -/
abbrev fmt.SprintfNamed.spec : Prop :=
  ∀ (format : GoString) (args : GoSlice) (xs : List GoInterface) (dq : DFrac),
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ args ↦*{dq} xs ∗
        ⌜∀ a ∈ xs, fmt.SprintfArgOk a⌝ }}
      (App (App (Val #(functions _root_.Perennial.fmt.Sprintf [])) (Val #format)) (Val #args))
    {{ (s : GoString), RET #s; args ↦*{dq} xs ∗ ⌜_root_.Perennial.fmt.SprintfOut format xs s⌝ }}

end spec

end EtcdGrove
end Perennial
