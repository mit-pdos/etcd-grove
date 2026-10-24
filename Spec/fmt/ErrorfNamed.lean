/-
`fmt.Errorf` with arguments of methodless named types (`fmt.errorfNamedTypes`): the trust
boundary, for the calls `requestV2.Unmarshal` (`legacy_request.go`) makes with
`protowire.Number` (`type Number int32`) and `protowire.Type` (`type Type int8`).
Perennial's `fmt.wp_Errorf` admits arguments of predeclared basic types only (`fmt.ArgsWf`);
a named type is not one, even with a basic underlying type. A spec of its own (as
`Spec/fmt/SprintfNamed.lean`), so that `Errorf`'s other callers do not rest on it. Lean-first.
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
no methods (`Error`, `String`, `Format`, `GoString`):
* `google.golang.org/protobuf/encoding/protowire.Number`: `type Number int32` (`wire.go:34`).
* `google.golang.org/protobuf/encoding/protowire.Type`: `type Type int8` (`wire.go:63`). -/
def fmt.errorfNamedTypes : List GoString :=
  [go!"google.golang.org/protobuf/encoding/protowire.Number",
   go!"google.golang.org/protobuf/encoding/protowire.Type"]

/-- An argument of `Errorf` that Go formats without calling any method: `nil`, a value of a
predeclared basic type (`fmt.ArgWf`), or a value of one of `fmt.errorfNamedTypes`, whose
underlying type is basic. -/
def fmt.ErrorfArgOk : GoInterface → Prop
  | .nil => True
  | .ok ii => _root_.Perennial.fmt.ArgWf ii ∨
      ((∃ n, ii.ty = go.GoType.Named n [] ∧ n ∈ fmt.errorfNamedTypes) ∧
        _root_.Perennial.fmt.IsBasicType (underlying ii.ty))

end defs

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.fmt.Assumptions]

/-- `fmt.Errorf(format, args...)` with every argument `fmt.ErrorfArgOk` returns a non-nil
`error` (`interface.ok err`) and gives the arguments' slice back. -/
abbrev fmt.ErrorfNamed.spec : Prop :=
  ∀ (format : GoString) (args_sl : GoSlice) (xs : List GoInterface) (dq : DFrac),
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt ∗ args_sl ↦*{dq} xs ∗
        ⌜∀ a ∈ xs, fmt.ErrorfArgOk a⌝ }}
      (App (App (Val (@! _root_.Perennial.fmt.Errorf)) (Val #format)) (Val #args_sl))
    {{ (err : GoInterfaceOk), RET #(interface.ok err); args_sl ↦*{dq} xs }}

end spec

end EtcdGrove
end Perennial
