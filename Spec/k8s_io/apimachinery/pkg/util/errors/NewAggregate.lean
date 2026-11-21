/-
`utilerrors.NewAggregate(errlist)` (`k8s.io/apimachinery/pkg/util/errors/errors.go`, translated with its
body): the code returns
`nil` for an empty list (or one of `nil`s), else an `aggregate` of a new slice holding the
non-`nil` errors (it reads the list's elements, compares each with `nil`, and keeps no reference to
the list). The spec says: the list kept, and `nil` or an `aggregate` of a slice (read-only for good: nothing
else holds it) of non-`nil` elements of the list (2026-11-20: what `aggregate.Error`'s spec needs of
the errors it formats, `Proof/.../util/errors/Defs.lean`'s `errTree`; until then nothing of the
result). Lean-first (no Rocq counterpart).
-/
module

public import Proof.k8s_io.kubernetes.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace utilerrors

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- See the file header. -/
abbrev NewAggregate.spec : Prop :=
  ∀ (s : GoSlice) (dq : DFrac) (es : List GoInterface),
  {{ (s ↦*{dq} es : IProp GF) }}
    (App (Val (@! k8s_io.apimachinery.pkg.util.errors.NewAggregate)) (Val #s))
  {{ (a : GoInterface), RET #a; s ↦*{dq} es ∗
      (⌜a = interface.nil⌝ ∨ ∃ (sl : GoSlice) (ys : List GoInterface),
        ⌜a = interface.mkOk k8s_io.apimachinery.pkg.util.errors.aggregate.ty #sl ∧
          ∀ y ∈ ys, y ≠ interface.nil ∧ y ∈ es⌝ ∗ sl ↦*□ ys) }}

end spec

end utilerrors
end EtcdGrove
end Perennial
