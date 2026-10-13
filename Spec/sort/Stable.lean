/-
`sort.Stable` over a `sort.Interface` (the sorter of `Spec/sort/Sort.lean`). The trust boundary:
Perennial translates `Stable` (insertion sort of blocks, then `symMerge`) but proves only
`sort.Sort`. Lean-first (no Rocq counterpart); see `notes/decisions.md`, "The backend: the
buffers".

A stable sort by a strict weak order `lt` keeps the elements no element is `lt`-less than in
their order, so its result is determined: Lean's stable `List.mergeSort` with "`a` may stay
before `b` unless `b` is less than `a`".
-/
module

public import Spec.sort.Sort

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.sort.Assumptions]

/-- `sort.Stable(x)`: the sorter's list sorted stably by the strict weak order `lt`. -/
abbrev sort.Stable.spec : Prop :=
  ∀ (E : Type) (x : GoInterfaceOk) (R : List E → IProp GF) (lt : E → E → Bool) (l : List E),
  slices.StrictWeakOrder (fun a b => lt a b = true) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.sort ∗ sorterSpec x R lt ∗ R l ∗ ⌜l.length ≤ 2 ^ 62⌝ }}
    (App (Val (@! sort.Stable)) (Val #(GoInterface.ok x)))
  {{ RET #(); R (l.mergeSort (fun a b => !lt b a)) }}

end spec

end EtcdGrove
end Perennial
