/-
`collectReasonsAndErrors(prefix, d, dec)` (`conditionsunion.go`): new slices of reasons and errors
(recursively through `d`'s unions). The premise bounds the prefix's length plus `d`'s depth (each
name, the prefix's and `d`'s, at most `N` bytes, `decNames`) so that the prefix, joined with `": "`,
fits `strings.Join` (fmt stage 1); so it is less than `2 ^ 63`: at each union the function extends
the prefix by one name with `slices.Concat`, which panics when the length overflows `int`. Each
reason is a joined path of names and a reason (at most `maxAddr` bytes, read by `len`), one per
leaf at most (`Dec.size`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.k8s_io.apiserver.pkg.authorization.authorizer.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authorizer

open Iris Iris.BI k8s_io.apiserver.pkg.authorization.authorizer

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.authorization.authorizer.Assumptions]

/-- See the file header. -/
abbrev collectReasonsAndErrors.spec : Prop :=
  ∀ (s : GoSlice) (dq : DFrac) (pre : List GoString) (d : ConditionsAwareDecision) (m : Dec) (k : w64)
    (N : Nat),
  (∀ x ∈ pre, x.length ≤ N) → (pre.length + m.depth) * (N + 2) < _root_.Perennial.strings.joinMax →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.authorization.authorizer ∗ s ↦*{dq} pre ∗ isDecision d m ∗
      decNames N d m }}
    (App (App (App (Val (@! collectReasonsAndErrors)) (Val #s)) (Val #d)) (Val #k))
  {{ (rs es : GoSlice), RET (PairV #rs #es); s ↦*{dq} pre ∗
      (∃ xs : List GoString, rs ↦* xs ∗ ownSliceCap GoString rs (DFrac.own 1) ∗
        ⌜xs.length ≤ m.size ∧
          ∀ x ∈ xs, x.length ≤ (pre.length + m.depth) * (N + 2) + maxAddr.toNat + 4⌝) ∗
      (∃ ys : List GoInterface, es ↦* ys ∗ ownSliceCap GoInterface es (DFrac.own 1) ∗
        [∗list] e ∈ ys, utilerrors.errTree e) }}

end spec

end authorizer
end EtcdGrove
end Perennial
