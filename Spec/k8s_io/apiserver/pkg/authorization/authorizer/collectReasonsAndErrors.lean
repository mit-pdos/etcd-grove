/-
`collectReasonsAndErrors(prefix, d, dec)` (`conditionsunion.go`): new slices of reasons and errors
(recursively through `d`'s unions). The premise bounds the prefix's length plus `d`'s depth by
`2 ^ 63`: at each union the function extends the prefix by one name with `slices.Concat`, which
panics when the length overflows `int`. Lean-first (no Rocq counterpart).
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
  ∀ (s : GoSlice) (dq : DFrac) (pre : List GoString) (d : ConditionsAwareDecision) (m : Dec) (k : w64),
  pre.length + m.depth < 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.authorization.authorizer ∗ s ↦*{dq} pre ∗ isDecision d m }}
    (App (App (App (Val (@! collectReasonsAndErrors)) (Val #s)) (Val #d)) (Val #k))
  {{ (rs es : GoSlice), RET (PairV #rs #es); s ↦*{dq} pre ∗
      (∃ xs : List GoString, rs ↦* xs ∗ ownSliceCap GoString rs (DFrac.own 1)) ∗
      (∃ ys : List GoInterface, es ↦* ys ∗ ownSliceCap GoInterface es (DFrac.own 1) ∗
        [∗list] e ∈ ys, utilerrors.errTree e) }}

end spec

end authorizer
end EtcdGrove
end Perennial
