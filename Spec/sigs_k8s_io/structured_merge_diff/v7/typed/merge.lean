/-
`typed.merge(lhs, rhs, rule, postRule)` (internal: `TypedValue.Merge`'s body) with `Merge`'s rule
(`ruleKeepRHS`'s closure) and no post-rule: a fresh typed value of the two operands' schema and
type holding `merge S t l r`. Takes a merging walker from `mwPool` (`typedPools`) and gives it
back reset (`mwPooled`).

Draft (2026-11-19, notes/smd-plan.md, "The call DAG": the `typed` rows).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.Base
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.Walkers

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI
open sigs_k8s_io.structured_merge_diff.v7

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : typed.Assumptions]

/-- See the file header. -/
abbrev typed.merge.spec : Prop :=
  ∀ (lp rp sc : Loc) (S : Schema) (t : TypeRef) (l r : UVal) (rule postRule : GoFunc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ isTV lp sc S t l ∗ isTV rp sc S t r ∗ ruleKeepRHSOk rule ∗ ⌜postRule = func.nil⌝ }}
    (App (App (App (App (Val (@! _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.merge)) (Val #lp)) (Val #rp)) (Val #rule)) (Val #postRule))
  {{ (p : Loc) (err : GoInterface), RET (PairV #p #err);
      ⌜err = interface.nil⌝ ∗ isTV p sc S t (merge S t l r) }}

end spec

end smd
end EtcdGrove
end Perennial
