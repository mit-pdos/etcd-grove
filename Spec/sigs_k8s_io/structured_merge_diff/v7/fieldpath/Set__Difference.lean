/-
`Set.Difference(s2)`: a set holding `S1 \ S2` (path by path: `parent - child = parent`). The result's top node and its merged members and children
slices are fresh; children only one side has (or, for the difference, a child of `s` that `s2`
lacks) are **shared** with the inputs (the same `*Set`), so the result is persistent like the
inputs (`isSet`), never owned. Recursive with `SetNodeMap.Difference` (that proof takes this spec; this
one unfolds `SetNodeMap.Difference`'s body under Löb induction, as the repository's mutual recursions).

Draft (2026-11-19, notes/smd-plan.md, "The call DAG"): cross-package (`merge`'s update and pruning, `typed`'s reconciliation).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Base
public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Vocab

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
variable [package_sem : fieldpath.Assumptions]

/-- See the file header. -/
abbrev fieldpath.Set.Difference.spec : Prop :=
  ∀ (p p2 : Loc) (A B : PathSet),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.fieldpath ∗ isSet p A ∗ isSet p2 B }}
    (App (Val (p @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set'.ty @!! go!"Difference")) (Val #p2))
  {{ (r : Loc), RET #r; isSet r (PathSet.diff A B) }}

end spec

end smd
end EtcdGrove
end Perennial
