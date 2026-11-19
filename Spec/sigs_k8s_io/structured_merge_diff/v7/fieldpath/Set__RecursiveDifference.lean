/-
`Set.RecursiveDifference(s2)`: the paths of `s` none of whose non-empty prefixes (the path itself
included) is in `s2`: a path of `s2` removes itself and everything below it (`PathSet.rdiff`).
Shares children with `s` as `Set.Difference` does; recursive with
`SetNodeMap.RecursiveDifference`.

Draft (2026-11-19, notes/smd-plan.md, "The call DAG"): cross-package (`typed.ReconcileFieldSetWithSchema`).
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
abbrev fieldpath.Set.RecursiveDifference.spec : Prop :=
  ∀ (p p2 : Loc) (A B : PathSet),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.fieldpath ∗ isSet p A ∗ isSet p2 B }}
    (App (Val (p @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set'.ty @!! go!"RecursiveDifference")) (Val #p2))
  {{ (r : Loc), RET #r; isSet r (PathSet.rdiff A B) }}

end spec

end smd
end EtcdGrove
end Perennial
