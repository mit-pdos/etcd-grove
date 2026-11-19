/-
`SetNodeMap.RecursiveDifference(s2)`: the children part of `Set.RecursiveDifference` (a child whose
element is a member of `s2` goes whole). Internal.

Draft (2026-11-19, notes/smd-plan.md, "The call DAG"): internal.
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
abbrev fieldpath.SetNodeMap.RecursiveDifference.spec : Prop :=
  ∀ (l p2 : Loc) (D B : PathSet),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.fieldpath ∗ isNodes l D ∗ isSet p2 B }}
    (App (Val (l @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.fieldpath.SetNodeMap.ty @!! go!"RecursiveDifference")) (Val #p2))
  {{ (r : Loc), RET #r; isNodes r (PathSet.rdiff D B) }}

end spec

end smd
end EtcdGrove
end Perennial
