/-
`SetNodeMap.Iterate(f)`: calls `f` once on each child's path element (`PathSet.heads`), as
`PathElementSet.Iterate` (the margin: in `PE.compare`'s order).

Draft (2026-11-19, notes/smd-plan.md, "The call DAG"): cross-package (`typed`'s reconciliation iterates `element.Children`).
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
abbrev fieldpath.SetNodeMap.Iterate.spec : Prop :=
  ∀ (l : Loc) (D : PathSet) (f : GoFunc) (I : List PE → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.fieldpath ∗ isNodes l D ∗ I [] ∗
      □ (∀ (done : List PE) (e : fieldpath.PathElement) (x : PE), ⌜x ∈ D.heads ∧ x ∉ done⌝ -∗
        {{ I done ∗ isPE e x }} (App (Val #f) (Val #e)) {{ RET #(); I (done ++ [x]) }}) }}
    (App (Val (l @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.fieldpath.SetNodeMap.ty @!! go!"Iterate")) (Val #f))
  {{ RET #(); ∃ done : List PE, ⌜done.Nodup ∧ FSet.ofList done = D.heads⌝ ∗ I done }}

end spec

end smd
end EtcdGrove
end Perennial
