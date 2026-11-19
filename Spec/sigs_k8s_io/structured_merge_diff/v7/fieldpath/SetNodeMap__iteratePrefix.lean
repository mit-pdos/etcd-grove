/-
`SetNodeMap.iteratePrefix(prefix, f)`: each child's `iteratePrefix` with `append(prefix, pe)`: `f`
once on `prefix ++ q` for each path `q` of the children, as `Set.iteratePrefix`. Internal.

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
abbrev fieldpath.SetNodeMap.iteratePrefix.spec : Prop :=
  ∀ (l : Loc) (D : PathSet) (ps : GoSlice) (es : List fieldpath.PathElement) (pre : Path)
    (f : GoFunc) (T : PathSet) (I : List Path → IProp GF) (done0 : List Path),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.fieldpath ∗ isNodes l D ∗ ps ↦* es ∗ ownSliceCap fieldpath.PathElement ps (DFrac.own 1) ∗
      isPEs es pre ∗ I done0 ∗ ⌜∀ q, q ∈ D → (pre ++ q) ∈ T ∧ (pre ++ q) ∉ done0⌝ ∗
      □ (∀ (done : List Path) (q : Path) (s : GoSlice) (dq : DFrac), ⌜q ∈ T ∧ q ∉ done⌝ -∗
        {{ I done ∗ isPathF s dq q }} (App (Val #f) (Val #s))
        {{ RET #(); I (done ++ [q]) ∗ isPathF s dq q }}) }}
    (App (App (Val (l @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.fieldpath.SetNodeMap.ty @!! go!"iteratePrefix")) (Val #ps)) (Val #f))
  {{ RET #(); ps ↦* es ∗ ownSliceCap fieldpath.PathElement ps (DFrac.own 1) ∗
      ∃ ds : List Path, ⌜ds.Nodup ∧ FSet.ofList ds = PathSet.prepend pre D⌝ ∗ I (done0 ++ ds) }}

end spec

end smd
end EtcdGrove
end Perennial
