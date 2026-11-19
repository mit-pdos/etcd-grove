/-
`SetNodeMap.Size()`: the number of paths below (summed in a Go `int`: exact below `2^63`, as
`Set.Size`). Internal.

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
abbrev fieldpath.SetNodeMap.Size.spec : Prop :=
  ∀ (l : Loc) (D : PathSet),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.fieldpath ∗ isNodes l D }}
    (App (Val (l @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.fieldpath.SetNodeMap.ty @!! go!"Size")) (Val #()))
  {{ (r : w64), RET #r; ⌜∀ n, D.HasCard n → n < 2 ^ 63 → sint.Z r = n⌝ }}

end spec

end smd
end EtcdGrove
end Perennial
