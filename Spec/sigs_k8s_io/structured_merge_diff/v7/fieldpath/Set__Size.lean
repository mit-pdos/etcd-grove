/-
`Set.Size()`: the number of paths (members at every level, summed in a Go `int`). Exact when the
count is below `2^63`; above, the model's sum wraps (a trie sharing children can hold that many
paths in little memory; real Go never finishes counting them), so the post is conditional, not a
premise: a caller that needs the count supplies the bound.

Draft (2026-11-19, notes/smd-plan.md, "The call DAG"): cross-package (`typed`'s reconciliation: `Size() > 0`).
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
abbrev fieldpath.Set.Size.spec : Prop :=
  ∀ (p : Loc) (S : PathSet),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.fieldpath ∗ isSet p S }}
    (App (Val (p @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set'.ty @!! go!"Size")) (Val #()))
  {{ (r : w64), RET #r; ⌜∀ n, S.HasCard n → n < 2 ^ 63 → sint.Z r = n⌝ }}

end spec

end smd
end EtcdGrove
end Perennial
