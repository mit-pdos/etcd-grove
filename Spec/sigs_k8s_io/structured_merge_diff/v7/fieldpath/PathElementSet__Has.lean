/-
`PathElementSet.Has(pe)`: whether `pe` is a member (binary search), on a set read at any fraction
(an owned one through `ownPESetV_read`, a set's members through `isSet_split`).

Draft (2026-11-19, notes/smd-plan.md, "The call DAG"): cross-package (`typed`'s walkers; `typed`'s reconciliation reads a set's members).
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
abbrev fieldpath.PathElementSet.Has.spec : Prop :=
  ∀ (l : Loc) (dq : DFrac) (S : FSet PE) (e : fieldpath.PathElement) (pe : PE),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.fieldpath ∗ isPESet l dq S ∗ isPE e pe }}
    (App (Val (l @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElementSet.ty @!! go!"Has")) (Val #e))
  {{ (r : Bool), RET #r; isPESet l dq S ∗ ⌜r = true ↔ pe ∈ S⌝ }}

end spec

end smd
end EtcdGrove
end Perennial
