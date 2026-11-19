/-
`PathElementSet.Insert(pe)`: adds `pe` (binary search for its place, `slices.Insert` there; nothing
if present). The size premise is `slices.Insert`'s length bound (the model's 64-bit length; real Go
runs out of memory first).

Draft (2026-11-19, notes/smd-plan.md, "The call DAG"): cross-package (`typed`'s walkers' local sets; `Set.Insert`, `Set.EnsureNamedFieldsAreMembers`).
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
abbrev fieldpath.PathElementSet.Insert.spec : Prop :=
  ∀ (l : Loc) (S : FSet PE) (e : fieldpath.PathElement) (pe : PE),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.fieldpath ∗ ownPESet l S ∗ isPE e pe ∗ ⌜S.CardLt (2 ^ 63 - 1)⌝ }}
    (App (Val (l @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElementSet.ty @!! go!"Insert")) (Val #e))
  {{ RET #(); ownPESet l (FSet.union S (FSet.ofList [pe])) }}

end spec

end smd
end EtcdGrove
end Perennial
