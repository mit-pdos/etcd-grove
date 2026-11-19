/-
`PathElementMap.Insert(pe, v)`: `m[pe] = v` (replaced if present, else inserted in order). The
size premise is `slices.Insert`'s length bound.

Draft (2026-11-19, notes/smd-plan.md, "The call DAG"): cross-package (`typed`'s compare and merge walkers).
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
abbrev fieldpath.PathElementMap.Insert.spec : Prop :=
  ∀ (l : Loc) (M : PEMap GoInterface) (e : fieldpath.PathElement) (pe : PE) (x : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.fieldpath ∗ ownPEMap l M ∗ isPE e pe ∗ ⌜M.CardLt (2 ^ 63 - 1)⌝ }}
    (App (App (Val (l @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElementMap.ty @!! go!"Insert")) (Val #e)) (Val #x))
  {{ RET #(); ownPEMap l (M.insert pe x) }}

end spec

end smd
end EtcdGrove
end Perennial
