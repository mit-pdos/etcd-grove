/-
`PathElementSet.Union(s2)`: a new set of the elements in either (a merge of the two sorted slices into a
fresh one, owned; the elements are copied, the inputs read at any fraction and given back).

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
abbrev fieldpath.PathElementSet.Union.spec : Prop :=
  ∀ (l l2 : Loc) (dq dq2 : DFrac) (A B : FSet PE),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.fieldpath ∗ isPESet l dq A ∗ isPESet l2 dq2 B }}
    (App (Val (l @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElementSet.ty @!! go!"Union")) (Val #l2))
  {{ (r : Loc), RET #r; isPESet l dq A ∗ isPESet l2 dq2 B ∗ ownPESet r (FSet.union A B) }}

end spec

end smd
end EtcdGrove
end Perennial
