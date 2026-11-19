/-
`PathElement.Compare(rhs)`: SMD's order of path elements, `PE.compare` (field names, then keys,
then set items, then indices; within a kind, `strings.Compare`, `FieldList.Compare`,
`value.Compare`, the integers' order). On well-formed elements (every `isPE`'s, `isPE_wf`) it is a
strict total order whose zero is equality (`PE.compare_*` laws, `Vocab.lean`).

Draft (2026-11-19, notes/smd-plan.md, "The call DAG"): internal (its callers: the sorted slices of this package).
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
abbrev fieldpath.PathElement.Compare.spec : Prop :=
  ∀ (e e' : fieldpath.PathElement) (a b : PE),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.fieldpath ∗ isPE e a ∗ isPE e' b }}
    (App (Val (e @!! _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.fieldpath.PathElement.ty @!! go!"Compare")) (Val #e'))
  {{ (r : w64), RET #r; ⌜sint.Z r = PE.compare a b⌝ }}

end spec

end smd
end EtcdGrove
end Perennial
