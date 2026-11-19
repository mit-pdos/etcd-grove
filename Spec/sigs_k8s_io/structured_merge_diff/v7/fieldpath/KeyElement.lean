/-
`fieldpath.KeyElement(fields...)`: a key path element of those fields, in the order given (the
`FieldList` is the variadic slice itself, behind a fresh pointer: its ownership is given up,
persistent).

Lean-first (2026-11-19, notes/smd-robustness.md).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Base
public import Proof.sigs_k8s_io.structured_merge_diff.v7.Own

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
variable [package_sem : merge.Assumptions]

/-- See the file header. -/
abbrev fieldpath.KeyElement.spec : Prop :=
  ∀ (s : GoSlice) (fl : FieldList),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.fieldpath ∗ ownFieldList s fl }}
    (App (Val (@! _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.fieldpath.KeyElement)) (Val #s))
  {{ (e : fieldpath.PathElement), RET #e; ownPE e (.key fl) }}

end spec

end smd
end EtcdGrove
end Perennial
