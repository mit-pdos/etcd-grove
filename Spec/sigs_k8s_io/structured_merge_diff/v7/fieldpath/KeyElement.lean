/-
`fieldpath.KeyElement(fields...)`: the path element of an associative list item's key, the
fields in the order given (SMD's own keys are sorted by name: `typed/Defs.lean`, `keyOf`). Its
values' maps are small (`UVal.mapLensOk`: `isPE`'s, 2026-11-20).

Lean-first (2026-11-19, notes/smd-plan.md).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Base
public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Defs

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
abbrev fieldpath.KeyElement.spec : Prop :=
  ∀ (s : GoSlice) (fl : FieldList),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.fieldpath ∗ isFieldList s fl ∗
      ⌜fl.all (fun f => f.2.mapLensOk) = true⌝ }}
    (App (Val (@! _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.fieldpath.KeyElement)) (Val #s))
  {{ (e : fieldpath.PathElement), RET #e; isPE e (.key fl) }}

end spec

end smd
end EtcdGrove
end Perennial
