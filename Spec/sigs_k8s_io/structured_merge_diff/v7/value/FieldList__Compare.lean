/-
`FieldList.Compare(rhs)`: the lexicographic order of two field lists (`flCompare`: names by
`strings.Compare`, values by `value.Compare`). Called by `fieldpath` (`PathElement.Compare` of
key elements). `FieldList`, `flCompare` and `isFieldList` are `fieldpath`'s vocabulary today
(`fieldpath/Defs.lean`); they belong in `value` (report).

Lean-first (2026-11-19, notes/smd-plan.md): Draft, the stage's per-package specs of `value`.
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.Base
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.Defs
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.Objects
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
variable [package_sem : value.Assumptions]

/-- See the file header. -/
abbrev value.FieldList.Compare.spec : Prop :=
  ∀ (f g : GoSlice) (fl gl : FieldList),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.value ∗ isFieldList f fl ∗ isFieldList g gl ∗
      ⌜fl.all (fun f => f.2.mapLensOk) = true ∧ gl.all (fun f => f.2.mapLensOk) = true⌝ }}
    (App (Val (f @!! value.FieldList.ty @!! go!"Compare")) (Val #g))
  {{ (r : w64), RET #r; ⌜r.toInt = flCompare fl gl⌝ }}

end spec

end smd
end EtcdGrove
end Perennial
