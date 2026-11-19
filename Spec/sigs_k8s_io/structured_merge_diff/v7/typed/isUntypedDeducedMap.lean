/-
`typed.isUntypedDeducedMap(m)` (internal): the map type is the deduced one (element type
`__untyped_deduced_`, no fields). `true` only if the element type is named `__untyped_deduced_`,
which a schema in scope does not declare (`Schema.WF`), so the reconcile walker never skips a map
in the scope.

Draft (2026-11-19, notes/smd-plan.md, "The call DAG": the `typed` rows).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.Base
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.Walkers

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
variable [package_sem : typed.Assumptions]

/-- See the file header. -/
abbrev typed.isUntypedDeducedMap.spec : Prop :=
  ∀ (mp : Loc) (fs : List (GoString × TypeRef)) (e : Option TypeRef) (rel : ElemRel),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ isMapRep mp fs e rel }}
    (App (Val (@! _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.isUntypedDeducedMap)) (Val #mp))
  {{ (b : Bool), RET #b; ⌜b = true → e.map (·.name) = some go!"__untyped_deduced_"⌝ }}

end spec

end smd
end EtcdGrove
end Perennial
