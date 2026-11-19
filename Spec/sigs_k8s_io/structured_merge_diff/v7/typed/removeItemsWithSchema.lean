/-
`typed.removeItemsWithSchema(val, toRemove, schema, typeRef, false)` (internal: `RemoveItems`'s
body and the removing walker's recursion on an item or entry; `shouldExtract` false, the scope:
`ExtractItems` is not reached): a fresh value (`NewValueInterface`, whole) holding `val` without
the paths of `toRemove` (`removeAt`). The value is lent (any share), conforming to the type.

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
abbrev typed.removeItemsWithSchema.spec : Prop :=
  ∀ (v : value.Value) (dq : DFrac) (x : UVal) (rp sc : Loc) (R : PathSet) (S : Schema)
    (tr : schema.TypeRef) (t : TypeRef),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ isValF v dq x ∗ isSet rp R ∗ isSchema sc S ∗ isTypeRef tr t ∗ ⌜S.WF ∧ conforms S t x⌝ }}
    (App (App (App (App (App (Val (@! _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.removeItemsWithSchema)) (Val #v)) (Val #rp)) (Val #sc)) (Val #tr)) (Val #false))
  {{ (v' : value.Value), RET #v'; isValF v dq x ∗ isValF v' (DFrac.own 1) (removeAt S t R x) }}

end spec

end smd
end EtcdGrove
end Perennial
