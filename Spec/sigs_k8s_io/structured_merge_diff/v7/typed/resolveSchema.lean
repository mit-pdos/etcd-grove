/-
`typed.resolveSchema(s, tr, v, ah)` (internal): resolves the type `tr` names (`Schema.Resolve`),
narrows the atom to the value's kind (`deduceAtom`: the atom itself, single-kind in the scope)
and dispatches to the handler `ah`'s method for the atom (`handleAtom`). Stated for a handler
whose method for the type's atom `A` takes the value back with `Pre` (`atomHandlerOk`): the
toFieldSet, validating and removing walkers. The unresolved-type branch (an error) is excluded:
the type resolves.

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
abbrev typed.resolveSchema.spec : Prop :=
  ∀ (sc : Loc) (S : Schema) (tr : schema.TypeRef) (t : TypeRef) (A : Atom) (v : value.Value)
    (dq : DFrac) (o : Option UVal) (T : go.GoType) (hv : val) (Pre : IProp GF)
    (Q : GoSlice → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ isSchema sc S ∗ isTypeRef tr t ∗ ⌜S.WF ∧ S.find t.name = some A⌝ ∗ isValO v dq o ∗ Pre ∗
      (∀ a : schema.Atom, isAtomOpt a (some A) -∗ atomHandlerOk A a T hv iprop(isValO v dq o ∗ Pre) Q) }}
    (App (App (App (App (Val (@! _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.resolveSchema)) (Val #sc)) (Val #tr)) (Val #v)) (Val #(interface.mkOk T hv)))
  {{ (errs : GoSlice), RET #errs; Q errs }}

end spec

end smd
end EtcdGrove
end Perennial
