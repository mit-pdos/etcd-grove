/-
`toFieldSetWalker.toFieldSet()` (internal; recursive through `resolveSchema` and the walker's
`doScalar`/`doList`/`doMap`): adds the fields the walker's value (conforming to `st.t`) sets at
its node to the set: `fieldsAt S st.t st.path x`. No error. The value is lent (any share).

Premise: the set stays below `Set.Insert`'s bound (`typedSizeMax`).

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
abbrev typed.toFieldSetWalker.toFieldSet.spec : Prop :=
  ∀ (w sc : Loc) (S : Schema) (st : TWSt) (s : Loc) (F : PathSet) (dq : DFrac) (x : UVal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ twOwn w sc S st s F ∗ isValF st.value dq x ∗ ⌜conforms S st.t x ∧ (F.union (fieldsAt S st.t st.path x)).CardLt typedSizeMax⌝ }}
    (App (Val (w @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.toFieldSetWalker.ty @!! go!"toFieldSet")) (Val #()))
  {{ (errs : GoSlice), RET #errs; noErrs errs ∗ isValF st.value dq x ∗
      twOwn w sc S st s (F.union (fieldsAt S st.t st.path x)) }}

end spec

end smd
end EtcdGrove
end Perennial
