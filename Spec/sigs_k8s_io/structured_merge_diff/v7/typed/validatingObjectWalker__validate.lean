/-
`validatingObjectWalker.validate(prefixFn)` (internal; recursive through `resolveSchema` and the
walker's `doScalar`/`doList`/`doMap`): no error exactly when the walker's value conforms to its
type (`conforms`). The value is lent (any share).

Prove phase (2026-11-20, agent D1c, under the ownership rule: every caller is the validating
walker's own proofs and `TypedValue.Validate`): the premise `prefixOk f` dropped. On a conforming
value there are no errors, so `WithLazyPrefix` never calls `f` (its spec takes `es = [] ∨ prefixOk
f`); the walker's own `f`s (`pe.String`, a closure over it) would need `PathElement.String`'s spec,
which no proof takes.

Draft (2026-11-19, notes/smd-plan.md, "The call DAG": the `typed` rows).

D10 (c) (2026-11-19, the Draft's integration): specified on conforming values only (the premise `conforms`, no error after): rejection is outside the scope, so the error paths (`errorf`, `fmt`) are not reached and no `fmt` spec is needed.
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
abbrev typed.validatingObjectWalker.validate.spec : Prop :=
  ∀ (w sc : Loc) (S : Schema) (st : VWSt) (dq : DFrac) (x : UVal) (f : GoFunc) (sp : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ vwOwn w sc S st sp ∗ isValF st.value dq x ∗ ⌜(S.find st.t.name).isSome⌝ ∗ ⌜conforms S st.t x⌝ }}
    (App (Val (w @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.validatingObjectWalker.ty @!! go!"validate")) (Val #f))
  {{ (errs : GoSlice), RET #errs; noErrs errs ∗ isValF st.value dq x ∗
      (∃ sp' : Loc, vwOwn w sc S st sp' ∗ ⌜sp ≠ null → sp' = sp⌝) }}

end spec

end smd
end EtcdGrove
end Perennial
