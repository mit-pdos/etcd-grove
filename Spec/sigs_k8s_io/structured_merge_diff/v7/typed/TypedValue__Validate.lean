/-
`TypedValue.Validate(opts...)` (value receiver), without options (the scope: no
`AllowDuplicates`): no error exactly when the value conforms to the type (`conforms`). The value
is lent (any share, given back): `AsTyped` validates a value before it is a `TypedValue` of the
API (`isTVu`: not validated).

Margin: the error branch formats the value (`errorf` with `%#v`, `%T`, `%v` of a `value.Value`),
beyond what `fmt.Sprintf`'s trust-boundary spec covers today (`ArgsWf`): `errorf`'s proof needs a
stronger `fmt` spec (`notes/smd-plan.md`, "Margins").

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
abbrev typed.TypedValue.Validate.spec : Prop :=
  ∀ (tv : _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.TypedValue) (sc : Loc) (S : Schema) (t : TypeRef) (x : UVal) (dq : DFrac)
    (opts : GoSlice) (dqo : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ isTVu tv sc S t x dq ∗ opts ↦*{dqo} ([] : List w64) }}
    (App (Val (tv @!! _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.TypedValue.ty @!! go!"Validate")) (Val #opts))
  {{ (err : GoInterface), RET #err; isValF tv.value' dq x ∗ opts ↦*{dqo} ([] : List w64) ∗
      ⌜err = interface.nil ↔ conforms S t x⌝ }}

end spec

end smd
end EtcdGrove
end Perennial
