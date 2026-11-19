/-
`typed.AsTyped(v, s, typeRef)` (no validation option): a typed value of `typeRef` holding `v`,
if `v` conforms to it (`TypedValue.Validate`), else an error.

Premises: the schema is in the scope (`Schema.WF`); no validation option (`AllowDuplicates`: a
scope restriction, `notes/smd-plan.md`). Every value `NewValueInterface` admits (`isIface`) is
either accepted or rejected: there is no third outcome. The typed value carries the schema
(`isTV`: `isSchema sc S`, `S.WF`).

Margin (`notes/smd-plan.md`, "Margins"): the error branch formats the value (`errorf("...%#v")`,
`%T`, `PathElement.String`), so its proof will rest on `fmt`'s trust-boundary axioms for arbitrary
interface values; and validation recurses once per level of the value (Go's stack, not
GooseLang's, bounds the depth).

Lean-first (2026-11-19, notes/smd-plan.md).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.Base
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.Defs

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
abbrev typed.AsTyped.spec : Prop :=
  ∀ (v : value.Value) (x : UVal) (sc : Loc) (S : Schema) (tr : schema.TypeRef) (t : TypeRef),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ isVal v x ∗ isSchema sc S ∗ isTypeRef tr t ∗ ⌜S.WF⌝ }}
    (App (App (App (App (Val (@! _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.AsTyped)) (Val #v)) (Val #sc)) (Val #tr)) (Val #slice.nil))
  {{ (p : Loc) (err : GoInterface), RET (PairV #p #err);
      (⌜conforms S t x ∧ err = interface.nil⌝ ∗ isTV p sc S t x) ∨
      ⌜¬ conforms S t x ∧ p = null ∧ err ≠ interface.nil⌝ }}

end spec

end smd
end EtcdGrove
end Perennial
