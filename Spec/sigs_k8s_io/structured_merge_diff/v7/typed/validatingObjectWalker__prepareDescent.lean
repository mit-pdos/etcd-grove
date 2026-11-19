/-
`validatingObjectWalker.prepareDescent(tr)` (internal): a child walker of type `tr` (its value set
by the caller after): a spare walker (or a new one) filled from the parent. No path.

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
abbrev typed.validatingObjectWalker.prepareDescent.spec : Prop :=
  ∀ (w sc : Loc) (S : Schema) (st : VWSt) (sp : Loc) (a : value.Allocator) (tr : schema.TypeRef)
    (t' : TypeRef),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ vwCore w sc S st sp a ∗ spareWalkers _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.validatingObjectWalker sp ∗ isTypeRef tr t' }}
    (App (Val (w @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.validatingObjectWalker.ty @!! go!"prepareDescent")) (Val #tr))
  {{ (w2 : Loc), RET #w2; ∃ sp' : Loc, vwCore w sc S st sp' a ∗ vwCore w2 sc S ⟨st.value, t', a⟩ sp' a ∗
      spareWalkers _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.validatingObjectWalker sp' ∗ ⌜sp' ≠ null⌝ }}

end spec

end smd
end EtcdGrove
end Perennial
