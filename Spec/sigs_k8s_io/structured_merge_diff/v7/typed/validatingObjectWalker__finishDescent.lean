/-
`validatingObjectWalker.finishDescent(v2)` (internal): the child goes to the spare list.

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
abbrev typed.validatingObjectWalker.finishDescent.spec : Prop :=
  ∀ (w w2 sc : Loc) (S : Schema) (st st2 : VWSt) (sp : Loc) (a : value.Allocator),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ vwCore w sc S st sp a ∗ vwCore w2 sc S st2 sp a ∗ spareWalkers _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.validatingObjectWalker sp }}
    (App (Val (w @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.validatingObjectWalker.ty @!! go!"finishDescent")) (Val #w2))
  {{ RET #(); vwCore w sc S st sp a ∗ spareWalkers _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.validatingObjectWalker sp }}

end spec

end smd
end EtcdGrove
end Perennial
