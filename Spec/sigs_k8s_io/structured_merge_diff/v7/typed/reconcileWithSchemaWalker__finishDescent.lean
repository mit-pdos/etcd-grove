/-
`reconcileWithSchemaWalker.finishDescent(v2)` (internal): back from the child `v2`: its
accumulators are merged into the parent's (`optU`: `Set.Union` when both are set), the child is
reset and goes to the spare list.

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
abbrev typed.reconcileWithSchemaWalker.finishDescent.spec : Prop :=
  ∀ (w w2 sc : Loc) (S : Schema) (st st2 : RWSt) (ps ps2 : fieldpath.Path)
    (fs tv rem add fs2 tv2 rem2 add2 sp : Loc) (R A R2 A2 : Option PathSet),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ rwCore w sc S st ps fs tv rem add sp ∗ rwCore w2 sc S st2 ps2 fs2 tv2 rem2 add2 sp ∗
      isSetO rem R ∗ isSetO add A ∗ isSetO rem2 R2 ∗ isSetO add2 A2 ∗
      spareWalkers _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.reconcileWithSchemaWalker sp }}
    (App (Val (w @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.reconcileWithSchemaWalker.ty @!! go!"finishDescent")) (Val #w2))
  {{ RET #(); ∃ rem' add' : Loc, rwCore w sc S st ps fs tv rem' add' sp ∗ isSetO rem' (optU R R2) ∗
      isSetO add' (optU A A2) ∗ spareWalkers _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.reconcileWithSchemaWalker sp }}

end spec

end smd
end EtcdGrove
end Perennial
