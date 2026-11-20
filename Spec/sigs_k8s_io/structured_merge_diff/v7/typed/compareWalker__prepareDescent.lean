/-
`compareWalker.prepareDescent(pe, tr, cmp)` (internal): a child walker for the child at `pe` of
type `tr`, adding to the comparison `cmp` (the parent's): as `mergingWalker.prepareDescent`.

The spare list is non-nil after (Prove phase, 2026-11-19: `finishDescent` dereferences it).

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
abbrev typed.compareWalker.prepareDescent.spec : Prop :=
  ∀ (w sc : Loc) (S : Schema) (st : CWSt) (ps : fieldpath.Path) (c sp : Loc) (a : value.Allocator)
    (pe : fieldpath.PathElement) (pe' : PE) (tr : schema.TypeRef) (t' : TypeRef) (c' : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ cwCore w sc S st ps c sp a ∗ ownPath ps st.path ∗ spareWalkers _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker sp ∗
      isPE pe pe' ∗ isTypeRef tr t' }}
    (App (App (App (Val (w @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker.ty @!! go!"prepareDescent")) (Val #pe)) (Val #tr)) (Val #c'))
  {{ (w2 : Loc), RET #w2; ∃ (sp' : Loc) (ps2 : fieldpath.Path), cwCore w sc S st ps c sp' a ∗
      cwCore w2 sc S ⟨interface.nil, interface.nil, t', st.path ++ [pe'], st.inLeaf, a⟩ ps2 c' sp' a ∗
      ownPath ps2 (st.path ++ [pe']) ∗ spareWalkers _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker sp' ∗ ⌜sp' ≠ null ∧ (sp ≠ null → sp' = sp)⌝ }}

end spec

end smd
end EtcdGrove
end Perennial
