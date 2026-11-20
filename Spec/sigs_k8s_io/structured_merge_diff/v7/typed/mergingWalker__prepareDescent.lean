/-
`mergingWalker.prepareDescent(pe, tr)` (internal): a child walker for the child at `pe` of type
`tr`: a spare walker (or a new one) filled from the parent (`*w2 = *w`: schema, rule, allocator,
spare list, `inLeaf`), its path the parent's with `pe` appended (in the parent's buffer), no
sides, no output. The parent keeps its struct (`mwCore`, its spare list now allocated: `sp'`);
the descent's resources (path buffer, spare walkers) go to the child.

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
abbrev typed.mergingWalker.prepareDescent.spec : Prop :=
  ∀ (w sc : Loc) (S : Schema) (st : MWSt) (ps : fieldpath.Path) (sp : Loc) (a : value.Allocator)
    (pe : fieldpath.PathElement) (pe' : PE) (tr : schema.TypeRef) (t' : TypeRef),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ mwCore w sc S st ps sp a ∗ ownPath ps st.path ∗ spareWalkers _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker sp ∗
      isPE pe pe' ∗ isTypeRef tr t' }}
    (App (App (Val (w @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker.ty @!! go!"prepareDescent")) (Val #pe)) (Val #tr))
  {{ (w2 : Loc), RET #w2; ∃ (sp' : Loc) (ps2 : fieldpath.Path), mwCore w sc S st ps sp' a ∗
      mwCore w2 sc S ⟨interface.nil, interface.nil, t', st.path ++ [pe'], none, st.inLeaf, a⟩ ps2 sp' a ∗
      ownPath ps2 (st.path ++ [pe']) ∗ spareWalkers _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker sp' ∗ ⌜sp' ≠ null ∧ (sp ≠ null → sp' = sp)⌝ }}

end spec

end smd
end EtcdGrove
end Perennial
