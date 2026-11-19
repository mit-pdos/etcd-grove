/-
`reconcileWithSchemaWalker.prepareDescent(pe, tr)` (internal): a child walker for the child at `pe`
of type `tr`, filled from the parent (`*v2 = *v`: its child set, `isAtomic` and accumulators too,
which the caller and the child overwrite), its path the parent's with `pe` appended (`append(v.path,
pe)`: the parent's path is not reassigned after, so the child's path buffer is given back to the
parent by the wand, Go's `append` leaving the old elements in place).

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
abbrev typed.reconcileWithSchemaWalker.prepareDescent.spec : Prop :=
  ∀ (w sc : Loc) (S : Schema) (st : RWSt) (ps : fieldpath.Path) (fs tv rem add sp : Loc)
    (pe : fieldpath.PathElement) (pe' : PE) (tr : schema.TypeRef) (t' : TypeRef),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ rwCore w sc S st ps fs tv rem add sp ∗ ownPath ps st.path ∗
      spareWalkers _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.reconcileWithSchemaWalker sp ∗ isPE pe pe' ∗ isTypeRef tr t' }}
    (App (App (Val (w @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.reconcileWithSchemaWalker.ty @!! go!"prepareDescent")) (Val #pe)) (Val #tr))
  {{ (w2 : Loc), RET #w2; ∃ (sp' : Loc) (ps2 : fieldpath.Path),
      rwCore w sc S st ps fs tv rem add sp' ∗
      rwCore w2 sc S ⟨t', st.path ++ [pe'], st.isAtomic⟩ ps2 fs tv rem add sp' ∗
      ownPath ps2 (st.path ++ [pe']) ∗ (ownPath ps2 (st.path ++ [pe']) -∗ ownPath ps st.path) ∗
      spareWalkers _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.reconcileWithSchemaWalker sp' }}

end spec

end smd
end EtcdGrove
end Perennial
