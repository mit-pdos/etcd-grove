/-
`toFieldSetWalker.prepareDescent(pe, tr)` (internal): a child walker for the child at `pe` of type
`tr` (its value set by the caller after), adding to the same set: as
`mergingWalker.prepareDescent`.

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
abbrev typed.toFieldSetWalker.prepareDescent.spec : Prop :=
  ∀ (w sc : Loc) (S : Schema) (st : TWSt) (ps : fieldpath.Path) (s sp : Loc) (a : value.Allocator)
    (pe : fieldpath.PathElement) (pe' : PE) (tr : schema.TypeRef) (t' : TypeRef),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ twCore w sc S st ps s sp a ∗ ownPath ps st.path ∗ spareWalkers _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.toFieldSetWalker sp ∗
      isPE pe pe' ∗ isTypeRef tr t' }}
    (App (App (Val (w @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.toFieldSetWalker.ty @!! go!"prepareDescent")) (Val #pe)) (Val #tr))
  {{ (w2 : Loc), RET #w2; ∃ (sp' : Loc) (ps2 : fieldpath.Path), twCore w sc S st ps s sp' a ∗
      twCore w2 sc S ⟨st.value, t', st.path ++ [pe'], a⟩ ps2 s sp' a ∗
      ownPath ps2 (st.path ++ [pe']) ∗ spareWalkers _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.toFieldSetWalker sp' ∗ ⌜sp' ≠ null⌝ }}

end spec

end smd
end EtcdGrove
end Perennial
