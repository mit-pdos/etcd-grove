/-
`compareWalker.finishDescent(w2)` (internal): as `mergingWalker.finishDescent`.

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
abbrev typed.compareWalker.finishDescent.spec : Prop :=
  ∀ (w w2 sc : Loc) (S : Schema) (st st2 : CWSt) (ps ps2 : fieldpath.Path) (c c2 sp : Loc)
    (a : value.Allocator) (pe : PE),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ cwCore w sc S st ps c sp a ∗ cwCore w2 sc S st2 ps2 c2 sp a ∗ ownPath ps2 (st.path ++ [pe]) ∗
      spareWalkers _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker sp }}
    (App (Val (w @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker.ty @!! go!"finishDescent")) (Val #w2))
  {{ RET #(); ∃ ps' : fieldpath.Path, cwCore w sc S st ps' c sp a ∗ ownPath ps' st.path ∗
      spareWalkers _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker sp }}

end spec

end smd
end EtcdGrove
end Perennial
