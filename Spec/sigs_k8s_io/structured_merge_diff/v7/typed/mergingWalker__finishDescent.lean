/-
`mergingWalker.finishDescent(w2)` (internal): back from the child `w2`: the parent's path is the
child's without its last element (the buffer, perhaps reallocated by the child's append), and
the child goes to the spare list (its struct, junk).

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
abbrev typed.mergingWalker.finishDescent.spec : Prop :=
  ∀ (w w2 sc : Loc) (S : Schema) (st st2 : MWSt) (ps ps2 : fieldpath.Path) (sp : Loc)
    (a : value.Allocator) (pe : PE),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ mwCore w sc S st ps sp a ∗ mwCore w2 sc S st2 ps2 sp a ∗ ownPath ps2 (st.path ++ [pe]) ∗
      spareWalkers _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker sp }}
    (App (Val (w @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker.ty @!! go!"finishDescent")) (Val #w2))
  {{ RET #(); ∃ ps' : fieldpath.Path, mwCore w sc S st ps' sp a ∗ ownPath ps' st.path ∗
      spareWalkers _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker sp }}

end spec

end smd
end EtcdGrove
end Perennial
