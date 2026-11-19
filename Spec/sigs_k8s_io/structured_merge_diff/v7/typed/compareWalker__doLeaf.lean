/-
`compareWalker.doLeaf()` (internal): at a leaf, the first time (`inLeaf` false): the node's path
is added (left absent), removed (right absent) or modified (the sides differ: `value.EqualsUsing`)
(`leafC`); `inLeaf` true. Already in a leaf: nothing.

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
abbrev typed.compareWalker.doLeaf.spec : Prop :=
  ∀ (w sc : Loc) (S : Schema) (st : CWSt) (c : Loc) (C : Cmp) (dql dqr : DFrac) (l r : Option UVal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ cwOwn w sc S st c C ∗ isValO st.lhs dql l ∗ isValO st.rhs dqr r ∗ ⌜(l.isSome ∨ r.isSome) ∧
      (C.union (leafC st.path l r)).removed.CardLt typedSizeMax ∧
      (C.union (leafC st.path l r)).modified.CardLt typedSizeMax ∧
      (C.union (leafC st.path l r)).added.CardLt typedSizeMax⌝ }}
    (App (Val (w @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker.ty @!! go!"doLeaf")) (Val #()))
  {{ RET #(); isValO st.lhs dql l ∗ isValO st.rhs dqr r ∗
      (if st.inLeaf then cwOwn w sc S st c C
       else cwOwn w sc S { st with inLeaf := true } c (C.union (leafC st.path l r))) }}

end spec

end smd
end EtcdGrove
end Perennial
