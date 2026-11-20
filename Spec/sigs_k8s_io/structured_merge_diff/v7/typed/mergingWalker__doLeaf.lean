/-
`mergingWalker.doLeaf()` (internal): at a leaf, the first time (`inLeaf` false), runs the rule
(`ruleKeepRHS`): `out` becomes the right side if present, else the left (`leafM`), and `inLeaf`
true. Already in a leaf: nothing.

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
abbrev typed.mergingWalker.doLeaf.spec : Prop :=
  ∀ (w sc : Loc) (S : Schema) (st : MWSt) (dql dqr : DFrac) (l r : Option UVal) (sp : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ mwOwn w sc S st sp ∗ isValO st.lhs dql l ∗ isValO st.rhs dqr r ∗ ⌜l.isSome ∨ r.isSome⌝ }}
    (App (Val (w @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker.ty @!! go!"doLeaf")) (Val #()))
  {{ RET #(); isValO st.lhs dql l ∗ isValO st.rhs dqr r ∗
      (if st.inLeaf then mwOwn w sc S st sp
       else mwOwn w sc S { st with out := leafM l r, inLeaf := true } sp) }}

end spec

end smd
end EtcdGrove
end Perennial
