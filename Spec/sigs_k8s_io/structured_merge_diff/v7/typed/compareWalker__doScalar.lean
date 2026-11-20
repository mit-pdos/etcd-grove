/-
`compareWalker.doScalar(t)` (internal; the `atomHandler` method for a scalar type): the sides
validate (conforming), so the node is a leaf (`doLeaf`): adds `cmpBelow` (`leafC` at a scalar).

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
abbrev typed.compareWalker.doScalar.spec : Prop :=
  ∀ (w sc : Loc) (S : Schema) (st : CWSt) (c : Loc) (C : Cmp) (dql dqr : DFrac) (l r : Option UVal) (tp : Loc) (s : Scalar) (sp : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ cwOwn w sc S st c C sp ∗ isValO st.lhs dql l ∗ isValO st.rhs dqr r ∗ tp ↦□ s.goName ∗
      ⌜S.find st.t.name = some (.scalar s) ∧ (l.isSome ∨ r.isSome) ∧ confO S st.t l ∧ confO S st.t r ∧ st.inLeaf = false ∧
        (C.union (cmpO S st.t st.path l r)).removed.CardLt (2 ^ 63 - 1) ∧ (C.union (cmpO S st.t st.path l r)).modified.CardLt (2 ^ 63 - 1) ∧ (C.union (cmpO S st.t st.path l r)).added.CardLt (2 ^ 63 - 1)⌝ }}
    (App (Val (w @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker.ty @!! go!"doScalar")) (Val #tp))
  {{ (errs : GoSlice), RET #errs; noErrs errs ∗ isValO st.lhs dql l ∗ isValO st.rhs dqr r ∗
      cwOwn w sc S { st with inLeaf := true } c (C.union (cmpBelow S st.t st.path l r)) sp }}

end spec

end smd
end EtcdGrove
end Perennial
