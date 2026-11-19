/-
`mergingWalker.doScalar(t)` (internal; the walker's `atomHandler` method for a scalar type): both
sides validate (conforming), so the node is a leaf: `out` becomes `mergeO` (`leafM` at a scalar).

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
abbrev typed.mergingWalker.doScalar.spec : Prop :=
  ∀ (w sc : Loc) (S : Schema) (st : MWSt) (dql dqr : DFrac) (l r : Option UVal) (tp : Loc)
    (s : Scalar),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ mwOwn w sc S st ∗ isValO st.lhs dql l ∗ isValO st.rhs dqr r ∗ tp ↦□ s.goName ∗
      ⌜S.find st.t.name = some (.scalar s) ∧ (l.isSome ∨ r.isSome) ∧ confO S st.t l ∧ confO S st.t r ∧
        st.inLeaf = false⌝ }}
    (App (Val (w @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker.ty @!! go!"doScalar")) (Val #tp))
  {{ (errs : GoSlice), RET #errs; noErrs errs ∗ isValO st.lhs dql l ∗ isValO st.rhs dqr r ∗
      mwOwn w sc S { st with out := mergeO S st.t l r, inLeaf := true } }}

end spec

end smd
end EtcdGrove
end Perennial
