/-
`compareWalker.compare(prefixFn)` (internal; recursive through `handleAtom` and the walker's
`doScalar`/`doList`/`doMap`): compares the walker's two sides (one at least present, each
conforming to `st.t`) at its node and adds the changes to the comparison: `cmpO S st.t st.path l r`
(`cmpF` at the node: a leaf's change, or the items' or entries' changes and the node itself
added or removed when a side is absent). No error. `inLeaf` ends as whether the node is a leaf.

Premise: the comparison's sets stay below `Set.Insert`'s bound (`typedSizeMax`).

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
abbrev typed.compareWalker.compare.spec : Prop :=
  ∀ (w sc : Loc) (S : Schema) (st : CWSt) (c : Loc) (C : Cmp) (dql dqr : DFrac) (l r : Option UVal) (f : GoFunc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ cwOwn w sc S st c C ∗ isValO st.lhs dql l ∗ isValO st.rhs dqr r ∗
      ⌜(l.isSome ∨ r.isSome) ∧ confO S st.t l ∧ confO S st.t r ∧ st.inLeaf = false ∧ (C.union (cmpO S st.t st.path l r)).removed.CardLt typedSizeMax ∧ (C.union (cmpO S st.t st.path l r)).modified.CardLt typedSizeMax ∧ (C.union (cmpO S st.t st.path l r)).added.CardLt typedSizeMax⌝ }}
    (App (Val (w @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker.ty @!! go!"compare")) (Val #f))
  {{ (errs : GoSlice), RET #errs; noErrs errs ∗ isValO st.lhs dql l ∗ isValO st.rhs dqr r ∗
      cwOwn w sc S { st with inLeaf := leafAt S st.t l r } c (C.union (cmpO S st.t st.path l r)) }}

end spec

end smd
end EtcdGrove
end Perennial
