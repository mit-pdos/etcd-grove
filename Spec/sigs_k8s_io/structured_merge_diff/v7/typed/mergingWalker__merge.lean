/-
`mergingWalker.merge(prefixFn)` (internal; recursive through `handleAtom` and the walker's
`doScalar`/`doList`/`doMap`): merges the walker's two sides (one at least present, each
conforming to the node's type `st.t`) and sets its `out` to `mergeO S st.t l r` (`mergeF` at the
node: the right side wins at a leaf, maps per key, lists per item key in `mergeKeys` order). Its
`inLeaf` ends as whether the node is a leaf (`leafAt`). No error (the post-item hook is nil:
`Merge`'s). The sides are lent (any share) and given back.

The walker comes in fresh (no output yet, not in a leaf): what `prepareDescent` and `merge` set.

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
abbrev typed.mergingWalker.merge.spec : Prop :=
  ∀ (w sc : Loc) (S : Schema) (st : MWSt) (dql dqr : DFrac) (l r : Option UVal) (f : GoFunc) (sp : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ mwOwn w sc S st sp ∗ isValO st.lhs dql l ∗ isValO st.rhs dqr r ∗
      ⌜(l.isSome ∨ r.isSome) ∧ confO S st.t l ∧ confO S st.t r ∧ st.out = none ∧ st.inLeaf = false⌝ }}
    (App (Val (w @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker.ty @!! go!"merge")) (Val #f))
  {{ (errs : GoSlice), RET #errs; noErrs errs ∗ isValO st.lhs dql l ∗ isValO st.rhs dqr r ∗
      (∃ sp' : Loc, mwOwn w sc S { st with out := mergeO S st.t l r, inLeaf := leafAt S st.t l r } sp' ∗ ⌜sp ≠ null → sp' = sp⌝) }}

end spec

end smd
end EtcdGrove
end Perennial
