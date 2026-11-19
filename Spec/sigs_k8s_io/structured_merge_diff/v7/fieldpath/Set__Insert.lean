/-
`Set.Insert(p)`: adds the path `p` to a set under construction (nothing for the empty path: "no
one owns the entire object"), descending the children (`SetNodeMap.Descend`, creating them) and
inserting the last element in the members. The path is only read (lent at any fraction: a walker's
reused path). The size premise is `slices.Insert`'s length bound at each level.

Draft (2026-11-19, notes/smd-plan.md, "The call DAG"): cross-package (`typed`'s walkers build field sets and comparisons; `NewSet`).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Base
public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Vocab

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
variable [package_sem : fieldpath.Assumptions]

/-- See the file header. -/
abbrev fieldpath.Set.Insert.spec : Prop :=
  ∀ (p : Loc) (S : PathSet) (s : GoSlice) (dq : DFrac) (q : Path),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.fieldpath ∗ ownSet p S ∗ isPathF s dq q ∗ ⌜S.CardLt (2 ^ 63 - 1)⌝ }}
    (App (Val (p @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set'.ty @!! go!"Insert")) (Val #s))
  {{ RET #(); ownSet p (PathSet.union S (PathSet.single q)) ∗ isPathF s dq q }}

end spec

end smd
end EtcdGrove
end Perennial
