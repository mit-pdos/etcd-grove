/-
`fieldpath.NewSet(paths...)`: the set of the non-empty paths among `paths`, **owned** (a set under
construction: `typed.Compare` inserts into the three `NewSet()` of its `Comparison`); a client
wanting the persistent set applies `ownSet_persist`. The paths are read at any fraction (the
slice of paths at `dq`, each path persistent).

Draft (2026-11-19, notes/smd-plan.md, "The call DAG"): API (round 1's, its post made owned: see the report).
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
abbrev fieldpath.NewSet.spec : Prop :=
  ∀ (s : GoSlice) (dq : DFrac) (ss : List GoSlice) (ps : List Path),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.fieldpath ∗ s ↦*{dq} ss ∗ isPaths ss ps }}
    (App (Val (@! _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.fieldpath.NewSet)) (Val #s))
  {{ (p : Loc), RET #p; s ↦*{dq} ss ∗ ownSet p (PathSet.ofList ps) }}

end spec

end smd
end EtcdGrove
end Perennial
