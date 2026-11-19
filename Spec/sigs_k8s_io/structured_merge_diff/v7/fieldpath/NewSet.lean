/-
`fieldpath.NewSet(paths...)`: a new set holding the paths, inserted in order (`PSet.ofPaths`;
`Set.Insert` of each: the trie's structure is the model's).

Lean-first (2026-11-19, notes/smd-robustness.md).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Base
public import Proof.sigs_k8s_io.structured_merge_diff.v7.Own

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
variable [package_sem : merge.Assumptions]

/-- See the file header. -/
abbrev fieldpath.NewSet.spec : Prop :=
  ∀ (s : GoSlice) (dq : DFrac) (ss : List GoSlice) (ps : List Path),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.fieldpath ∗ s ↦*{dq} ss ∗ ownPaths ss ps }}
    (App (Val (@! _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.fieldpath.NewSet)) (Val #s))
  {{ (p : Loc), RET #p; s ↦*{dq} ss ∗ ownSet p (PSet.ofPaths ps) }}

end spec

end smd
end EtcdGrove
end Perennial
