/-
`Path.Copy()`: a fresh copy of a path read at any fraction, owned (`merge`'s conflicts copy the
path `Set.Iterate` lends).

Draft (2026-11-19, notes/smd-plan.md, "The call DAG"): cross-package (`merge.ConflictsFromManagers`).
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
abbrev fieldpath.Path.Copy.spec : Prop :=
  ∀ (s : GoSlice) (dq : DFrac) (p : Path),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.fieldpath ∗ isPathF s dq p }}
    (App (Val (s @!! _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Path.ty @!! go!"Copy")) (Val #()))
  {{ (s' : GoSlice), RET #s'; isPathF s dq p ∗ isPathF s' (DFrac.own 1) p }}

end spec

end smd
end EtcdGrove
end Perennial
