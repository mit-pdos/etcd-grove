/-
`fieldpath.MakePathElementSet(size)`: an empty `PathElementSet` with room for `size` elements,
owned (`make` panics on a negative size). The caller stores it in a variable `l` and holds
`ownPESet l ∅` (`ownPESet`'s definition).

Draft (2026-11-19, notes/smd-plan.md, "The call DAG"): cross-package (`typed`'s validation and field-set walkers: duplicate detection).
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
abbrev fieldpath.MakePathElementSet.spec : Prop :=
  ∀ (n : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.fieldpath ∗ ⌜0 ≤ sint.Z n⌝ }}
    (App (Val (@! _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.fieldpath.MakePathElementSet)) (Val #n))
  {{ (v : fieldpath.PathElementSet), RET #v; ownPESetV v FSet.empty }}

end spec

end smd
end EtcdGrove
end Perennial
