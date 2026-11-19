/-
`fieldpath.MakePathElementMap(size)`: an empty `PathElementMap`, owned (`make` panics on a
negative size). The caller stores it in a variable `l` and holds `ownPEMap l PEMap.empty`.

Draft (2026-11-19, notes/smd-plan.md, "The call DAG"): cross-package (`typed`'s compare and merge walkers).
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
abbrev fieldpath.MakePathElementMap.spec : Prop :=
  ∀ (n : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.fieldpath ∗ ⌜0 ≤ sint.Z n⌝ }}
    (App (Val (@! _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.fieldpath.MakePathElementMap)) (Val #n))
  {{ (v : fieldpath.PathElementMap), RET #v; ownPEMapV v PEMap.empty }}

end spec

end smd
end EtcdGrove
end Perennial
