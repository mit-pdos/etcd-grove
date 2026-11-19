/-
`fieldpath.NewVersionedSet(set, apiVersion, applied)`: the `versionedSet` of its arguments, as a
`VersionedSet`.

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
abbrev fieldpath.NewVersionedSet.spec : Prop :=
  ∀ (p : Loc) (ver : GoString) (b : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.fieldpath }}
    (App (App (App (Val (@! _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.fieldpath.NewVersionedSet)) (Val #p)) (Val #ver)) (Val #b))
  {{ RET #(interface.mkOk _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.fieldpath.versionedSet.ty #(_root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.fieldpath.versionedSet.mk p ver b)); True }}

end spec

end smd
end EtcdGrove
end Perennial
