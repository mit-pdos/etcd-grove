/-
`fieldpath.NewVersionedSet(set, apiVersion, applied)`: the versioned set.

Lean-first (2026-11-19, notes/smd-plan.md).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.merge.Base
public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Defs

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
  ∀ (p : Loc) (S : PathSet) (ver : GoString) (b : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.fieldpath ∗ isSet p S }}
    (App (App (App (Val (@! _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.fieldpath.NewVersionedSet)) (Val #p)) (Val #ver)) (Val #b))
  {{ (i : fieldpath.VersionedSet), RET #i; isVSet i ⟨S, ver, b⟩ }}

end spec

end smd
end EtcdGrove
end Perennial
