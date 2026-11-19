/-
`versionedSet.Set()`: the versioned set's set. A client holding the interface (`isVSet i e`)
resolves the dynamic type with `isVSet_concrete` and calls this method.

Draft (2026-11-19, notes/smd-plan.md, "The call DAG"): cross-package (`merge` reads every manager's entry).
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
abbrev fieldpath.versionedSet.Set.spec : Prop :=
  ∀ (v : fieldpath.versionedSet) (e : VSet),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.fieldpath ∗ isVSet (interface.mkOk _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.fieldpath.versionedSet.ty #v) e }}
    (App (Val (v @!! _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.fieldpath.versionedSet.ty @!! go!"Set")) (Val #()))
  {{ (p : Loc), RET #p; isSet p e.set }}

end spec

end smd
end EtcdGrove
end Perennial
