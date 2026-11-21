/-
`reconcileWithSchemaWalker.doScalar(t)` (internal): nothing (paths below a scalar are not the
walker's: `reconOut` is `none` at a scalar type).

Draft (2026-11-19, notes/smd-plan.md, "The call DAG": the `typed` rows).

The walker is `rwOwnAt` with its path slice `ps` the same before and after (spec change, Prove
phase 2026-11-21, ownership rule: `LawProofsBRecon2Own.lean`; it was `rwOwn`, slice hidden).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.Base
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.Walkers
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsBRecon2Own

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
abbrev typed.reconcileWithSchemaWalker.doScalar.spec : Prop :=
  ∀ (w sc : Loc) (S : Schema) (st : RWSt) (ps : fieldpath.Path) (F R A : Option PathSet) (tp : Loc) (sp : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.typed ∗ rwOwnAt w sc S st ps F R A sp }}
    (App (Val (w @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.typed.reconcileWithSchemaWalker.ty @!! go!"doScalar")) (Val #tp))
  {{ (errs : GoSlice), RET #errs; noErrs errs ∗ rwOwnAt w sc S st ps F R A sp }}

end spec

end smd
end EtcdGrove
end Perennial
