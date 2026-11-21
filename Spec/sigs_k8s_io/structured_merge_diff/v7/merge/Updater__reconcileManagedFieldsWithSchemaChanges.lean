/-
`(*Updater).reconcileManagedFieldsWithSchemaChanges(liveObject, managers)` (internal): a fresh
`ManagedFields` map holding every manager's set reconciled with the schema (`reconcileMF`: each set
`reconcile S t`, version and applied flag kept; `ReconcileFieldSetWithSchema`'s `nil`, "already
consistent", keeps the entry itself, which is `reconcile`'s identity case), **owned** (`ownMF`):
`Apply` and `Update` go on to write it. With an identity converter every manager's version
converts (`Convert` returns the live object, `IsMissingVersionError(nil)` is `false`), so no
manager is dropped and there is no error. The input map is only read. The managers' union below
`smdSizeMax` trie nodes (D9, `inputsSmall`'s second half) gives `ReconcileFieldSetWithSchema` its
`CardLt (2 ^ 63)` premise (added in Prove, 2026-11-21: the premise was missing). The first stage of
`applyResult` and `updateResult` (`mf0`).

Internal to `merge`: mirrors the code over the abstract stage. Draft (2026-11-19,
notes/smd-plan.md).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.merge.Base
public import Proof.sigs_k8s_io.structured_merge_diff.v7.merge.Defs

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
abbrev merge.Updater.reconcileManagedFieldsWithSchemaChanges.spec : Prop :=
  ∀ (u : Loc) (cv : merge.Converter) (igf igfl : GoMap) (rion : Bool) (sc : Loc) (S : Schema) (t : TypeRef)
    (lp : Loc) (live : UVal) (mfm : GoMap) (mf : MF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.merge ∗ isUpdater u cv igf igfl rion ∗ isIdentityConverter cv ∗ isTV lp sc S t live ∗ isMF mfm mf ∗
      ⌜(mfUnion mf).nodes.card < smdSizeMax⌝ }}
    (App (App (Val (u @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.merge.Updater.ty @!! go!"reconcileManagedFieldsWithSchemaChanges"))
      (Val #lp)) (Val #mfm))
  {{ (r : GoMap) (err : GoInterface), RET (PairV #r #err);
      ⌜err = interface.nil⌝ ∗ ownMF r (reconcileMF S t mf) }}

end spec

end smd
end EtcdGrove
end Perennial
