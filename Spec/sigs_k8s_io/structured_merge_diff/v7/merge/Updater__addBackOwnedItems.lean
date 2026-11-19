/-
`(*Updater).addBackOwnedItems(merged, pruned, prunedVersion, managedFields, applyingManager)`
(internal): `prune`'s second pass. Go groups the managers' sets by version
(`managedAtVersion`, each the union of that version's sets) and runs
`addBackOwnedItemsForVersion` once per version, the pruned version first, then the others in Go's
map order, each from the previous pass's output. With **every manager at `prunedVersion`** (the
premise; `Apply` requires one version, which is why: with several versions the passes compose and
a field owned at the applier's version can be pruned,
`issues/smd-apply-multiversion-prunes-owned.md`) that is one pass over the union of all the sets
(`addBackOwnedMF`; no manager, no pass). `applyingManager` is not read. The managed fields are only
read and given back.

Internal to `merge`: mirrors the code over the abstract stage. Draft (2026-11-19,
notes/smd-plan.md).

D10 (b)/D9 (the Draft's integration): the pass's result conforms (`RemoveItems`' premise, from `prune`'s `keysWithItems`: `prune_conforms`) and the sizes (`ToFieldSet`, `EnsureNamedFieldsAreMembers`), from `prune`'s premises.
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
abbrev merge.Updater.addBackOwnedItems.spec : Prop :=
  ∀ (u : Loc) (cv : merge.Converter) (igf igfl : GoMap) (rion : Bool) (sc : Loc) (S : Schema) (t : TypeRef)
    (mp : Loc) (merged : UVal) (pp : Loc) (pruned : UVal) (pv : GoString) (mfm : GoMap) (mf : MF)
    (mgr : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.merge ∗ isUpdater u cv igf igfl rion ∗ isIdentityConverter cv ∗ isTV mp sc S t merged ∗ isTV pp sc S t pruned ∗ ownMF mfm mf ∗
      ⌜∀ m e, mf.get m = some e → e.version = pv⌝ ∗
      ⌜merged.size < smdSizeMax ∧ pruned.size < smdSizeMax ∧ (mfUnion mf).nodes.card < smdSizeMax ∧
        conforms S t (addBackOwnedMF S t merged pruned mf)⌝ }}
    (App (App (App (App (App (Val (u @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.merge.Updater.ty @!! go!"addBackOwnedItems"))
      (Val #mp)) (Val #pp)) (Val #pv)) (Val #mfm)) (Val #mgr))
  {{ (r : Loc) (err : GoInterface), RET (PairV #r #err);
      ⌜err = interface.nil⌝ ∗ ownMF mfm mf ∗ isTV r sc S t (addBackOwnedMF S t merged pruned mf) }}

end spec

end smd
end EtcdGrove
end Perennial
