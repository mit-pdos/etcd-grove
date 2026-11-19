/-
`(*Updater).addBackDanglingItems(merged, pruned, lastSet)` (internal): `prune`'s third pass: the
merged object less what the pruned object lost of the manager's last applied set, each closed by
`ensureNamed` (`addBackDangling`: `merged.RemoveItems((ens(fs merged) \ ens(fs pruned)) ∩
ens last)`): what was pruned but the manager did not apply last time comes back. No error in the
scope (the identity converter; `ToFieldSet` of conforming values).

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
abbrev merge.Updater.addBackDanglingItems.spec : Prop :=
  ∀ (u : Loc) (cv : merge.Converter) (igf igfl : GoMap) (rion : Bool) (sc : Loc) (S : Schema) (t : TypeRef)
    (mp : Loc) (merged : UVal) (pp : Loc) (pruned : UVal) (ls : fieldpath.VersionedSet) (L : VSet),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.merge ∗ isUpdater u cv igf igfl rion ∗ isIdentityConverter cv ∗ isTV mp sc S t merged ∗ isTV pp sc S t pruned ∗ isVSet ls L }}
    (App (App (App (Val (u @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.merge.Updater.ty @!! go!"addBackDanglingItems"))
      (Val #mp)) (Val #pp)) (Val #ls))
  {{ (r : Loc) (err : GoInterface), RET (PairV #r #err);
      ⌜err = interface.nil⌝ ∗ isTV r sc S t (addBackDangling S t merged pruned L.set) }}

end spec

end smd
end EtcdGrove
end Perennial
