/-
`(*Updater).prune(merged, managers, applyingManager, lastSet)` (internal): the merged object
pruned for the applying manager (`prune S t merged mf last`, `merge/Defs.lean`): unchanged when the
manager has no last applied set or an empty one (`lastSet` the nil interface, `last = none`, or an
empty set); else three passes: remove what the manager applied last time, put back what any
manager owns (`addBackOwnedItems`), put back what the manager did not apply last time
(`addBackDanglingItems`) (`prune_stages`, `merge/Laws.lean`). The managed fields are only read and
given back.

Premises: every manager's entry and the last set at one version `ver` (`addBackOwnedItems`'
premise; `Apply`'s one-version premise gives it); the applying manager has an entry (`Apply` has
just written it): **required**, the last line reads `managers[applyingManager].APIVersion()`,
which on a missing entry calls a method on the nil interface and panics.

Internal to `merge`: mirrors the code over the abstract stage. Draft (2026-11-19,
notes/smd-plan.md).

D10 (b) (2026-11-19, the Draft's integration): `RemoveItems` takes the premise that its result conforms; `prune` discharges it for its three passes from `keysWithItems` of the managers' and the last sets (`prune_conforms`, `merge/Laws.lean`), which `Apply`'s premise gives. D9: the sizes (`ToFieldSet`'s premise, `EnsureNamedFieldsAreMembers`' count), from `Apply`'s `inputsSmall`.
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
abbrev merge.Updater.prune.spec : Prop :=
  ∀ (u : Loc) (cv : merge.Converter) (igf igfl : GoMap) (rion : Bool) (sc : Loc) (S : Schema) (t : TypeRef)
    (mp : Loc) (merged : UVal) (mfm : GoMap) (mf : MF) (mgr : GoString)
    (ls : fieldpath.VersionedSet) (last : Option VSet) (ver : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.merge ∗ isUpdater u cv igf igfl rion ∗ isIdentityConverter cv ∗ isTV mp sc S t merged ∗ ownMF mfm mf ∗ isVSetOpt ls last ∗
      ⌜(mf.get mgr).isSome ∧ (∀ m e, mf.get m = some e → e.version = ver) ∧
        (∀ L, last = some L → L.version = ver)⌝ ∗
      ⌜(∀ m e, mf.get m = some e → keysWithItems S t e.set) ∧
        (∀ L, last = some L → keysWithItems S t L.set ∧ L.set.nodes.card < smdSizeMax) ∧
        merged.size < smdSizeMax ∧ (mfUnion mf).nodes.card < smdSizeMax⌝ }}
    (App (App (App (App (Val (u @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.merge.Updater.ty @!! go!"prune"))
      (Val #mp)) (Val #mfm)) (Val #mgr)) (Val #ls))
  {{ (r : Loc) (err : GoInterface), RET (PairV #r #err);
      ⌜err = interface.nil⌝ ∗ ownMF mfm mf ∗ isTV r sc S t (prune S t merged mf last) }}

end spec

end smd
end EtcdGrove
end Perennial
