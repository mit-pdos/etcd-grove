/-
`(*Updater).update(oldObject, newObject, version, managers, workflow, force)` (internal): the
ownership change of an object going from `oldObject` to `newObject` (`c = compare S t old new`):
each manager but `workflow` conflicts on its paths the change modifies or adds (`conflictsOf`).
- Not forced, with a conflict: the error `Conflicts` listing exactly those (manager, path) pairs
  (each once, in an order not stated: `ConflictsFromManagers`), a nil map and a nil comparison;
  the managers are not touched (given back unchanged).
- Else: the managers map itself, updated in place to `afterUpdate mf workflow confl c.removed`
  (every manager but `workflow` loses its conflicting and its removed paths; a manager left empty,
  `workflow` too, goes), and the comparison `c`.

Premises: an identity converter (every manager's version compares alike: no version premise, the
converted objects are the objects themselves); `IgnoredFields` nil and `IgnoreFilter` nil (the
API's premises: `IgnoredFields[version]` on a non-nil map without the version's entry would panic
further on, `issues/smd-ignoredfields-missing-version-panic.md`; `FilterFields(nil)` returns the
comparison unchanged). Both objects of one schema and type (`isTV`), so `Compare` succeeds.

The shared step of `Apply` (`managers` with the applier's new entry, `force` the caller's) and
`Update` (`managers` reconciled, forced). Internal to `merge`: mirrors the code over the abstract
stage. Draft (2026-11-19, notes/smd-plan.md).

D9: the objects' sizes (`Compare`'s premise), from `Apply`'s/`Update`'s `inputsSmall` (`inputsSmall_prune`, `merge/Laws.lean`).
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
abbrev merge.Updater.update.spec : Prop :=
  ∀ (u : Loc) (cv : merge.Converter) (rion : Bool) (sc : Loc) (S : Schema) (t : TypeRef)
    (op : Loc) (old : UVal) (np : Loc) (new : UVal) (ver : GoString) (mfm : GoMap) (mf : MF)
    (wf : GoString) (force : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.merge ∗ isUpdater u cv (zero_val GoMap) (zero_val GoMap) rion ∗ isIdentityConverter cv ∗ isTV op sc S t old ∗ isTV np sc S t new ∗ ownMF mfm mf ∗
      ⌜old.size < smdSizeMax ∧ new.size < smdSizeMax⌝ }}
    (App (App (App (App (App (App (Val (u @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.merge.Updater.ty @!! go!"update"))
      (Val #op)) (Val #np)) (Val #ver)) (Val #mfm)) (Val #wf)) (Val #force))
  {{ (r : GoMap) (cp : Loc) (err : GoInterface), RET (PairV (PairV #r #cp) #err);
      if !force && !(conflictsOf mf wf (compare S t old new)).isEmpty then
        iprop(⌜r = zero_val GoMap ∧ cp = null⌝ ∗ ownMF mfm mf ∗
          ∃ (s : merge.Conflicts) (l : List (GoString × Path)),
            ⌜err = interface.mkOk _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.merge.Conflicts.ty #s ∧ l.Nodup ∧
              FSet.ofList l = conflictsOf mf wf (compare S t old new)⌝ ∗ isConflicts s l)
      else
        iprop(⌜r = mfm ∧ err = interface.nil⌝ ∗
          ownMF mfm (afterUpdate mf wf (conflictsOf mf wf (compare S t old new))
            (compare S t old new).removed) ∗
          isComparison cp (compare S t old new)) }}

end spec

end smd
end EtcdGrove
end Perennial
