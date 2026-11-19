/-
`(*Updater).Apply(liveObject, configObject, version, managers, manager, force)`: server-side
apply of `configObject` by `manager`. The outcome is `applyResult` (`merge/Defs.lean`): either the
new object (`nil` when it equals the live one and the updater does not return the input on a
no-op) and the new managers (`manager` owning exactly the configuration's fields, applied; every
other manager losing what changed and what was removed), or, without `force`, a `Conflicts` error
listing exactly each other manager's fields that the apply changes (the conflict set `cs` of
(manager, path) pairs: each pair once, in an order not stated, Go ranging over a map of managers),
with a `nil` object and an empty `ManagedFields`. There is no other outcome in the scope. The
inputs are only read.

Premises (`notes/smd-plan.md`, "Scope"; each checkable on what the caller holds):
- the updater: an identity converter, no ignored fields (`IgnoredFields` nil: required, a non-nil
  map without an entry at `version` makes SMD panic, `issues/smd-ignoredfields-missing-version-panic.md`)
  and no ignore filter (`IgnoreFilter` nil: a scope restriction; an empty non-nil map behaves the
  same, kept nil as the simpler statement);
- both objects of the schema at `sc` and of the type `t` (`isTV`: `typed.AsTyped`'s post, which
  carries the schema, `Schema.WF` and conformance);
- every manager's set at `version`: **required**, not only a saving. With managers at several
  versions SMD prunes per version (`addBackOwnedItems`, one pass per version in Go's map order,
  each from the previous pass's output), and a field owned at the applier's own version can be
  pruned (`issues/smd-apply-multiversion-prunes-owned.md`, Go-reproduced); with three or more
  versions the result depends on the map's order. A spec covering several versions needs a
  per-version `prune` with that nondeterminism;
- each set keeps list items with their key fields and has nothing below a key field
  (`keysWithItems`: every set SMD computes does; otherwise the pruning can strip a key field off an
  item it keeps, and SMD fails with an error that is not a conflict, or leaves two items with one
  key and reports a spurious conflict, or, forced, returns them as a non-conforming object:
  `nonissues/smd-apply-keyless-item-compare-error.md`). Decidable (`keysWithItemsB`).

Faithful, not repaired (`merge/Defs.lean`): a list item goes as a whole when its path is pruned,
even if another manager owns a field inside it (SSA-03); a container emptied by the pruning becomes
`null` (SSA-01/02); an applier's own struct whose only remaining content is an empty list is
deleted (`issues/smd-apply-deletes-own-struct.md`).

Lean-first (2026-11-19, notes/smd-plan.md); round 1's repairs 2026-11-19 (the third clause of
`keysWithItems`; the schema carried by `isTV`; the conflicts as a set).

D9 (2026-11-19, the Draft's integration): the workload premise `inputsSmall` (`merge/Defs.lean`), stated once here; the internal size premises of the stages and of the typed API follow from it (`merge/Laws.lean`).
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
abbrev merge.Updater.Apply.spec : Prop :=
  ∀ (u : Loc) (cv : merge.Converter) (rion : Bool) (sc : Loc) (S : Schema) (t : TypeRef)
    (lp cp : Loc) (live config : UVal) (ver : GoString) (mfm : GoMap) (mf : MF) (mgr : GoString)
    (force : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.merge ∗
      isUpdater u cv (zero_val GoMap) (zero_val GoMap) rion ∗ isIdentityConverter cv ∗
      isTV lp sc S t live ∗ isTV cp sc S t config ∗ isMF mfm mf ∗
      ⌜∀ m e, mf.get m = some e → e.version = ver ∧ keysWithItems S t e.set⌝ ∗
      ⌜inputsSmall [live, config] mf⌝ }}
    (App (App (App (App (App (App (Val (u @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.merge.Updater.ty @!! go!"Apply"))
      (Val #lp)) (Val #cp)) (Val #ver)) (Val #mfm)) (Val #mgr)) (Val #force))
  {{ (op : Loc) (mfm' : GoMap) (err : GoInterface), RET (PairV (PairV #op #mfm') #err);
      match applyResult S t rion live config ver mf mgr force with
      | .ok obj mf' => iprop(⌜err = interface.nil⌝ ∗ isMF mfm' mf' ∗
          match obj with
          | none => iprop(⌜op = null⌝)
          | some x => isTV op sc S t x)
      | .conflicts cs => iprop(⌜op = null⌝ ∗ isMF mfm' MF.none ∗
          ∃ (s : merge.Conflicts) (l : List (GoString × Path)),
            ⌜err = interface.mkOk _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.merge.Conflicts.ty #s ∧ l.Nodup ∧
              FSet.ofList l = cs⌝ ∗ isConflicts s l) }}

end spec

end smd
end EtcdGrove
end Perennial
