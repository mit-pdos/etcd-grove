/-
`(*Updater).Update(liveObject, newObject, version, managers, manager)`: an update (create, update
or patch). Returns `newObject` itself and the managers the model `updateObj` computes
(`updatePost`): `manager` owns (not applied) what it owned less what was removed, plus what changed
or was added; every other manager loses what changed or was removed (an update forces); or an
error, with a `nil` object and an empty `ManagedFields`. The schema's lazy indexes are threaded
through; the inputs are only read.

Premises (what the model covers, `Model/Merge.lean`'s header): the updater's converter is the
identity on one API version, it has no ignored fields or filter (`ownUpdater`); every manager's
set is at the request's version `version`; the objects' type is a named type (whose map types'
indexes `ownSchema` owns) and the schema's associative lists have distinct key names
(`Schema.keysNodup`); the live and new objects are of the schema `sc` (one pointer: `Compare`
and `merge` check it) and of one type (else the model's error); and the model does not panic on
these inputs (it panics exactly where Go does, on a nil `value.Value`, which `merge` returns when
its walker's output is nil: never for a live object that is a non-empty map).

Lean-first (2026-11-19, notes/smd-robustness.md).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.merge.Base
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
abbrev merge.Updater.Update.spec : Prop :=
  ∀ (u : Loc) (rion : Bool) (sc : Loc) (S : Schema) (lp np : Loc) (live new : TV)
    (ver : GoString) (mfm : GoMap) (mf : MF) (manager : GoString),
  (∀ e ∈ mf, e.2.version = ver) → live.typeRef.namedType.isSome = true → S.keysNodup = true →
  (match updateObj S live new ver mf manager with | .panic => False | _ => True) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.merge ∗ ownUpdater u rion ∗ ownSchema sc S ∗ ownTV lp sc live ∗ ownTV np sc new ∗
      ownMF mfm mf }}
    (App (App (App (App (App (Val (u @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.merge.Updater.ty @!! go!"Update"))
      (Val #lp)) (Val #np)) (Val #ver)) (Val #mfm)) (Val #manager))
  {{ (op : Loc) (mfm' : GoMap) (err : GoInterface), RET (PairV (PairV #op #mfm') #err);
      ownSchema sc S ∗ updatePost (updateObj S live new ver mf manager) np op mfm' err }}

end spec

end smd
end EtcdGrove
end Perennial
