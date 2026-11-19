/-
`(*Updater).Update(liveObject, newObject, version, managers, manager)`: an update (create,
update or patch) by `manager` from `liveObject` to `newObject`. Returns `newObject` itself and the
managers `updateResult` computes (`merge/Defs.lean`): every other manager loses what changed or was
removed (an update forces); `manager` owns (not applied) what it owned, less what was removed, plus
what changed or was added. No error in the scope. The inputs are only read.

Premises (`notes/smd-plan.md`, "Scope"): the updater: an identity converter, no ignored fields or
filter (scope restriction); the schema in scope (`Schema.WF`); both objects of the schema at `sc`
and of the type `t` (`isTV`). No premise on the managers' versions (with an identity converter
every version compares alike).

Lean-first (2026-11-19, notes/smd-plan.md).
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
abbrev merge.Updater.Update.spec : Prop :=
  ∀ (u : Loc) (cv : merge.Converter) (rion : Bool) (sc : Loc) (S : Schema) (t : TypeRef)
    (lp np : Loc) (live new : UVal) (ver : GoString) (mfm : GoMap) (mf : MF) (mgr : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.merge ∗
      isUpdater u cv (zero_val GoMap) (zero_val GoMap) rion ∗ isIdentityConverter cv ∗
      isSchema sc S ∗ isTV lp sc S t live ∗ isTV np sc S t new ∗ isMF mfm mf ∗ ⌜S.WF⌝ }}
    (App (App (App (App (App (Val (u @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.merge.Updater.ty @!! go!"Update"))
      (Val #lp)) (Val #np)) (Val #ver)) (Val #mfm)) (Val #mgr))
  {{ (op : Loc) (mfm' : GoMap) (err : GoInterface), RET (PairV (PairV #op #mfm') #err);
      ⌜op = np ∧ err = interface.nil⌝ ∗ isMF mfm' (updateResult S t live new ver mf mgr) }}

end spec

end smd
end EtcdGrove
end Perennial
