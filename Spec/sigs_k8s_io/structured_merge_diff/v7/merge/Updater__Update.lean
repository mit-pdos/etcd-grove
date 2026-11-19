/-
`(*Updater).Update(liveObject, newObject, version, managers, manager)`: an update (create,
update or patch) by `manager` from `liveObject` to `newObject`. Returns `newObject` itself and the
managers `updateResult` computes (`merge/Defs.lean`): every other manager loses what changed or was
removed (an update forces); `manager` owns (not applied) what it owned, less what was removed, plus
what changed or was added. No error in the scope. The inputs are only read.

Premises (`notes/smd-plan.md`, "Scope"): the updater: an identity converter, no ignored fields
(required: see `Updater.Apply`) or filter (scope restriction); both objects of the schema at `sc`
and of the type `t` (`isTV`, which carries the schema and `Schema.WF`). No premise on the
managers' versions (with an identity converter every version compares alike: Go-checked on 26000
updates with mixed versions, review round 1) and none on their sets.

Lean-first (2026-11-19, notes/smd-plan.md); round 1's repairs 2026-11-19 (the schema carried by
`isTV`).

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
abbrev merge.Updater.Update.spec : Prop :=
  ∀ (u : Loc) (cv : merge.Converter) (rion : Bool) (sc : Loc) (S : Schema) (t : TypeRef)
    (lp np : Loc) (live new : UVal) (ver : GoString) (mfm : GoMap) (mf : MF) (mgr : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.merge ∗
      isUpdater u cv (zero_val GoMap) (zero_val GoMap) rion ∗ isIdentityConverter cv ∗
      isTV lp sc S t live ∗ isTV np sc S t new ∗ isMF mfm mf ∗ ⌜inputsSmall [live, new] mf⌝ }}
    (App (App (App (App (App (Val (u @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.merge.Updater.ty @!! go!"Update"))
      (Val #lp)) (Val #np)) (Val #ver)) (Val #mfm)) (Val #mgr))
  {{ (op : Loc) (mfm' : GoMap) (err : GoInterface), RET (PairV (PairV #op #mfm') #err);
      ⌜op = np ∧ err = interface.nil⌝ ∗ isMF mfm' (updateResult S t live new ver mf mgr) }}

end spec

end smd
end EtcdGrove
end Perennial
