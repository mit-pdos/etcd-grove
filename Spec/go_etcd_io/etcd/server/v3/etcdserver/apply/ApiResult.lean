/-
# etcd's apply layer (batch 3a): the result and the uber-applier's contract

The part of the vocabulary that names 2c's result predicate (`EtcdServer.applyResult`, over 2c's
`IrrBody`): what a member's `*apply.Result` holds, and the bundle of the uber-applier's `Apply`
method that `apply.Apply`'s interface call uses (`isUber_apply`, the approved shape of
`.claude/skills/spec/examples/apply-uber-contract.md`). Kept apart from `Api.lean` so that the model
does not depend on the request path's vocabulary.

* `opBody op` (transparent): 2c's model of the request (`IrrBody`): a client request as itself
  (a hashed user change with the hash in the password's place: its reply does not depend on it), a
  token as `.authToken`, an alarm `GET` as `.alarmList`, an activation as `.alarmActivate`, a
  deactivation as `.alarmDisarm`, a publication as `.publish`, the rest as `.noop`.
* `resultAt γ ar ir sk res` (transparent): **`ar` is the result of applying `ir` with the step's
  answer `res`**: `nil` with the placeholder answer (the replay), or 2c's `applyResult` of an answer
  `res'` with `resMatch` (`Api.lean`: the answer itself, an alarm list in another order, a skipped
  transaction's ranges empty, the quota's `ErrNoSpace` after a write it applied).
* `replyAt_result` (law): a method's reply is the result's `Resp` and `Err`.
* `isUber_apply` (law): the uber-applier's `Apply` as the interface method `apply.Apply` calls.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.Api
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiReq

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Apply

open Iris Iris.BI EtcdModel Classical

/-- 2c's model of the request (see the header). -/
def opBody : IrrOp → EtcdServer.IrrBody
  | .req rq => .req rq
  | .userAdd name h np => .req (.userAdd name h np)
  | .userChangePassword name h => .req (.userChangePassword name h)
  | .authenticate name _ => .authToken name
  | .alarm .get _ _ => .req .alarmList
  | .alarm .activate mid at' =>
      match V3alarm.kindOf at' with
      | some k => .alarmActivate ⟨mid, k⟩
      | none => .noop
  | .alarm .deactivate mid at' =>
      match V3alarm.kindOf at' with
      | some k => .req (.alarmDisarm ⟨mid, k⟩)
      | none => .noop
  | .memberAttrSet id name urls => .publish id name urls
  | _ => .noop

section vocab
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors}
  [hG : HeapGS HasLC.hasLC GF] [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- **`ar` is the result of applying `ir`** (skipping its ranges if `sk`), whose step answered
`res`. -/
def resultAt (γ : Cluster) (ar : Loc) (ir : Irr) (sk : Bool) (res : Resp) : IProp GF :=
  iprop(⌜ar = null ∧ res = noAns⌝ ∨
    ∃ res', ⌜resMatch ir.op sk res res'⌝ ∗ EtcdServer.applyResult γ ar (opBody ir.op) res')

end vocab

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors}
  [hG : HeapGS HasLC.hasLC GF] [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- **A method's reply is a result's `Resp` and `Err`** (`dispatch` stores them): the reply of the
answer (`nil` error), or the answer's server-side error. -/
def replyAt_result.spec : Prop :=
  ∀ (γ : Cluster) (op : IrrOp) (res : Resp) (resp err : GoInterface),
    replyAt (GF := GF) γ op res resp err ⊢
      match res with
      | .ok _ => iprop(⌜err = GoInterface.nil⌝ ∗ EtcdServer.irrReply γ (opBody op) res resp)
      | .err e => iprop(⌜EtcdServer.srvErrOf err e⌝)

/-- **The uber-applier's `Apply`, as the interface method** (`isUber`'s bundle; the concrete spec is
`uberApplier.Apply.spec`): from the state machine at `σ`, with the lent `R` and the membership
update, the state machine at the step's `σ'` and the result of its answer. -/
def isUber_apply.spec : Prop :=
  ∀ (ua : GoInterface) (mc : MemberCfg) (γ : Cluster) (γc : Membership.CNames) (R : IProp GF),
    isUber ua mc γ γc R ⊢
      ∃ ui : GoInterfaceOk, ⌜ua = GoInterface.ok ui⌝ ∗
        □ ∀ (r : Loc) (ir : Irr) (sk v3 : Bool) (σ : State) (Qm : IProp GF),
          {{ wrapperAt r ir sk ∗ ⌜ir.op.ok ∧ (sk = true → ir.op.isTxn = true)⌝ ∗ smAt ua σ ∗
              memberUpd γc ir Qm ∗ R }}
            (App (App (Val #(methods ui.ty go!"Apply" ui.v)) (Val #r)) (Val #v3))
          {{ (ar : Loc), RET #ar; R ∗ Qm ∗ ∃ σ' res, ⌜irrStep mc σ ir v3 σ' res⌝ ∗ smAt ua σ' ∗
              resultAt γ ar ir sk res }}

end laws

end Apply
end EtcdGrove
end Perennial
