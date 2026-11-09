/-
# etcd's apply layer (batch 3a): the result and the uber-applier's contract

The part of the vocabulary that names 2c's result predicate (`EtcdServer.applyResult`, over 2c's
`IrrBody`): what a member's `*apply.Result` holds, and the bundle of the uber-applier's `Apply`
method that `apply.Apply`'s interface call uses (`isUber_apply`, the approved shape of
`.claude/skills/spec/examples/apply-uber-contract.md`). Kept apart from `Api.lean` so that the model
does not depend on the request path's vocabulary.

* `opBody op b` (transparent): 2c's model of the request (`IrrBody`): a client request as itself
  (a user change with the credential `h` as the client's request with a password `h` is a hash of,
  W0's `pwHash`: its reply does not depend on it), a
  token as `.authToken`, an alarm `GET` as `.alarmList`, an activation as `.alarmActivate`, a
  deactivation as `.alarmDisarm`, a publication as `.publish`, the rest as `.noop`.
* `resultAt γ ar ir sk res` (transparent): **`ar` is the result of applying `ir` with the step's
  answer `res`**: `nil` with the placeholder answer (the replay), or 2c's `applyResult` of an answer
  `res'` with `resMatch` (`Api.lean`: the answer itself, an alarm list in another order, a skipped
  transaction's ranges empty, the quota's `ErrNoSpace` after a write it applied), or, for a token
  assignment, the token provider's error (`provErrResult`: the coordinator's decision, I5).
* `checksOut C cs err`, `chkExact`, `chkPost` (internal): the permission checks' outcome, each
  check reported by `C` (the writer's exact `checkErr`, or 3d's `checkPost` for the request path);
  the laws `permReads_writer`, `permReads_reader` give `permReads`' two instances.
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

/-- 2c's model of the request (3h's `EtcdServerPb.IrrBody`, see the header). -/
def opBody (op : IrrOp) (b : EtcdServer.IrrBody) : Prop :=
  match op with
  | .req rq => b = .req rq
  | .userAdd name h np => ∃ pw, (np = false → pwHash pw h) ∧ b = .req (.userAdd name pw np)
  | .userChangePassword name h => ∃ pw, pwHash pw h ∧ b = .req (.userChangePassword name pw)
  | .authenticate name _ _ => b = .authToken name
  | .alarm .get _ at' => if at' = W32 0 then b = .req .alarmList else b = .noop
  | .alarm .activate mid at' =>
      match V3alarm.kindOf at' with
      | some k => b = .alarmActivate ⟨mid, k⟩
      | none => b = .noop
  | .alarm .deactivate mid at' =>
      match V3alarm.kindOf at' with
      | some k => b = .req (.alarmDisarm ⟨mid, k⟩)
      | none => b = .noop
  | .memberAttrSet id name urls => b = .publish id name urls
  | _ => b = .noop

section vocab
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors}
  [hG : HeapGS HasLC.hasLC GF] [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- **A result carrying a token provider's error** (`Authenticate`'s apply, whose step answered
`.ok .authenticate`; the coordinator's decision, integration I5): 2c's `applyResult`'s fields with a
non-`nil` `Err` that need be no etcd error: the no-op provider's `assign` always fails
(`ErrAuthFailed`), JWT's on a signing error (any error, `jwt.go:107-115`) or `ErrVerifyOnly`. The
state is unchanged and no token is assigned. -/
def provErrResult (ar : Loc) : IProp GF :=
  iprop(⌜ar ≠ null⌝ ∗ ∃ (resp : GoInterface) (err : GoInterface) (ph : Loc) (tr : Loc),
    ar.[go_etcd_io.etcd.server.v3.etcdserver.apply.Result, go!"Resp"] ↦□ resp ∗
    ar.[go_etcd_io.etcd.server.v3.etcdserver.apply.Result, go!"Err"] ↦□ err ∗
    ar.[go_etcd_io.etcd.server.v3.etcdserver.apply.Result, go!"Physc"] ↦□ ph ∗
    ar.[go_etcd_io.etcd.server.v3.etcdserver.apply.Result, go!"Trace"] ↦□ tr ∗
    TraceUtil.traceOpt tr ∗ (⌜ph = null⌝ ∨ Read.recvAny ph) ∗ ⌜err ≠ GoInterface.nil⌝)

/-- **`ar` is the result of applying `ir`** (skipping its ranges if `sk`), whose step answered
`res`: `nil` (the replay), 2c's `applyResult` of an answer `resMatch`ing `res`, or, for a token
assignment the step answered, the token provider's error (`provErrResult`). -/
def resultAt (γ : Cluster) (ar : Loc) (ir : Irr) (sk : Bool) (res : Resp) : IProp GF :=
  iprop(⌜ar = null ∧ res = noAns⌝ ∨
    (∃ res' b, ⌜resMatch ir.op sk res res' ∧ opBody ir.op b⌝ ∗ EtcdServer.applyResult γ ar b res') ∨
    (⌜ir.op.isAuthn = true ∧ res = .ok .authenticate⌝ ∗ provErrResult ar))

/-- **The outcome of the permission checks `cs`**, each check's answer reported by `C`
(`permReads`): `nil` and every check passing, or the error of a failing check `cs[i]` after the
earlier ones passed. -/
def checksOut (C : Check → GoInterface → IProp GF) (cs : List Check) (err : GoInterface) :
    IProp GF :=
  iprop((⌜err = GoInterface.nil⌝ ∗ [∗list] c ∈ cs, C c GoInterface.nil) ∨
    ∃ (i : Nat) (c : Check), ⌜cs[i]? = some c ∧ err ≠ GoInterface.nil⌝ ∗ C c err ∗
      [∗list] c' ∈ cs.take i, C c' GoInterface.nil)

/-- **The apply thread's report of a check** at the auth info `u`, `rev`: exactly `checkErr` at
the stores' one state `σ` (`nil` for a pass, the server error of the refusal: 2c's `srvErr`, the
sentinel's global value; second pass, was the deprecated pure `srvErrOf`). -/
def chkExact (σ : State) (u : GoString) (rev : Nat) (c : Check) (err : GoInterface) : IProp GF :=
  iprop(⌜err = GoInterface.nil ∧ checkErr σ u rev c = none⌝ ∨
    (∃ e, ⌜checkErr σ u rev c = some e⌝ ∗ EtcdServer.srvErr err e))

/-- **What one check of the request path reports** (3d's `Auth.checkPost`, from the lower bound
`i0`): an operation's check with its recorded states (a denial with the states it failed at); a
lease's keys: nothing when it passes, the failing key's write check when it does not. -/
def chkPost (γa : Auth.AuthNames) (i0 : Nat) (u : GoString) (rev : w64) (c : Check)
    (err : GoInterface) : IProp GF :=
  match c with
  | .op t rng => Auth.checkPost γa i0 u rev t rng err
  | .lease _ => iprop(⌜err = GoInterface.nil⌝ ∨ ∃ rng, Auth.checkPost γa i0 u rev .write rng err)

end vocab

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors}
  [hG : HeapGS HasLC.hasLC GF] [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- **A method's reply is a result's `Resp` and `Err`** (`dispatch` stores them): the reply of the
answer (`nil` error), or the answer's server-side error; for a token assignment answered
`.ok .authenticate`, also the token provider's error (any non-`nil` error: `provErrResult`). -/
def replyAt_result.spec : Prop :=
  ∀ (γ : Cluster) (op : IrrOp) (res : Resp) (resp err : GoInterface),
    replyAt (GF := GF) γ op res resp err ⊢
      match res with
      | .ok _ => iprop((⌜err = GoInterface.nil⌝ ∗ ∃ b, ⌜opBody op b⌝ ∗ EtcdServer.irrReply γ b res resp) ∨
          ⌜op.isAuthn = true ∧ res = .ok .authenticate ∧ err ≠ GoInterface.nil⌝)
      | .err e => iprop(EtcdServer.srvErr err e ∗ EtcdServer.srvErrShape err)

/-- (internal) **A method's reply message lends what the deferred warnings size** (`dispatch`'s
`warnOfExpensiveRequest(..., ar.Resp, ar.Err)`, 3b's `WarnOfExpensiveRequest` takes `msgOpt`): the
`*pb.<Kind>Response` a method built (a fresh message, its depth below protobuf's bound) or a typed
`nil` on an error, lent and given back (verify-round A9, second tier: the depth fact was looked for
in 2c's `irrReply`, which says nothing of a `.noop`'s reply). -/
def replyAt_msgOpt.spec : Prop :=
  ∀ (γ : Cluster) (op : IrrOp) (res : Resp) (resp err : GoInterface),
    replyAt (GF := GF) γ op res resp err ⊢
      ∃ m, Txn.msgOpt resp m ∗ (Txn.msgOpt resp m -∗ replyAt γ op res resp err)

/-- **The apply thread's permission checks** (internal): through the options' auth store and
lessor, lending the stores at `σ`, each check is answered exactly (`chkExact`): the writer's views
are all at its state (3d's `authCur_at`, `authAt_le`; 3c's `lessorState_le`). -/
def permReads_writer.spec : Prop :=
  ∀ (b : Loc) (mc : MemberCfg) (γ : Cluster) (γc : Membership.CNames) (R : IProp GF)
    (o : go_etcd_io.etcd.server.v3.etcdserver.apply.ApplierOptions) (σ : State) (u : GoString)
    (rev : w64),
    beAt (GF := GF) b mc γ γc R ∗ beOpts b o ⊢
      permReads o.AuthStore' o.Lessor' u rev (stAt b σ) true (chkExact σ u (uint.nat rev))

/-- **The request path's permission checks** (internal; `CheckTxnAuth`): through a member's auth
store read from the lower bound `i0`, no lease check, each operation's check reported by 3d's
`checkPost` (`chkPost`). -/
def permReads_reader.spec : Prop :=
  ∀ (st : Loc) (γ : Cluster) (γa : Auth.AuthNames) (i0 : Nat) (le : GoInterface) (u : GoString)
    (rev : w64),
    Auth.authStoreAt (GF := GF) st γ γa ∗ Auth.authLb γa i0 ⊢
      permReads (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.authStore.ty)
        #st) le u rev emp false (chkPost γa i0 u rev)

/-- **The uber-applier's `Apply`, as the interface method** (`isUber`'s bundle; the concrete spec is
`uberApplier.Apply.spec`): from the state machine at `σ`, with the lent `R` and the membership
update, the state machine at the step's `σ'` and the result of its answer. -/
def isUber_apply.spec : Prop :=
  ∀ (ua : GoInterface) (mc : MemberCfg) (γ : Cluster) (γc : Membership.CNames) (R : IProp GF),
    isUber ua mc γ γc R ⊢
      ∃ ui : GoInterfaceOk, ⌜ua = GoInterface.ok ui⌝ ∗
        □ ∀ (r : Loc) (ir : Irr) (sk v3 : Bool) (σ : State) (Qm : IProp GF),
          {{ wrapperAt r ir sk ∗ ⌜ir.op.ok ∧ (sk = true → ir.op.isTxn = true)⌝ ∗ smAt ua σ ∗
              nextOk γ R ir.op (fun σ' => ∃ res, irrStep mc σ ir v3 σ' res) ∗
              memberUpd γc ir.op Qm ∗ R ∗ threadTok }}
            (App (App (Val #(methods ui.ty go!"Apply" ui.v)) (Val #r)) (Val #v3))
          {{ (ar : Loc), RET #ar; R ∗ threadTok ∗ Qm ∗ ∃ σ' res, ⌜irrStep mc σ ir v3 σ' res ∧
        (v3 = false → ir.op.isMembership = false →
          (ir.op.needAdmin = true → adminErr σ.auth ir.user = none) → ar = null)⌝ ∗ smAt ua σ' ∗
              resultAt γ ar ir sk res }}

end laws

end Apply
end EtcdGrove
end Perennial
