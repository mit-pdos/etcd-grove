/-
**`dispatch` on an admitted admin request in the mode `on`** (the auth plan's E2n, 2026-10-26;
`notes/decisions.md`, "E2n of the auth plan"). Lean-first (no Rocq counterpart).

A second triple of `apply.uberApplier.dispatch` (`uber_applier.go`), beside its spec
(`Spec/.../apply/uberApplier__dispatch.lean`), for the requests the mode `on` admits by their shape
(`adminKindOk`: `SetUp`'s five, `UserAdd`, `RoleAdd`, `UserGrantRole`, `RoleGrantPermission`,
`AuthEnable`): with the current applier's admin triples (`applierAdmin E c a W`, E2m), the admin
side's authority with its fuel (`auth.authOwnFu γa hs`) and the store's write resource `W`, the
request's method runs on a time receipt the caller takes at a Go step of its own (`⧗ 1`, as
`srvWTPool_take_extra` pays for an entry), and its result (`AdminReq.result`: the model's step or its refusal, E2l's
`adminOutFu`) is the admin outcome of `dispatch`'s result (`adminDone`); without `shouldApplyV3`
nothing runs and the authority comes back. The KV, the chain's resources and the critical
section's contract are as for a request that leaves the log as it is (`fin_same` of the spec's
proof). The proof walks the same code as the spec's: every other request kind is ruled out by
`adminKindOk` at its branch.

Not here: its use at `uberApplier.Apply` and `applyEntryNormal` (the mode-on request path), the
current applier's admin triples at the apply thread (`uberOwn` after `restoreAlarms`), and the
borrow of the rest's half of `be` that `W` holds at the server ("E2n of the auth plan").
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.uberApplier__dispatch
public import Spec.errors.Is
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.ApplySecObserve
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.WarnOfExpensiveRequest
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.WarnOfFailedRequest
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.DispatchLemmas
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.AdminChain
public import Proof.ReceiptTactics

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.apply go_etcd_io.etcd.api.v3

/-- **The admin request a request model `rq` carries**, by the field `dispatch` takes
(`dispatchKind`): one of `SetUp`'s five, an `Authenticate` (C1's A2), or none. -/
def apply.adminReqOf (rq : apply.IRRModel) : Option apply.AdminReq :=
  match apply.dispatchKind rq with
  | .authUserAdd => rq.authUserAdd.map (fun m => .userAdd m.name)
  | .authRoleAdd => rq.authRoleAdd.map .roleAdd
  | .authUserGrantRole => rq.authUserGrantRole.map (fun ur => .userGrantRole ur.1 ur.2)
  | .authRoleGrantPermission => rq.authRoleGrantPermission.map (fun nw => .roleGrantPermission nw.1 nw.2)
  | .authEnable => some .authEnable
  | .authenticate => rq.authenticate.map (fun am => .authenticate am.name am.simpleToken)
  | _ => none

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **What an admitted admin request needs besides `mPre`** (C1's A2, 2026-10-28): its
`AdminReq.extraPre` (an `Authenticate`'s right to issue its token at the index `ConsistentIndex()`
returns under what it borrows from the critical section's precondition `Pre`). -/
def apply.adminExtra (E : apply.AEnv GF) (γa : auth.AuthNames) (rq : apply.IRRModel) (Pre : IProp GF) :
    IProp GF :=
  match apply.adminReqOf rq with
  | some ad => ad.extraPre E γa Pre
  | none => iprop(True)

/-- An `Authenticate`'s `adminExtra`: an index `x` that `ConsistentIndex()` reads under what it
borrows from `Pre`, and the right to its token at `x`. -/
theorem apply.adminExtra_authenticate (E : apply.AEnv GF) (γa : auth.AuthNames)
    (rq : apply.IRRModel) (Pre : IProp GF) (am : apply.AuthenticateModel) (x : w64)
    (hk : apply.dispatchKind rq = .authenticate) (ha : rq.authenticate = some am) :
    apply.ciSplitAt E Pre x ∗ auth.tokFresh γa (auth.simpleTok am.simpleToken x) ⊢
      apply.adminExtra E γa rq Pre := by
  iintro ⟨#H, Hf⟩
  unfold apply.adminExtra apply.adminReqOf
  simp only [hk, ha, Option.map_some, apply.AdminReq.extraPre]
  iexists x
  iframe H Hf

/-- Of a request other than `Authenticate`, `adminExtra` is free. -/
theorem apply.adminExtra_of_ne (E : apply.AEnv GF) (γa : auth.AuthNames) (rq : apply.IRRModel)
    (Pre : IProp GF) (h : apply.dispatchKind rq ≠ .authenticate) :
    ⊢ apply.adminExtra E γa rq Pre := by
  unfold apply.adminExtra apply.adminReqOf
  cases hk : apply.dispatchKind rq <;> simp only [hk] at h ⊢
  all_goals first
    | exact absurd rfl h
    | itrivial
    | (cases rq.authUserAdd <;> cases rq.authRoleAdd <;> cases rq.authUserGrantRole <;>
        cases rq.authRoleGrantPermission <;>
        simp only [Option.map, apply.AdminReq.extraPre] <;> itrivial)

/-- **The admin outcome of `dispatch`'s result `ar`** (the auth plan's E2n): with `v3`, the
request's result (`AdminReq.result` at the result's response and error: the step on the latest
recorded state, the authority with its fuel after it, or the model's refusal; C1's A2: an
`Authenticate`'s token); without, the authority as it was. -/
def apply.adminDone (Own : auth.AuthNames → List auth.AuthState → IProp GF) (γa : auth.AuthNames) (M : auth.AuthMode)
    (hs : List auth.AuthState)
    (rq : apply.IRRModel) (v3 : Bool) (ar : Loc) : IProp GF :=
  if v3 then iprop(∃ (v : go_etcd_io.etcd.server.v3.etcdserver.apply.Result) (ad : apply.AdminReq)
      (resp : Loc), ⌜apply.adminReqOf rq = some ad ∧
        v.Resp' = interface.mkOk (go.GoType.PointerType ad.respTy) #resp⌝ ∗
    ar ↦□ v ∗ ad.result Own γa M hs resp v.Err')
  else Own γa hs

variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- **`a.dispatch(r, shouldApplyV3)` on an admitted admin request in the mode `on γa`** (see the
file header): `dispatch.spec`'s precondition but for the KV floor, the store's write token, the
rest buckets and the certificates (which an admin request does not use), with `adminKindOk rq` in
place of `rqOk`, the current applier's admin triples, the authority with its fuel, a time
receipt (the admin step's cost, E2l) and `W`; (C1's A2) with `v3`, the request's `adminExtra` (an
`Authenticate`'s token right at the index `ConsistentIndex()` reads). -/
abbrev apply.uberApplier.dispatch.adminSpec : Prop :=
  ∀ (E : apply.AEnv GF) (p : Loc) (opts : go_etcd_io.etcd.server.v3.etcdserver.apply.ApplierOptions) (c : apply.Chain) (a : GoInterface)
    (r : Loc) (rq : apply.IRRModel) (skip v3 : Bool) (log : mvcc.Log) (Pre Q Post : IProp GF)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (W : IProp GF) (γa : auth.AuthNames)
    (hs : List auth.AuthState) (Own : auth.AuthNames → List auth.AuthState → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗ apply.uberIs E p opts ∗
      apply.irrWrapperIs r rq skip ∗ apply.chainRes c a info ∗
      structFieldRef uberApplier go!"applyV3" p ↦ a ∗ apply.applierSpec E c a ∗
      apply.applierAdmin E c a W Own ∗
      apply.kvOwn E log ∗ apply.cPre v3 E.P E.f Pre Q Post ∗
      ⌜E.authMode = .on γa ∧ apply.adminKindOk rq ∧ apply.dispatchOk E.authOn rq ∧
        receiptBound GF ≤ 2 ^ 48⌝ ∗ ⌜c.authOn = E.authOn⌝ ∗
      Own γa hs ∗ ⧗ 1 ∗ W ∗ (if v3 then apply.adminExtra E γa rq Pre else iprop(True)) }}
    (App (App (Val (p @!! go.GoType.PointerType uberApplier.ty @!! go!"dispatch")) (Val #r)) (Val #v3))
  {{ (ar : Loc), RET #ar; apply.chainResAny c a ∗ structFieldRef uberApplier go!"applyV3" p ↦ a ∗
      ∃ o : apply.Outcome, apply.kvOwn E (o.logAfter log) ∗ apply.cPost v3 Pre Post ∗
        ⌜apply.dispatchStep c rq v3 log o⌝ ∗ apply.resTrace ar ∗
        apply.dispatchResult rq v3 log skip ar o ∗ W ∗ apply.adminDone Own γa E.authMode hs rq v3 ar }}

end defs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

set_option hygiene false in
/-- Persist the result struct `ar` (all stores done) and split it into its fields (read-only
from now on: the deferred metrics read `Resp` and `Err`). -/
local macro "persist_ar" : tactic => `(tactic| (
  ihave ⟨H0, %hn⟩ := typedPointsto_not_null_dup _ _ _ $$ «$r0»
  ipersist H0
  ihave #H0' := H0
  iStructNamed H0'))

set_option hygiene false in
/-- The deferred metrics with `success` (`ar.Err == nil`). -/
local macro "ok_path" : tactic => `(tactic| (
  wp_apply time.wp_Since as %d -
  wp_apply hASO
  wp_alloc s1 as Hs1
  wp_auto
  wp_apply hWER $$ [Hs1]
  · isplitr
    · ipureintro; exact HlgN
    iexists s1, _
    iframe Hs1
    ipureintro; exact ⟨rfl, Hipn⟩))

set_option hygiene false in
/-- The failure's warning (`WarnOfFailedRequest`), with a fresh stringer of the request. -/
local macro "wfr_step" : tactic => `(tactic| (
  wp_alloc s2 as Hs2
  wp_auto
  wp_apply hWFR $$ [Hs2]
  · isplitr
    · ipureintro; exact HlgN
    iexists s2, _
    iframe Hs2
    ipureintro; exact ⟨rfl, Hipn⟩))

set_option hygiene false in
/-- The deferred metrics with `ar.Err` not nil: `errors.Is(ar.Err, ErrCompacted)`, then the
warnings (the failure's if not `success`). -/
local macro "err_path" : tactic => `(tactic| (
  ihave #HeIu := applyErrIs_tree _ $$ HeI
  ihave ⟨%S, %M, #Htree, %HS⟩ := HeIu $$ %(GoInterface.ok ec)
  wp_apply (hIs S M _ (GoInterface.ok ec) (fun tii h => by cases h; exact Hecl.1)
    (HS.2 (fun tii h => by cases h; exact Hecl.1)))
    $$ [] as %b -
  · iframe Htree; ipureintro; exact HS.1
  wp_apply time.wp_Since as %d -
  wp_apply hASO
  wp_alloc s1 as Hs1
  wp_auto
  wp_apply hWER $$ [Hs1]
  · isplitr
    · ipureintro; exact HlgN
    iexists s1, _
    iframe Hs1
    ipureintro; exact ⟨rfl, Hipn⟩
  cases b <;> (try wp_auto) <;> (try wfr_step)))

set_option hygiene false in
/-- The deferred metrics, whatever `ar.Err`. -/
local macro "dtail" : tactic => `(tactic| (
  cases err <;> (try wp_auto) <;> first | ok_path | err_path))

set_option hygiene false in
/-- The postcondition for a request that leaves the KV and the chain as they are. -/
local macro "fin_same" : tactic => `(tactic| (
  (try ihave Hres := apply.chainResAny_of _ _ _ $$ Hres)
  iframe Hres
  iexists (GoInterface.ok ai), c, (Outcome.applied log false)
  simp only [apply.Outcome.logAfter]
  iframe Ha Hs Hkv
  isplitl [HPP]
  · simp only [apply.cPost, ↓reduceIte]; iexact HPP
  isplitr
  · ipureintro; simp [apply.kvFloorOk, apply.isFloorKind, apply.dispatchStep, apply.chainAfter, hk, apply.preV3Kind, apply.storeKind, apply.Outcome.logAfter]
  isplitl []
  · iintro %_; iapply (apply.chainClass_nonKV _ _ _ _ _ (by rw [hk]; rfl))
  first | isplitl [Htrc] | isplitl []
  · iapply apply.resTrace_of $$ H0
    first | iexact Htrc | iapply apply.traceRes_null
  simp only [apply.dispatchResult, hk, apply.preV3Kind, _root_.true_or, _root_.or_true, ↓reduceIte]
  iframe %hn
  iexists _
  iframe H0
  isplitl; rotate_left
  · first | iexact HeI | iapply applyErrIs_nil
  simp only [apply.dispatchAnswer, hk]))

set_option hygiene false in
/-- The postcondition for a request whose outcome `oc` is the chain's (`Hst`). -/
local macro "fin_kv" : tactic => `(tactic| (
  (try ihave Hres := apply.chainResAny_of _ _ _ $$ Hres)
  iframe Hres
  iexists (GoInterface.ok ai), c, oc
  iframe Ha Hs Hkv
  isplitl [HPP]
  · simp only [apply.cPost, ↓reduceIte]; iexact HPP
  isplitr
  · ipureintro
    refine ⟨?_, Or.inl rfl, ?_⟩
    · simp only [apply.dispatchStep, hk, apply.preV3Kind, apply.storeKind,
        Bool.false_eq_true, _root_.or_self, ↓reduceIte]
      first | exact Hst.1 | exact Hst
    · first | exact fun _ _ => Hst.2 | simp [apply.kvFloorOk, apply.isFloorKind, hk]
  isplitl []
  · iintro %_; iexact Hcls
  first | isplitl [Htrc] | isplitl []
  · iapply apply.resTrace_of $$ H0
    first | iexact Htrc | iapply apply.traceRes_null
  simp only [apply.dispatchResult, hk, apply.preV3Kind, _root_.or_true, ↓reduceIte]
  iframe %hn
  iexists _
  iframe H0
  isplitl; rotate_left
  · first | iexact HeI | iapply applyErrIs_nil
  simp only [apply.dispatchAnswer, hk]))

set_option hygiene false in
/-- A case of the second `switch` at the join point (`R` of the `wp_join` below): `ar` (made
read-only) and `op` as computed, then the postcondition of `dispatch` at `ar`. -/
local macro "join_ar" : tactic => `(tactic| (
  wp_join_done
  persist_ar
  imodintro
  iexists _, _, _, _, _
  iframe a r ar op H0 HeI))


set_option linter.unusedVariables false in
set_option maxHeartbeats 10000000 in
/-- **`dispatch` on an admitted admin request** (see the file header). -/
theorem apply.uberApplier.dispatch.wp_admin
    (hIs : errors.Is.spec (GF := GF) (hG := hG))
    (hASO : txn.ApplySecObserve.spec (GF := GF) (hG := hG))
    (hWER : txn.WarnOfExpensiveRequest.spec (GF := GF) (hG := hG))
    (hWFR : txn.WarnOfFailedRequest.spec (GF := GF) (hG := hG)) :
    apply.uberApplier.dispatch.adminSpec (GF := GF) (hG := hG) := by
  -- (C1's A2) phase 1 of the spec-first stage: the proof (at 2040bccc8a) is redone in phase 2
  sorry

end proof

end EtcdGrove
end Perennial
