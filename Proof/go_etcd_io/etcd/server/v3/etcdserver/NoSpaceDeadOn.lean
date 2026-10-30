/-
**`applyEntryNormal`'s NOSPACE branch is dead with auth on** (the auth plan's E3i, 2026-10-27;
E3f's blocker 2). Lean-first (no Rocq counterpart).

At the start's chain with auth off (`NoSpaceDead.lean`, D19k) a covered request's result error is
`nil` or one of the backend's `errors.New` variables, none of them `ErrNoSpace`'s. With auth on
(`alarmChain true false false`) the auth layer may also refuse it (`.rejected .auth`), with the
auth store's error: since E3i stated over the auth package's error variables (`apply.rejErrIs`'
`authApplyErrIs`: `authErrVarIs`, a leaf error of a variable of `auth.authErrMsgs`), which the
apply package's facts tell apart from `ErrNoSpace` (`applyErrVars`' `authErrsApart`, from the
variables' message cells). Every other outcome is the auth-off chain's (`dispatchStep_on_off`), so
`NoSpaceDead`'s lemmas apply to it.

Not covered: an admin entry's result (the admin path's errors, `apply.Apply.adminSpecL`), which
`applyEntryNormal`'s admin case with auth on will need too.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.NoSpaceDead

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

/-- **A dispatch at the start's chain with auth on is the auth layer's refusal or the auth-off
chain's.** -/
theorem dispatchStep_on_off (rq : apply.IRRModel) (log : mvcc.Log) (o : apply.Outcome)
    (h : apply.dispatchStep (apply.alarmChain true false false) rq true log o) :
    o = .rejected .auth ∨ apply.dispatchStep (apply.alarmChain false false false) rq true log o := by
  unfold apply.dispatchStep at h ⊢
  split at h
  · rename_i hc; simp only [hc, ↓reduceIte]; exact Or.inr h
  rename_i hc
  simp only [hc, ↓reduceIte]
  split at h
  · rename_i hs
    simp only [hs, ↓reduceIte]
    simp only [apply.alarmChain, apply.baseChain, Bool.false_eq_true, ↓reduceIte,
      apply.chainStep] at h ⊢
    by_cases ha : (apply.authChecks (apply.dispatchKind rq) = true ∨
      apply.needAdminPermission rq = true)
    · simp only [ha, ↓reduceIte] at h ⊢
      rcases h with ⟨-, rfl⟩ | h
      · exact Or.inl rfl
      · exact Or.inr (Or.inr h)
    · simp only [ha, ↓reduceIte] at h ⊢
      exact Or.inr h
  · rename_i hs; simp only [hs, ↓reduceIte]; exact Or.inr h

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- An auth-package error, told apart from `ErrNoSpace`'s. -/
theorem authErrVarIs_notNoSpace (err : GoInterface) :
    go_etcd_io.etcd.server.v3.etcdserver.apply.authErrsApart (GF := GF) ⊢
      authErrVarIs err -∗ notNoSpaceErr err := by
  iintro #Hap #H
  iunfold authErrVarIs at H
  iunfold notNoSpaceErr
  icases H with (%Hnil | ⟨%g, %e, %Hg, #Hge, %He⟩)
  · ileft; ipureintro; exact Hnil
  iunfold go_etcd_io.etcd.server.v3.etcdserver.apply.authErrsApart at Hap
  ihave #Ha := Hap $$ %g %Hg.1
  iunfold errVarApart at Ha
  icases Ha with ⟨%e1, %e2, #H1, #H2, %hne⟩
  icombine H2 Hge gives %h
  cases h
  iright
  iexists e, e1
  iframe H1
  ipureintro
  exact ⟨He, Hg.2, fun h => hne h.symm⟩

variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]
variable [errors_sem : _root_.Perennial.errors.Assumptions]

/-- **The answer's error at the start's chain with auth on** (given back): not `ErrNoSpace`'s
(`dispatchAnswer_notNoSpace`'s, and the auth layer's refusal). -/
theorem dispatchAnswer_notNoSpaceOn (rq : apply.IRRModel) (log : mvcc.Log) (skip : Bool)
    (resp err : GoInterface) (o : apply.Outcome) (hp : plainCover rq)
    (ho : o = .rejected .auth ∨ o = .rejected .backend ∨ ∃ l, o = .applied l false) :
    go_etcd_io.etcd.server.v3.etcdserver.apply.applyErrVars (GF := GF) ⊢
      apply.dispatchAnswer rq log skip resp err o -∗
      apply.dispatchAnswer rq log skip resp err o ∗ notNoSpaceErr err := by
  iintro #Hv H
  rcases ho with rfl | ho
  rotate_left
  · iapply dispatchAnswer_notNoSpace rq log skip resp err o hp ho $$ Hv H
  icases Hv with ⟨-, -, -, -, -, -, -, -, -, -, #Hap⟩
  have hnil : ⊢ notNoSpaceErr (GF := GF) GoInterface.nil := by
    iunfold notNoSpaceErr; iintro; ileft; ipureintro; rfl
  unfold plainCover at hp
  unfold apply.dispatchAnswer
  cases hk : apply.dispatchKind rq <;> simp only [hk] at hp ⊢
  · -- clusterVersionSet
    icases H with %h
    isplitr
    · ipureintro; exact h
    rw [h.2]; iapply hnil
  · -- clusterMemberAttrSet
    icases H with %h
    isplitr
    · ipureintro; exact h
    rw [h.2]; iapply hnil
  · -- put
    icases H with ⟨%op, %r, %h, H⟩
    simp only [apply.putAnswerIs, apply.putOutcomeIs, apply.rejErrIs]
    icases H with ⟨%hr, %hne, #HA⟩
    ihave #HA' := HA
    iunfold authApplyErrIs at HA'
    icases HA' with ⟨-, #HV⟩
    isplitl
    · iexists op, r; iframe HA; ipureintro; exact ⟨h, hr, hne⟩
    iapply authErrVarIs_notNoSpace err $$ Hap HV
  · -- deleteRange
    icases H with ⟨%op, %r, %h, H⟩
    simp only [apply.deleteAnswerIs, apply.deleteOutcomeIs, apply.rejErrIs]
    icases H with ⟨%hr, %hne, #HA⟩
    ihave #HA' := HA
    iunfold authApplyErrIs at HA'
    icases HA' with ⟨-, #HV⟩
    isplitl
    · iexists op, r; iframe HA; ipureintro; exact ⟨h, hr, hne⟩
    iapply authErrVarIs_notNoSpace err $$ Hap HV
  · -- txn
    icases H with ⟨%t, %r, %h, H⟩
    simp only [apply.txnAnswerIs, apply.txnOutcomeIs, apply.rejErrIs]
    icases H with ⟨%hr, %hne, #HA⟩
    ihave #HA' := HA
    iunfold authApplyErrIs at HA'
    icases HA' with ⟨-, #HV⟩
    isplitl
    · iexists t, r; iframe HA; ipureintro; exact ⟨h, hr, hne⟩
    iapply authErrVarIs_notNoSpace err $$ Hap HV
  all_goals exact hp.elim

/-- **`apply.Apply`'s result at the start's chain with auth on** (given back): `nil`, or its `Err`
is not `ErrNoSpace`'s (`applyResultIs_notNoSpace`'s counterpart). -/
theorem applyResultIs_notNoSpaceOn (rq : apply.IRRModel) (x x' : apply.ApplyKV) (ar : Loc)
    (out : apply.ApplyOut) (hp : plainCover rq)
    (hch : x.chain = apply.alarmChain true false false)
    (hs : apply.applyStep rq true x x' out) :
    go_etcd_io.etcd.server.v3.etcdserver.apply.applyErrVars (GF := GF) ⊢
      apply.applyResultIs rq true x.log ar out -∗
      apply.applyResultIs rq true x.log ar out ∗
      (⌜ar = null⌝ ∨ ∃ err : GoInterface,
        structFieldRef go_etcd_io.etcd.server.v3.etcdserver.apply.Result go!"Err" ar ↦□ err ∗
        notNoSpaceErr err) := by
  iintro #Hv H
  cases out with
  | skipped =>
    simp only [apply.applyResultIs]
    icases H with %h
    isplitr
    · ipureintro; exact h
    ileft; ipureintro; exact h
  | rejected =>
    exfalso
    have := hs.1
    rw [plainReq_noAdmin rq hp] at this
    cases this
  | dispatched o skip =>
    obtain ⟨-, hd, -, -⟩ := hs
    rw [hch] at hd
    have ho : o = .rejected .auth ∨ o = .rejected .backend ∨ ∃ l, o = .applied l false := by
      rcases dispatchStep_on_off rq x.log o hd with h | h
      · exact Or.inl h
      · exact Or.inr (dispatchStep_start rq x.log o hp h)
    simp only [apply.applyResultIs, apply.dispatchResult, or_true, ↓reduceIte]
    icases H with ⟨%hnn, %v, #Hvv, Hans, #HeI⟩
    ihave ⟨Hans, #Hn⟩ := dispatchAnswer_notNoSpaceOn rq x.log skip v.Resp' v.Err' o hp ho $$ Hv Hans
    isplitl [Hans]
    · isplitr
      · ipureintro; exact hnn
      iexists v
      iframe Hvv Hans HeI
    iright
    iexists v.Err'
    iframe Hn
    iapply apply.result_err_ro
    iexact Hvv

end iris

end EtcdGrove
end Perennial
