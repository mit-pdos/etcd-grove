/-
**`applyEntryNormal`'s NOSPACE branch is dead** (D19k, 2026-10-18). Lean-first (no Rocq
counterpart).

Go's `applyEntryNormal` raises the NOSPACE alarm (a goroutine proposing `{Alarm: ACTIVATE,
NOSPACE}`, the trust-boundary contract `EtcdServer.raftRequestAlarm` until D19k) when
`errors.Is(ar.Err, ErrNoSpace)` holds. In the model it never does: the entry's request is plain
(`plainReq`, within `plainCover`: the KV writes and the monitors' requests, no auth field;
since D19q the proofs here are over `plainCover`, so they hold at every workload), the chain is
the start's
(`alarmChain false false false`: auth off, no capped or corrupt layer, the quota the identity under
`backendUnderQuota`), so the result's error is `nil` or one of the backend's `errors.New`
variables (`ErrKeyNotFound`, `ErrLeaseNotFound`, mvcc's `ErrFutureRev`, `ErrCompacted`), none of
which holds `ErrNoSpace`'s error (`applyErrVars`' `errVarApart`, from the variables' message
cells); and `errors.Is` of such an error and `ErrNoSpace` is `false` (Perennial's `errors.Is`
spec, `Spec/errors/Is.lean`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVModel
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.UberLemmas
public import Spec.errors.Is

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

/-! ## The outcomes at the start's chain -/

/-- A covered request has no auth field set. -/
theorem plainReq_noAdmin (rq : apply.IRRModel) (hp : plainCover rq) :
    apply.needAdminPermission rq = false := by
  unfold plainCover at hp
  cases hk : apply.dispatchKind rq <;> simp only [hk] at hp
  all_goals first | exact hp | exact hp.2.1 | exact hp.2

/-- **A covered request dispatched at the start's chain** (with `v3`): the backend's rejection or an
applied outcome without the quota's `ErrNoSpace`. -/
theorem dispatchStep_start (rq : apply.IRRModel) (log : mvcc.Log) (o : apply.Outcome)
    (hp : plainCover rq)
    (h : apply.dispatchStep (apply.alarmChain false false false) rq true log o) :
    o = .rejected .backend ∨ ∃ l, o = .applied l false := by
  have hna := plainReq_noAdmin rq hp
  unfold plainCover at hp
  unfold apply.dispatchStep at h
  cases hk : apply.dispatchKind rq <;> simp only [hk] at hp h <;>
    simp only [apply.preV3Kind, apply.storeKind, Bool.false_eq_true, false_or, or_false,
      ↓reduceIte, true_or] at h
  all_goals first
    | exact Or.inr ⟨_, h⟩
    | skip
  all_goals
    simp only [apply.alarmChain, apply.baseChain, apply.chainStep, apply.authChecks,
      apply.authMayReject, hk, hna, Bool.false_eq_true, ↓reduceIte, true_or, or_false,
      false_or, ne_eq, reduceCtorEq, not_false_eq_true, and_self, and_false, not_true_eq_false,
      false_and] at h
    unfold apply.backendStep at h
    simp only [hk] at h
  · obtain ⟨op, -, h⟩ := h
    rcases h with ⟨-, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, rfl⟩
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inr ⟨_, rfl⟩
  · obtain ⟨op, -, rfl⟩ := h
    exact Or.inr ⟨_, rfl⟩
  · obtain ⟨t, -, h⟩ := h
    rcases h with ⟨rfl, -⟩ | ⟨rfl, -, -⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨_, rfl⟩

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **An error other than `ErrNoSpace`'s** (persistent): `nil`, or a leaf pointer error without
`Is` other than the one `ErrNoSpace` holds. -/
def notNoSpaceErr (err : GoInterface) : IProp GF :=
  iprop(⌜err = GoInterface.nil⌝ ∨ ∃ e eN : GoInterfaceOk,
    ⌜err = GoInterface.ok e ∧ errLeaf e ∧ e ≠ eN⌝ ∗
    globalAddr go_etcd_io.etcd.server.v3.etcdserver.errors.ErrNoSpace ↦□ GoInterface.ok eN)

instance notNoSpaceErr_persistent (err : GoInterface) :
    Persistent (notNoSpaceErr (GF := GF) err) := by
  unfold notNoSpaceErr; infer_instance

/-- An error variable's error, told apart from `ErrNoSpace`'s. -/
theorem errVarIs_notNoSpace (g : GoString) (err : GoInterface) :
    errVarLeaf (GF := GF) g ⊢
      errVarApart go_etcd_io.etcd.server.v3.etcdserver.errors.ErrNoSpace g -∗
      (∃ e : GoInterfaceOk, globalAddr g ↦□ GoInterface.ok e ∗ ⌜err = GoInterface.ok e⌝) -∗
      notNoSpaceErr err := by
  unfold errVarLeaf errVarApart notNoSpaceErr
  iintro ⟨%e, #He, %hl, -⟩ ⟨%e1, %e2, #H1, #H2, %hne⟩ ⟨%e', #He', %heq⟩
  icombine He He' gives %h1
  icombine H2 He gives %h2
  cases h1
  cases h2
  iright
  iexists e, e1
  iframe H1
  ipureintro
  exact ⟨heq, hl, fun h => hne h.symm⟩

variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]
variable [errors_sem : _root_.Perennial.errors.Assumptions]

/-- **The answer's error at the start's chain** (`dispatchAnswer`, given back): not
`ErrNoSpace`'s. -/
theorem dispatchAnswer_notNoSpace (rq : apply.IRRModel) (log : mvcc.Log) (skip : Bool)
    (resp err : GoInterface) (o : apply.Outcome) (hp : plainCover rq)
    (ho : o = .rejected .backend ∨ ∃ l, o = .applied l false) :
    go_etcd_io.etcd.server.v3.etcdserver.apply.applyErrVars (GF := GF) ⊢
      apply.dispatchAnswer rq log skip resp err o -∗
      apply.dispatchAnswer rq log skip resp err o ∗ notNoSpaceErr err := by
  iintro #Hv H
  icases Hv with ⟨-, -, #HK, #HL, #HF, #HC, #AK, #AL, #AF, #AC, -⟩
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
    rcases ho with rfl | ⟨l, rfl⟩
    · simp only [apply.putAnswerIs, apply.putOutcomeIs, apply.rejErrIs]
      icases H with ⟨%hr, #H⟩
      isplitl
      · iexists op, r; iframe H; ipureintro; exact ⟨h, hr⟩
      unfold txn.errVarIs
      icases H with (#H | #H)
      · iapply errVarIs_notNoSpace _ _ $$ HL AL H
      · iapply errVarIs_notNoSpace _ _ $$ HK AK H
    · simp only [apply.putAnswerIs, apply.putOutcomeIs, apply.noSpaceErrIs, Bool.false_eq_true,
        ↓reduceIte]
      icases H with ⟨⟨HR, %he⟩, Hh⟩
      isplitl
      · iexists op, r; iframe HR Hh; ipureintro; exact ⟨h, he⟩
      rw [he]; iapply hnil
  · -- deleteRange
    icases H with ⟨%op, %r, %h, H⟩
    rcases ho with rfl | ⟨l, rfl⟩
    · simp only [apply.deleteAnswerIs, apply.deleteOutcomeIs, apply.rejErrIs]
      icases H with ⟨-, H⟩
      icases H with %H
      exact H.elim
    · simp only [apply.deleteAnswerIs, apply.deleteOutcomeIs, apply.noSpaceErrIs,
        Bool.false_eq_true, ↓reduceIte]
      icases H with ⟨⟨HR, %he⟩, Hh⟩
      isplitl
      · iexists op, r; iframe HR Hh; ipureintro; exact ⟨h, he⟩
      rw [he]; iapply hnil
  · -- txn
    icases H with ⟨%t, %r, %h, H⟩
    rcases ho with rfl | ⟨l, rfl⟩
    · simp only [apply.txnAnswerIs, apply.txnOutcomeIs, apply.rejErrIs]
      icases H with ⟨%hr, #H⟩
      isplitl
      · iexists t, r; iframe H; ipureintro; exact ⟨h, hr⟩
      iunfold txn.checkErrIs at H
      unfold txn.errVarIs
      icases H with (#H | #H | #H | #H)
      · iapply errVarIs_notNoSpace _ _ $$ HL AL H
      · iapply errVarIs_notNoSpace _ _ $$ HK AK H
      · iapply errVarIs_notNoSpace _ _ $$ HF AF H
      · iapply errVarIs_notNoSpace _ _ $$ HC AC H
    · simp only [apply.txnAnswerIs, apply.txnOutcomeIs, apply.noSpaceErrIs, Bool.false_eq_true,
        ↓reduceIte]
      icases H with ⟨⟨HR, %he⟩, Hh⟩
      isplitl
      · iexists t, r; iframe HR Hh; ipureintro; exact ⟨h, he⟩
      rw [he]; iapply hnil
  all_goals exact hp.elim

/-- **`apply.Apply`'s result at the start's chain** (given back): `nil`, or its `Err` is not
`ErrNoSpace`'s. -/
theorem applyResultIs_notNoSpace (rq : apply.IRRModel) (x x' : apply.ApplyKV) (ar : Loc)
    (out : apply.ApplyOut) (hp : plainCover rq)
    (hch : x.chain = apply.alarmChain false false false)
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
    have ho := dispatchStep_start rq x.log o hp hd
    simp only [apply.applyResultIs, apply.dispatchResult, or_true, ↓reduceIte]
    icases H with ⟨%hnn, %v, #Hvv, Hans, #HeI⟩
    ihave ⟨Hans, #Hn⟩ := dispatchAnswer_notNoSpace rq x.log skip v.Resp' v.Err' o hp ho $$ Hv Hans
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

/-- **`errors.Is(err, ErrNoSpace)` of an error other than `ErrNoSpace`'s is `false`.** -/
theorem wp_Is_notNoSpace (hIs : errors.Is.spec (GF := GF) (hG := hG)) (err : GoInterface)
    (eN : GoInterfaceOk) (hpt : _root_.Perennial.errors.IsPointerError eN) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.errors ∗ applyErrIs err ∗ notNoSpaceErr err ∗
        globalAddr go_etcd_io.etcd.server.v3.etcdserver.errors.ErrNoSpace ↦□ GoInterface.ok eN }}
      (App (App (Val (@! _root_.Perennial.errors.Is)) (Val #err)) (Val #(GoInterface.ok eN)))
    {{ RET #false; True }} := by
  iintro %Φ ⟨#Hp, #HeI, #Hn, #HN⟩ HΦ
  iunfold notNoSpaceErr at Hn
  icases Hn with (%Hnil | ⟨%e, %eN', %Hf, #HN'⟩)
  · ihave #HT := applyErrIs_tree err $$ HeI
    ihave ⟨%S, %M, #Htree, %HS⟩ := HT $$ %(GoInterface.ok eN)
    iapply hIs S M err (GoInterface.ok eN) (fun tii h => by cases h; exact hpt)
      (HS.2 (fun tii h => by cases h; exact hpt)) $$ []
    · iframe #; ipureintro; exact HS.1
    iintro !> %b ⟨%h1, -, -⟩
    have hb : b = false := by
      rw [h1 (Or.inl Hnil), Hnil]; simp
    subst hb
    iapply HΦ
    itrivial
  · obtain ⟨rfl, hl, hne⟩ := Hf
    icombine HN HN' gives %h
    cases h
    iapply hIs (· = GoInterface.ok e) (fun _ => False) (GoInterface.ok e) (GoInterface.ok eN)
      (fun tii h => by cases h; exact hpt)
      (_root_.Perennial.errors.treeTyped_pointer e _ hl.1) $$ []
    · iframe Hp
      isplitl
      · iapply _root_.Perennial.errors.errorIsTree_leaf e (fun _ => False) _ hl.2.1 hl.2.2
      ipureintro; rfl
    iintro !> %b ⟨-, -, %h3⟩
    cases b
    · iapply HΦ; itrivial
    · exfalso
      obtain ⟨ii, hii, hor⟩ := h3 eN rfl hpt (by simp) rfl
      cases hii
      rcases hor with h | h
      · cases h; exact hne rfl
      · exact h

end iris

end EtcdGrove
end Perennial
