/-
Lemmas for `uberApplier.dispatch`'s proof (`server/v3/etcdserver/apply`, `uber_applier.go`):
a request field's pointer is nil iff the model's field is unset. Lean-first (no Rocq
counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.InvUber

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apply

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.apply go_etcd_io.etcd.api.v3

/-- Past `dispatch`'s first `switch`: not a request of it. -/
theorem preV3Kind_dispatchKind (rq : IRRModel) (h1 : rq.clusterVersionSet = none)
    (h2 : rq.clusterMemberAttrSet = none) (h3 : rq.downgradeInfoSet = none)
    (h4 : rq.downgradeVersionTest = false) : preV3Kind (dispatchKind rq) = false := by
  unfold dispatchKind
  simp only [h1, h2, h3, h4, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  simp only [apply_ite preV3Kind]
  simp only [preV3Kind, ite_self]

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- An optional request field is nil iff unset, given its predicate says not nil. -/
theorem optReqIs_null {α : Type} (l : Loc) (o : Option α) (P : Loc → α → IProp GF)
    (hP : ∀ a, P l a ⊢ ⌜l ≠ null⌝) : optReqIs l o P ⊢ ⌜l = null ↔ o = none⌝ := by
  cases o with
  | none =>
    simp only [optReqIs]
    iintro %h; ipureintro; simp [h]
  | some a =>
    simp only [optReqIs]
    iintro H
    ihave %h := hP a $$ H
    ipureintro; simp [h]

/-- The same for a field passed on unread. -/
theorem presentIs_null (l : Loc) (b : Bool) : presentIs (GF := GF) l b ⊢ ⌜l = null ↔ b = false⌝ := by
  simp only [presentIs]
  iintro %h; ipureintro
  cases b <;> simp_all


/-- The predicate of a set field. -/
theorem optReqIs_some {α : Type} (l : Loc) (o : Option α) (a : α) (P : Loc → α → IProp GF)
    (h : o = some a) : optReqIs l o P ⊢ P l a := by
  subst h; simp only [optReqIs]; iintro H; iexact H

theorem headerIs_nn (l : Loc) (a : HeaderModel) : headerIs (GF := GF) l a ⊢ ⌜l ≠ null⌝ := by
  unfold headerIs; iintro ⟨%h, -⟩; ipureintro; exact h

theorem rangeIs_nn (l : Loc) (a : OpFull) : txn.rangeRequestIs (GF := GF) l a ⊢ ⌜l ≠ null⌝ := by
  unfold txn.rangeRequestIs; iintro ⟨%h, -⟩; ipureintro; exact h

theorem putIs_nn (l : Loc) (a : OpFull) : txn.putRequestIs (GF := GF) l a ⊢ ⌜l ≠ null⌝ := by
  unfold txn.putRequestIs; iintro ⟨%h, -⟩; ipureintro; exact h

theorem deleteIs_nn (l : Loc) (a : OpFull) : txn.deleteRangeRequestIs (GF := GF) l a ⊢ ⌜l ≠ null⌝ := by
  unfold txn.deleteRangeRequestIs; iintro ⟨%h, -⟩; ipureintro; exact h

theorem txnIs_nn (l : Loc) (a : TxnModel) : txn.txnRequestIs (GF := GF) l a ⊢ ⌜l ≠ null⌝ := by
  unfold txn.txnRequestIs; iintro ⟨%h, -⟩; ipureintro; exact h

theorem compactionIs_nn (l : Loc) (a : w64) : compactionIs (GF := GF) l a ⊢ ⌜l ≠ null⌝ := by
  unfold compactionIs; iintro ⟨%h, -⟩; ipureintro; exact h

theorem leaseGrantIs_nn (l : Loc) (a : LeaseGrantModel) : leaseGrantIs (GF := GF) l a ⊢ ⌜l ≠ null⌝ := by
  unfold leaseGrantIs; iintro ⟨%h, -⟩; ipureintro; exact h

theorem leaseRevokeIs_nn (l : Loc) (a : w64) : leaseRevokeIs (GF := GF) l a ⊢ ⌜l ≠ null⌝ := by
  unfold leaseRevokeIs; iintro ⟨%h, -⟩; ipureintro; exact h

theorem alarmRequestIs_nn (l : Loc) (a : AlarmModel) : alarmRequestIs (GF := GF) l a ⊢ ⌜l ≠ null⌝ := by
  unfold alarmRequestIs; iintro ⟨%h, -⟩; ipureintro; exact h

theorem leaseCheckpointIs_nn (l : Loc) (a : (List CheckpointModel)) : leaseCheckpointIs (GF := GF) l a ⊢ ⌜l ≠ null⌝ := by
  unfold leaseCheckpointIs; iintro ⟨%h, -⟩; ipureintro; exact h

theorem authenticateIs_nn (l : Loc) (a : AuthenticateModel) : authenticateIs (GF := GF) l a ⊢ ⌜l ≠ null⌝ := by
  unfold authenticateIs; iintro ⟨%h, -⟩; ipureintro; exact h

theorem authUserGetIs_nn (l : Loc) (a : GoString) : authUserGetIs (GF := GF) l a ⊢ ⌜l ≠ null⌝ := by
  unfold authUserGetIs; iintro ⟨%h, -⟩; ipureintro; exact h

theorem authRoleGetIs_nn (l : Loc) (a : GoString) : authRoleGetIs (GF := GF) l a ⊢ ⌜l ≠ null⌝ := by
  unfold authRoleGetIs; iintro ⟨%h, -⟩; ipureintro; exact h

theorem clusterVersionSetIs_nn (l : Loc) (a : GoString) : clusterVersionSetIs (GF := GF) l a ⊢ ⌜l ≠ null⌝ := by
  unfold clusterVersionSetIs; iintro ⟨%h, -⟩; ipureintro; exact h

theorem memberAttrSetIs_nn (l : Loc) (a : MemberAttrModel) : memberAttrSetIs (GF := GF) l a ⊢ ⌜l ≠ null⌝ := by
  unfold memberAttrSetIs; iintro ⟨%h, -⟩; ipureintro; exact h

theorem downgradeInfoSetIs_nn (l : Loc) (a : DowngradeModel) : downgradeInfoSetIs (GF := GF) l a ⊢ ⌜l ≠ null⌝ := by
  unfold downgradeInfoSetIs; iintro ⟨%h, -⟩; ipureintro; exact h

end lemmas

/-! ## The KV answers' errors, as `errors.Is` sees them

Each KV answer (`putOutcomeIs`, ...) names its error: `nil`, an error variable (`ErrCorrupt`,
`ErrNoSpace`, the txn checks' `ErrLeaseNotFound`/`ErrKeyNotFound`, mvcc's `ErrFutureRev`/
`ErrCompacted`: `errors.New` errors, `applyErrVars`), or the auth store's or the lessor's (their
contracts': `applyErrIs`). So the error is one `errors.Is` can take (`applyErrIs`). -/

section errIs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [_root_.Perennial.errors.Assumptions]

/-- A persistent fact `applyErrIs err` drawn from `X` (with the persistent `V`) keeps `X`. -/
theorem keep_errIs {V X : IProp GF} {err : GoInterface} [Persistent V]
    (h : V ⊢ X -∗ applyErrIs err) : V ∗ X ⊢ X ∗ applyErrIs err := by
  have h2 : V ∗ X ⊢ applyErrIs err := by
    iintro ⟨#HV, HX⟩
    iapply h $$ HV HX
  exact (persistent_entails_left h2).trans (sep_mono_left sep_elim_right)

/-- An error variable's error (`txn.errVarIs`), by `applyErrVars`. -/
theorem errVarIs_errIs (g : GoString) (err : GoInterface) :
    errVarLeaf (GF := GF) g ⊢ txn.errVarIs g err -∗ applyErrIs err := by
  iintro #Hv H
  iunfold txn.errVarIs at H
  iapply errVar_applyErrIs g err $$ Hv H

/-- A rejection's error. -/
theorem rejErrIs_errIs (bk : GoInterface → IProp GF) (k : RejectKind) (err : GoInterface)
    (hbk : go_etcd_io.etcd.server.v3.etcdserver.apply.applyErrVars (GF := GF) ⊢
      bk err -∗ applyErrIs err) :
    go_etcd_io.etcd.server.v3.etcdserver.apply.applyErrVars (GF := GF) ⊢
      rejErrIs bk k err -∗ applyErrIs err := by
  iintro #Hv H
  ihave #Hv' := Hv
  icases Hv' with ⟨#HC, #HN, -⟩
  cases k <;> simp only [rejErrIs]
  · iapply errVarIs_errIs _ _ $$ HC H
  · iapply errVarIs_errIs _ _ $$ HN H
  · icases H with ⟨-, #H⟩; iexact H
  · iapply hbk $$ Hv H

/-- An applied write's error: `nil` or the quota's `ErrNoSpace`. -/
theorem noSpaceErrIs_errIs (ns : Bool) (err : GoInterface) :
    go_etcd_io.etcd.server.v3.etcdserver.apply.applyErrVars (GF := GF) ⊢
      noSpaceErrIs ns err -∗ applyErrIs err := by
  iintro #Hv H
  icases Hv with ⟨-, #HN, -⟩
  cases ns <;> simp only [noSpaceErrIs, Bool.false_eq_true, ↓reduceIte]
  · icases H with %h; subst h; iapply applyErrIs_nil
  · iapply errVarIs_errIs _ _ $$ HN H

theorem putOutcomeIs_errIs (log : mvcc.Log) (o : OpFull) (resp : Loc) (err : GoInterface)
    (oc : Outcome) :
    go_etcd_io.etcd.server.v3.etcdserver.apply.applyErrVars (GF := GF) ⊢
      putOutcomeIs log o resp err oc -∗ applyErrIs err := by
  iintro #Hv H
  rcases oc with k | ⟨log', ns⟩ <;> simp only [putOutcomeIs]
  · icases H with ⟨-, H⟩
    iapply rejErrIs_errIs _ k err ?_ $$ Hv H
    iintro #Hv (H | H)
    · icases Hv with ⟨-, -, -, #HL, -⟩; iapply errVarIs_errIs _ _ $$ HL H
    · icases Hv with ⟨-, -, #HK, -⟩; iapply errVarIs_errIs _ _ $$ HK H
  · icases H with ⟨-, H⟩
    iapply noSpaceErrIs_errIs ns err $$ Hv H

theorem deleteOutcomeIs_errIs (log : mvcc.Log) (o : OpFull) (resp : Loc) (err : GoInterface)
    (oc : Outcome) :
    go_etcd_io.etcd.server.v3.etcdserver.apply.applyErrVars (GF := GF) ⊢
      deleteOutcomeIs log o resp err oc -∗ applyErrIs err := by
  iintro #Hv H
  rcases oc with k | ⟨log', ns⟩ <;> simp only [deleteOutcomeIs]
  · icases H with ⟨-, H⟩
    iapply rejErrIs_errIs _ k err ?_ $$ Hv H
    iintro - %h; exact h.elim
  · icases H with ⟨-, H⟩
    iapply noSpaceErrIs_errIs ns err $$ Hv H

theorem rangeOutcomeIs_errIs (log : mvcc.Log) (o : OpFull) (resp : Loc) (err : GoInterface)
    (oc : Outcome) :
    go_etcd_io.etcd.server.v3.etcdserver.apply.applyErrVars (GF := GF) ⊢
      rangeOutcomeIs log o resp err oc -∗ applyErrIs err := by
  iintro #Hv H
  rcases oc with k | ⟨log', ns⟩ <;> simp only [rangeOutcomeIs]
  · icases H with ⟨-, H⟩
    iapply rejErrIs_errIs _ k err ?_ $$ Hv H
    iintro - %h; exact h.elim
  · icases H with ⟨H, %Hne⟩
    iunfold txn.rangeResult at H
    icases H with (⟨-, %ef, #Hef, %Herr⟩ | %Hce | ⟨%Hok, -⟩)
    · icases Hv with ⟨-, -, -, -, #HF, -⟩
      iapply errVar_applyErrIs _ _ $$ HF
      iexists ef; iframe Hef; ipureintro; exact Herr
    · exfalso
      rcases Hne with h | h
      · exact Hce.2.2.2.2 h
      · have := Hce.1; omega
    · rw [Hok.2]; iapply applyErrIs_nil

theorem txnOutcomeIs_errIs (log : mvcc.Log) (t : TxnModel) (skip : Bool) (resp : Loc)
    (err : GoInterface) (oc : Outcome) :
    go_etcd_io.etcd.server.v3.etcdserver.apply.applyErrVars (GF := GF) ⊢
      txnOutcomeIs log t skip resp err oc -∗ applyErrIs err := by
  iintro #Hv H
  rcases oc with k | ⟨log', ns⟩ <;> simp only [txnOutcomeIs]
  · icases H with ⟨-, H⟩
    iapply rejErrIs_errIs _ k err ?_ $$ Hv H
    iintro #Hv H
    iunfold txn.checkErrIs at H
    icases Hv with ⟨-, -, #HK, #HL, #HF, #HCp⟩
    icases H with (H | H | H | H)
    · iapply errVarIs_errIs _ _ $$ HL H
    · iapply errVarIs_errIs _ _ $$ HK H
    · iapply errVar_applyErrIs _ _ $$ HF H
    · iapply errVar_applyErrIs _ _ $$ HCp H
  · icases H with ⟨-, H⟩
    iapply noSpaceErrIs_errIs ns err $$ Hv H

theorem revokeOutcomeIs_errIs (resp : Loc) (err : GoInterface) (oc : Outcome) :
    go_etcd_io.etcd.server.v3.etcdserver.apply.applyErrVars (GF := GF) ⊢
      revokeOutcomeIs resp err oc -∗ applyErrIs err := by
  iintro #Hv H
  rcases oc with k | ⟨log', ns⟩ <;> simp only [revokeOutcomeIs]
  · icases H with ⟨-, H⟩
    iapply rejErrIs_errIs _ k err ?_ $$ Hv H
    iintro - %h; exact h.elim
  · iexact H

end errIs

end apply
end EtcdGrove
end Perennial
