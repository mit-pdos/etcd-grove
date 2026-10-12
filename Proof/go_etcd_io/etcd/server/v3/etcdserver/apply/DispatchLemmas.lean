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

end apply
end EtcdGrove
end Perennial
