/-
Lemmas of the uber-applier's and `apply.Apply`'s proofs (`server/v3/etcdserver/apply`, unit 2):
a request field's pointer is nil iff the model's field is unset. Lean-first (no Rocq counterpart).
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

theorem irrId_zero (rq : IRRModel) (h : rq.id = W64 0) :
    irrId rq = rq.header.map HeaderModel.id := by
  unfold irrId; rw [if_neg (fun h' => h' h)]

theorem irrId_nz (rq : IRRModel) (h : rq.id ≠ W64 0) : irrId rq = some rq.id := by
  unfold irrId; rw [if_pos h]

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- An optional request field is nil iff unset, when a set one is not nil. -/
theorem optReqIs_nil {α : Type} (l : Loc) (o : Option α) (P : Loc → α → IProp GF)
    (hP : ∀ l a, P l a ⊢ ⌜l ≠ null⌝) : optReqIs l o P ⊢ ⌜l = null ↔ o = none⌝ := by
  cases o with
  | none => simp only [optReqIs]; iintro %h; ipureintro; simp [h]
  | some a =>
    simp only [optReqIs]
    iintro H
    ihave %h := hP l a $$ H
    ipureintro; simp [h]

theorem rangeRequestIs_nn (l : Loc) (o : OpFull) : txn.rangeRequestIs (GF := GF) l o ⊢ ⌜l ≠ null⌝ := by
  unfold txn.rangeRequestIs; iintro ⟨%h, -⟩; ipureintro; exact h

theorem authUserGetIs_nn (l : Loc) (n : GoString) : authUserGetIs (GF := GF) l n ⊢ ⌜l ≠ null⌝ := by
  unfold authUserGetIs; iintro ⟨%h, -⟩; ipureintro; exact h

theorem authRoleGetIs_nn (l : Loc) (n : GoString) : authRoleGetIs (GF := GF) l n ⊢ ⌜l ≠ null⌝ := by
  unfold authRoleGetIs; iintro ⟨%h, -⟩; ipureintro; exact h

theorem txnRequestIs_nn (l : Loc) (t : TxnModel) : txn.txnRequestIs (GF := GF) l t ⊢ ⌜l ≠ null⌝ := by
  unfold txn.txnRequestIs; iintro ⟨%h, -⟩; ipureintro; exact h

theorem headerIs_nn (l : Loc) (h : HeaderModel) : headerIs (GF := GF) l h ⊢ ⌜l ≠ null⌝ := by
  unfold headerIs; iintro ⟨%h, -⟩; ipureintro; exact h

section pkg
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- A read-only `Result`'s `Err` is readable. -/
theorem result_err_ro (ar : Loc) (v : Result) :
    (ar ↦□ v : IProp GF) ⊢ structFieldRef Result go!"Err" ar ↦□ v.Err' := by
  iintro #H
  iStructNamed H
  iexact Err

/-- `apply.Apply`'s result has a readable `Err` (or is nil), `resultErrOk`. -/
theorem applyResultIs_resultErrOk (rq : IRRModel) (v3 : Bool) (log : mvcc.Log) (ar : Loc)
    (out : ApplyOut) :
    applyResultIs (GF := GF) rq v3 log ar out ⊢ resultErrOk ar ∗ applyResultIs rq v3 log ar out := by
  cases out with
  | skipped =>
    simp only [applyResultIs]
    iintro %h
    isplitl
    · iunfold resultErrOk; ileft; ipureintro; exact h
    · ipureintro; exact h
  | rejected =>
    simp only [applyResultIs]
    iintro #H
    iframe H
    iunfold rejectedResultIs at H
    icases H with ⟨-, %v, #Hv, -, #HeI⟩
    iunfold resultErrOk
    iright
    iexists v.Err'
    iframe HeI
    iapply result_err_ro
    iexact Hv
  | dispatched o skip =>
    simp only [applyResultIs, dispatchResult]
    split
    · iintro ⟨%h, %v, #Hv, Hans, #HeI⟩
      isplitr
      · iunfold resultErrOk
        iright
        iexists v.Err'
        iframe HeI
        iapply result_err_ro
        iexact Hv
      isplitr
      · ipureintro; exact h
      iexists v
      iframe Hv Hans HeI
    · iintro %h
      isplitl
      · iunfold resultErrOk; ileft; ipureintro; exact h
      · ipureintro; exact h

end pkg

end lemmas

end apply
end EtcdGrove
end Perennial
