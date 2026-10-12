/-
The apply package's lemmas for the wrapper layers' methods (`quota.go`): an answer whose error
is `nil` is that of an applied request without the quota's `ErrNoSpace` (every rejection's
error, and the applied `noSpace`'s, is not nil). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Chain

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apply

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.apply

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- A global error variable's value is not nil. -/
theorem errVarIs_nil (g : GoString) :
    txn.errVarIs (GF := GF) g GoInterface.nil ⊢ iprop(False) := by
  iunfold txn.errVarIs
  iintro ⟨%e, -, %He⟩
  cases He

/-- A put's answer with a `nil` error: applied, without the quota's `ErrNoSpace`. -/
theorem putOutcomeIs_nil (log : mvcc.Log) (o : OpFull) (resp : Loc) (oc : Outcome) :
    putOutcomeIs (GF := GF) log o resp GoInterface.nil oc ⊢
      ⌜∃ log', oc = .applied log' false⌝ := by
  rcases oc with k | ⟨log', ns⟩
  · cases k <;> simp only [putOutcomeIs, rejErrIs]
    · iintro ⟨-, H⟩; iexfalso; iapply errVarIs_nil $$ H
    · iintro ⟨-, H⟩; iexfalso; iapply errVarIs_nil $$ H
    · iintro ⟨-, %H⟩; exact absurd rfl H
    · iintro ⟨-, (H | H)⟩ <;> iexfalso <;> iapply errVarIs_nil $$ H
  · cases ns <;> simp only [putOutcomeIs, noSpaceErrIs, Bool.false_eq_true, ↓reduceIte]
    · iintro -; ipureintro; exact ⟨log', rfl⟩
    · iintro ⟨-, H⟩; iexfalso; iapply errVarIs_nil $$ H

/-- A transaction's answer with a `nil` error: applied, without the quota's `ErrNoSpace`. -/
theorem txnOutcomeIs_nil (log : mvcc.Log) (t : TxnModel) (skip : Bool) (resp : Loc)
    (oc : Outcome) :
    txnOutcomeIs (GF := GF) log t skip resp GoInterface.nil oc ⊢
      ⌜∃ log', oc = .applied log' false⌝ := by
  rcases oc with k | ⟨log', ns⟩
  · cases k <;> simp only [txnOutcomeIs, rejErrIs]
    · iintro ⟨-, H⟩; iexfalso; iapply errVarIs_nil $$ H
    · iintro ⟨-, H⟩; iexfalso; iapply errVarIs_nil $$ H
    · iintro ⟨-, %H⟩; exact absurd rfl H
    · iunfold txn.checkErrIs
      iintro ⟨-, (H | H | ⟨%e, -, %He⟩ | ⟨%e, -, %He⟩)⟩
      · iexfalso; iapply errVarIs_nil $$ H
      · iexfalso; iapply errVarIs_nil $$ H
      · cases He
      · cases He
  · cases ns <;> simp only [txnOutcomeIs, noSpaceErrIs, Bool.false_eq_true, ↓reduceIte]
    · iintro -; ipureintro; exact ⟨log', rfl⟩
    · iintro ⟨-, H⟩; iexfalso; iapply errVarIs_nil $$ H

end lemmas

end apply
end EtcdGrove
end Perennial
