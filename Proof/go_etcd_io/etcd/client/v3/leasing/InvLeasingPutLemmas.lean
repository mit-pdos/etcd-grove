/-
Lemmas for the leasing KV's guarded writes (`tryModifyOp`, `revoke`, `put`): the model of a
guarded transaction (`guardedTxn`) whose then-branch is one operation, and the owned response of a
committed one. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.leasingKV__tryModifyOp

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace leasing

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.leasing go_etcd_io.etcd.api.v3

/-! ## The model -/

/-- A transaction with the single then-operation `top`, whose comparisons held, ran `top`. -/
theorem runTxn_then (r : w64) (s : List EtcdKv) (cs : List CmpModel) (top : TxnOp)
    (els : List TxnOp) (h : (runTxn r s ⟨cs, [top], els⟩).1 = true) :
    (runTxn r s ⟨cs, [top], els⟩).2.1 = (applyTxnOp r s top).1 ∧
    (runTxn r s ⟨cs, [top], els⟩).2.2 = [(applyTxnOp r s top).2] ∧
    (TxnModel.branch ⟨cs, [top], els⟩ true) = [top] := by
  simp only [runTxn] at h
  refine ⟨?_, ?_, ?_⟩ <;> simp [runTxn, h, TxnModel.branch, runOps]

theorem txnWrote_single (x : TxnOpResult) : txnWrote [x] = x.wrote := by
  simp [txnWrote]

/-- The operations of a put `Op` (`OpPut`'s kinds). -/
def putKind : TxnOp → Bool
  | .put _ _ _ => true
  | .putKeep _ _ => true
  | .putIgnVal _ _ => true
  | _ => false

/-- A put or a delete `Op` stands for a write: a linearizable operation. -/
theorem txnOpOf_write_lin {o : OpFull} {top : TxnOp} (h : txnOpOf o = some top)
    (ht : o.t = W64 2 ∨ o.t = W64 3) : top.linearizable = true := by
  unfold txnOpOf at h
  rcases ht with ht | ht
  · rw [ite_eq_right (by rw [ht]; decide), ite_eq_left ht] at h
    repeat' (split at h)
    all_goals first | (injection h with h; subst h; rfl) | simp at h
  · rw [ite_eq_right (by rw [ht]; decide), ite_eq_right (by rw [ht]; decide), ite_eq_left ht] at h
    injection h with h; subst h; rfl

/-- A put `Op` stands for a put kind. -/
theorem txnOpOf_put_kind {o : OpFull} {top : TxnOp} (h : txnOpOf o = some top)
    (ht : o.t = W64 2) : putKind top = true := by
  unfold txnOpOf at h
  rw [ite_eq_right (by rw [ht]; decide), ite_eq_left ht] at h
  repeat' (split at h)
  all_goals first | (injection h with h; subst h; rfl) | simp at h

/-- A put kind's result is `.put`. -/
theorem applyTxnOp_put_kind (r : w64) (s : List EtcdKv) (top : TxnOp) (h : putKind top = true) :
    (applyTxnOp r s top).2 = .put := by
  cases top <;> simp_all [putKind, applyTxnOp]

/-- `OpPut(lkey, "REVOKE", WithIgnoreLease())` keeps the key's lease. -/
theorem revokeOp_txnOpOf (lkey : GoString) :
    txnOpOf (opPutModel lkey go!"REVOKE" [withIgnoreLeaseM]) = some (.putKeep lkey go!"REVOKE") := by
  simp [opPutModel, opFold, withIgnoreLeaseM, OpFull.putInit, OpFull.newOp, OpModel.zero, txnOpOf]

theorem revokeOp_not_panics (lkey : GoString) :
    ¬ (opPutModel lkey go!"REVOKE" [withIgnoreLeaseM]).putPanics := by
  simp [opPutModel, opFold, withIgnoreLeaseM, OpFull.putInit, OpFull.newOp, OpModel.zero,
    OpFull.putPanics]

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]

/-- **A guarded transaction's owned result**: its `Succeeded` field, and if it is true, the
committed `top` (`opCommitted`, given the field back). -/
theorem txnCommitOk_guarded (lo : w64) (cs : List CmpModel) (top : TxnOp) (els : List TxnOp)
    (resp : Loc) (hlin : (TxnModel.linearizable ⟨cs, [top], els⟩) = true) :
    txnCommitOk (GF := GF) [] lo ⟨cs, [top], els⟩ resp ⊢
      ∃ (ok : Bool) (hdr : Loc) (hm : HdrM),
        structFieldRef etcdserverpb.TxnResponse go!"Header" resp ↦□ hdr ∗ hdrFull hdr hm ∗
        ⌜0 < sint.Z hm.revision ∧ sint.Z hm.revision < 2 ^ 63 - 1⌝ ∗
        structFieldRef etcdserverpb.TxnResponse go!"Succeeded" resp ↦ ok ∗
        (if ok then (structFieldRef etcdserverpb.TxnResponse go!"Succeeded" resp ↦ true -∗
          opCommitted lo top resp) else iprop(True)) := by
  unfold txnCommitOk txnRespOwn
  iintro ⟨%r, %s, %hm, %Hhm, ⟨%hdr, %sl, %ps, #HH, #Hhf, HS, #HR, #Hps, Hops⟩, #Hr, %Hf, #Hts⟩
  cases hok : (runTxn r s ⟨cs, [top], els⟩).1
  · iexists false, hdr, hm
    iframe #
    isplitr
    · ipureintro; rw [Hhm]; exact ⟨Hf.2.1, Hf.2.2.1⟩
    isplitl [HS]
    · iexact HS
    · simp only [Bool.false_eq_true, ↓reduceIte]
      itrivial
  · obtain ⟨h1, h2, h3⟩ := runTxn_then r s cs top els hok
    iexists true, hdr, hm
    iframe #
    isplitr
    · ipureintro; rw [Hhm]; exact ⟨Hf.2.1, Hf.2.2.1⟩
    iframe HS
    simp only [↓reduceIte]
    iintro HS
    unfold opCommitted txnRespOwn
    iexists r, s, hm
    rw [h1, h2, h3] at *
    rw [txnWrote_single] at *
    iframe
    iframe #
    ipureintro
    exact ⟨Hhm, Hf.1 hlin, Hf.2.1, Hf.2.2.1, Hf.2.2.2⟩

/-- **A committed put's response** (owned): the header, `Succeeded`, the put's response with its
`Header` field owned. -/
theorem opCommitted_put (lo : w64) (top : TxnOp) (resp : Loc) (htop : putKind top = true) :
    opCommitted (GF := GF) lo top resp ⊢
      ∃ (r : w64) (s : List EtcdKv) (hm : HdrM) (hdr : Loc) (rsl : GoSlice) (p0 w pr h0 : Loc),
        ⌜hm.revision = r⌝ ∗
        structFieldRef etcdserverpb.TxnResponse go!"Header" resp ↦□ hdr ∗ hdrFull hdr hm ∗
        structFieldRef etcdserverpb.TxnResponse go!"Succeeded" resp ↦ true ∗
        structFieldRef etcdserverpb.TxnResponse go!"Responses" resp ↦□ rsl ∗ rsl ↦*□ [p0] ∗
        ⌜p0 ≠ null⌝ ∗
        structFieldRef etcdserverpb.ResponseOp go!"Response" p0 ↦□
          interface.mkOk (go.GoType.PointerType etcdserverpb.ResponseOp_ResponsePut.ty) #w ∗
        structFieldRef etcdserverpb.ResponseOp_ResponsePut go!"ResponsePut" w ↦□ pr ∗ ⌜pr ≠ null⌝ ∗
        structFieldRef etcdserverpb.PutResponse go!"Header" pr ↦ h0 ∗
        etcdReached r ∗
        ⌜sint.Z lo ≤ sint.Z r ∧ 0 < sint.Z r ∧ sint.Z r < 2 ^ 63 - 1 ∧ EtcdStateWf [] s⌝ ∗
        txnStates [] r s (applyTxnOp r s top).1 true := by
  unfold opCommitted txnRespOwn
  iintro ⟨%r, %s, %hm, %Hhm, ⟨%hdr, %sl, %ps, #HH, #Hhf, HS, #HR, #Hps, Hops⟩, #Hr, %Hf, #Hts⟩
  have hres := applyTxnOp_put_kind r s top htop
  rw [hres] at *
  simp only [TxnOpResult.wrote] at *
  cases ps with
  | nil => simp only [txnOpsRespOwn]; iexfalso; iexact Hops
  | cons p0 ps =>
  cases ps with
  | cons _ _ => simp only [txnOpsRespOwn]; icases Hops with ⟨-, Hf⟩; iexfalso; iexact Hf
  | nil =>
  simp only [txnOpsRespOwn]
  icases Hops with ⟨Hop, -⟩
  cases top <;> simp only [putKind, Bool.false_eq_true] at htop <;>
  · simp only [txnOpRespOwn]
    icases Hop with ⟨%Hp0, %w, %pr, %h0, #Hw, #Hpr, %Hprn, Hh0⟩
    iexists r, s, hm, hdr, sl, p0, w, pr, h0
    iframe
    iframe #
    ipureintro
    exact ⟨Hhm, Hp0, Hprn, Hf⟩

end lemmas

end leasing
end EtcdGrove
end Perennial
