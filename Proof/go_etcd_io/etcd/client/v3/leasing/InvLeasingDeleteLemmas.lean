/-
Lemmas for the leasing KV's deletes (`deleteRangeRPC`, `deleteRange`, `delete`): the range delete's
transaction in the model, and owned key-values read-only. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeasingKV
public import Spec.go_etcd_io.etcd.client.v3.leasing.leasingKV__deleteRangeRPC

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

/-- The keys-only get and the delete of a range (`deleteRangeRPC`'s then-branch): the get changes
nothing, the delete removes the range's keys. -/
theorem runOps_getDelete (r : w64) (s : List EtcdKv) (og od : OpFull) :
    runOps r s [.get og, .delete od] =
      (s.filter (fun v => !inRange od.key od.base.rangeEnd v.key),
        [.range (rangeSel s og) (rangeIn s og).length, .delete (rangeIn s od).length]) := by
  simp [runOps, applyTxnOp]

theorem txnWrote_getDelete (sel : List EtcdKv) (c n : Nat) :
    txnWrote [.range sel c, .delete n] = (n != 0) := by
  simp [txnWrote, TxnOpResult.wrote]

/-- A delete alone (`delete`'s single-key transactions). -/
theorem applyTxnOp_delete (r : w64) (s : List EtcdKv) (o : OpFull) :
    applyTxnOp r s (.delete o) =
      (s.filter (fun v => !inRange o.key o.base.rangeEnd v.key), .delete (rangeIn s o).length) := by
  simp [applyTxnOp]

/-- `rangeIn` reads the range only. -/
theorem rangeIn_congr (s : List EtcdKv) (o o' : OpFull) (hk : o.key = o'.key)
    (he : o.base.rangeEnd = o'.base.rangeEnd) : rangeIn s o = rangeIn s o' := by
  unfold rangeIn; rw [hk, he]

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

instance cachedKvOwn_discard_persistent (c : CachedKv) :
    Persistent (cachedKvOwn (GF := GF) c DFrac.discard) :=
  (cachedKvOwn_dfractional (GF := GF) c).dfractional_persistent

/-- An owned key-value made read-only is `kvValAt`. -/
theorem cachedKvOwn_kvValAt (c : CachedKv) :
    cachedKvOwn (GF := GF) c DFrac.discard ⊢ kvValAt c.p c.kv := by
  unfold cachedKvOwn kvValAt
  iintro ⟨-, HK, #Hks, HC, HM, HV, HVal, #Hvs, HL⟩
  iexists c.keySl, c.valSl
  iframe
  iframe #

/-- `deleteCommitted` reads the delete's range only. -/
theorem deleteCommitted_congr (lo : w64) (o o' : OpFull) (dr : Loc) (hk : o.key = o'.key)
    (he : o.base.rangeEnd = o'.base.rangeEnd) :
    deleteCommitted (GF := GF) lo o dr ⊢ deleteCommitted lo o' dr := by
  unfold deleteCommitted
  have h : ∀ s, rangeIn s o = rangeIn s o' := fun s => rangeIn_congr s o o' hk he
  simp only [hk, he, h]
  exact .rfl

theorem deleteCommitted_ne_null (lo : w64) (o : OpFull) (dr : Loc) :
    deleteCommitted (GF := GF) lo o dr ⊢ ⌜dr ≠ null⌝ ∗ deleteCommitted lo o dr := by
  unfold deleteCommitted
  iintro ⟨%r, %s, %hdr, %hm, %n, %Hf, H⟩
  isplitr
  · ipureintro; exact Hf.1
  iexists r, s, hdr, hm, n
  iframe
  ipureintro; exact Hf

/-- **A committed delete** (`opCommitted` of `.delete o`), unpacked: the response's header,
`Succeeded`, its one delete response (owned header, `Deleted`), and etcd's states. -/
theorem opCommitted_delete (lo : w64) (o : OpFull) (resp : Loc) :
    opCommitted (GF := GF) lo (.delete o) resp ⊢
      ∃ (r : w64) (s : List EtcdKv) (hm : HdrM) (hdr : Loc) (rsl : GoSlice) (p0 w dr h0 : Loc),
        ⌜hm.revision = r⌝ ∗
        structFieldRef etcdserverpb.TxnResponse go!"Header" resp ↦□ hdr ∗ hdrFull hdr hm ∗
        structFieldRef etcdserverpb.TxnResponse go!"Succeeded" resp ↦ true ∗
        structFieldRef etcdserverpb.TxnResponse go!"Responses" resp ↦□ rsl ∗ rsl ↦*□ [p0] ∗
        ⌜p0 ≠ null⌝ ∗
        structFieldRef etcdserverpb.ResponseOp go!"Response" p0 ↦□
          interface.mkOk (go.GoType.PointerType etcdserverpb.ResponseOp_ResponseDeleteRange.ty) #w ∗
        structFieldRef etcdserverpb.ResponseOp_ResponseDeleteRange go!"ResponseDeleteRange" w ↦□ dr ∗
        ⌜dr ≠ null⌝ ∗ structFieldRef etcdserverpb.DeleteRangeResponse go!"Header" dr ↦ h0 ∗
        structFieldRef etcdserverpb.DeleteRangeResponse go!"Deleted" dr ↦□
          W64 ((rangeIn s o).length : Int) ∗
        etcdReached r ∗
        ⌜sint.Z lo ≤ sint.Z r ∧ 0 < sint.Z r ∧ sint.Z r < 2 ^ 63 - 1 ∧ EtcdStateWf [] s⌝ ∗
        txnStates [] r s (s.filter (fun v => !inRange o.key o.base.rangeEnd v.key))
          ((rangeIn s o).length != 0) := by
  unfold opCommitted txnRespOwn
  iintro ⟨%r, %s, %hm, %Hhm, ⟨%hdr, %sl, %ps, #HH, #Hhf, HS, #HR, #Hps, Hops⟩, #Hr, %Hf, #Hts⟩
  simp only [applyTxnOp_delete, TxnOpResult.wrote]
  cases ps with
  | nil => simp only [txnOpsRespOwn]; iexfalso; iexact Hops
  | cons p0 ps =>
  cases ps with
  | cons _ _ => simp only [txnOpsRespOwn]; icases Hops with ⟨-, Hf⟩; iexfalso; iexact Hf
  | nil =>
  simp only [txnOpsRespOwn, txnOpRespOwn]
  icases Hops with ⟨⟨%Hp0, %w, %dr, %h0, #Hw, #Hdr, %Hdrn, Hh0, #Hdel⟩, -⟩
  iexists r, s, hm, hdr, sl, p0, w, dr, h0
  iframe
  iframe #
  ipureintro
  exact ⟨Hhm, Hp0, Hdrn, Hf⟩

theorem rangeDeleteOp_key (key e : GoString) : (leasing.rangeDeleteOp key e).key = key := by
  simp [leasing.rangeDeleteOp, opDeleteModel, opFold, withRangeM, OpFull.deleteInit, OpFull.newOp]

theorem rangeDeleteOp_end (key e : GoString) : (leasing.rangeDeleteOp key e).base.rangeEnd = e := by
  simp [leasing.rangeDeleteOp, opDeleteModel, opFold, withRangeM, OpFull.deleteInit, OpFull.newOp]

end lemmas

end EtcdGrove
end Perennial
