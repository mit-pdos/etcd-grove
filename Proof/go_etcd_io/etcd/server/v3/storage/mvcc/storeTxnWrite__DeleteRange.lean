/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.storeTxnWrite__DeleteRange
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.storeTxnWrite__deleteRange

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.storeTxnWrite.DeleteRange.wp_proof
    (hdel : mvcc.storeTxnWrite.deleteRange.spec (GF := GF) (hG := hG)) :
    mvcc.storeTxnWrite.DeleteRange.spec (GF := GF) (hG := hG) := by
  intro tw s γ ilog pend key endk k e
  wp_start as ⟨Htw, #Hkey, #Hend, %Hb⟩
  have hpm := mvcc.putMax_le γ
  (try wp_auto)
  wp_apply (hdel tw s γ ilog pend key endk k e) $$ [$Htw $Hkey $Hend] as Htw
  · ipureintro; exact Hb
  (try wp_auto)
  iunfold mvcc.storeTxnWriteIs at Htw
  iNamed Htw
  (try wp_auto)
  generalize hks : mvcc.delKeys ilog pend (decide (endk = slice.nil)) k e = ks at *
  have hrev : (W64 ((ilog.length : Int) - 1) : w64) + W64 1 = W64 (ilog.length : Int) := by
    rw [← mvcc.W64_add_one]; simp
  ihave %Hlen := ownSlice_len chs (DFrac.own 1) ps $$ Hchs
  have hcl : chs.len = W64 ((pend ++ ks.map mvcc.Change.del).length : Int) := by
    rw [← Hps, Hlen.1]; exact (mvcc.W64_sint_nat chs.len Hlen.2).symm
  have hpend : pend ++ List.map Change.del ks = [] ↔ chs.len = 0 := by
    obtain ⟨h1, h2⟩ := Hlen
    constructor
    · intro h
      have hz : ps.length = 0 := by rw [Hps, h]; rfl
      rw [← mvcc.W64_sint_nat chs.len h2, ← h1, hz]; rfl
    · intro h
      rw [h] at h1
      exact List.length_eq_zero_iff.1 (by rw [← Hps, h1]; rfl)
  have hkslt : ks.length < 2 ^ 63 := by omega
  have hksZ : sint.Z (W64 (ks.length : Int) : w64) = ks.length := by
    unfold sint.Z W64
    rw [BitVec.toInt_ofInt_eq_self (by decide)
      (by rw [show (64 - 1 : Nat) = 63 from rfl]; omega)
      (by rw [show (64 - 1 : Nat) = 63 from rfl]; omega)]
  have hpZ : sint.Z (W64 (pend.length : Int) : w64) = pend.length := by
    unfold sint.Z W64
    rw [BitVec.toInt_ofInt_eq_self (by decide)
      (by rw [show (64 - 1 : Nat) = 63 from rfl]; omega)
      (by rw [show (64 - 1 : Nat) = 63 from rfl]; omega)]
  have h0Z : sint.Z (W64 0 : w64) = 0 := by decide
  -- `n != 0 || len(tw.changes) > 0`: first `n == 0`
  wp_if_destruct
  · -- `n == 0`: nothing deleted
    have hks0 : ks.length = 0 := by
      have h := congrArg sint.Z Hif
      rw [hksZ, h0Z] at h
      omega
    have hks : ks = [] := List.length_eq_zero_iff.1 hks0
    subst hks
    simp only [List.map_nil, List.append_nil] at *
    (try wp_auto)
    wp_if_destruct
    · -- `len(tw.changes) > 0`: the pending revision
      have hpne : pend ≠ [] := by
        intro h
        have hc : sint.Z (W64 0 : w64) < sint.Z chs.len := by
          first | exact Hif | (have := go.intoVal_inj Hif; simpa using this)
        rw [hcl, hpZ, h0Z] at hc
        rw [h] at hc
        simp at hc
      (try wp_auto)
      iapply HΦ
      isplitl [Htoks Htok Htw Hchs Hcap Hkvs Hlocked Hw Hclog Hcur Hbv Hmu HrevMu Hti Hrt Hcres Hlrd]
      iunfold mvcc.storeTxnWriteIs
      iexists trace, ti, bt, Locked, chs, ps, ntok
      simp only [named]
      iframe Htoks Htok Htw Hchs Hcap Hkvs Hlocked Hw Hclog Hcur Hbv Hmu HrevMu Hti Hrt Hcres Hlrd
      iframe #
      ipureintro; exact ⟨Hbudget, Hps, Hne, Htrnn⟩
      ipureintro
      refine ⟨rfl, ?_⟩
      rw [hrev]; unfold mvcc.writeRev; rw [ite_eq_right hpne]
    · -- no change: the committed log's last revision
      have hp : pend = [] := by
        have hc : ¬ sint.Z (W64 0 : w64) < sint.Z chs.len := by
          first | exact Hif | exact fun h => Hif (by rw [decide_eq_true h])
        rw [hcl, hpZ, h0Z] at hc
        apply List.length_eq_zero_iff.1
        omega
      (try wp_auto)
      iapply HΦ
      isplitl [Htoks Htok Htw Hchs Hcap Hkvs Hlocked Hw Hclog Hcur Hbv Hmu HrevMu Hti Hrt Hcres Hlrd]
      iunfold mvcc.storeTxnWriteIs
      iexists trace, ti, bt, Locked, chs, ps, ntok
      simp only [named]
      iframe Htoks Htok Htw Hchs Hcap Hkvs Hlocked Hw Hclog Hcur Hbv Hmu HrevMu Hti Hrt Hcres Hlrd
      iframe #
      ipureintro; exact ⟨Hbudget, Hps, Hne, Htrnn⟩
      ipureintro
      refine ⟨rfl, ?_⟩
      unfold mvcc.writeRev; rw [ite_eq_left hp]; congr 1
      have := List.length_pos_iff.2 Hne
      omega
  · -- `n != 0`: the pending revision
    have hks : ks ≠ [] := by
      intro h; subst h; exact Hif rfl
    (try wp_auto)
    iapply HΦ
    isplitl [Htoks Htok Htw Hchs Hcap Hkvs Hlocked Hw Hclog Hcur Hbv Hmu HrevMu Hti Hrt Hcres Hlrd]
    iunfold mvcc.storeTxnWriteIs
    iexists trace, ti, bt, Locked, chs, ps, ntok
    simp only [named]
    iframe Htoks Htok Htw Hchs Hcap Hkvs Hlocked Hw Hclog Hcur Hbv Hmu HrevMu Hti Hrt Hcres Hlrd
    iframe #
    ipureintro; exact ⟨Hbudget, Hps, Hne, Htrnn⟩
    ipureintro
    refine ⟨rfl, ?_⟩
    rw [hrev]; unfold mvcc.writeRev
    rw [ite_eq_right (by simp [hks])]

end proof

end EtcdGrove
end Perennial
