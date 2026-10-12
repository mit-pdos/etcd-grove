/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.deleteRange
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.mkGteRange
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.metricsTxnWrite__Range
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.metricsTxnWrite__DeleteRange

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver
  go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

theorem txn.deleteRange.wp_proof
    (hGte : txn.mkGteRange.spec (GF := GF) (hG := hG))
    (hRange : mvcc.metricsTxnWrite.Range.spec (GF := GF) (hG := hG))
    (hDel : mvcc.metricsTxnWrite.DeleteRange.spec (GF := GF) (hG := hG)) :
    txn.deleteRange.spec (GF := GF) (hG := hG) := by
  intro ctx cd nd mw s γ ilog pend puts deletes putSize dr o
  wp_start as ⟨#Hctx, #Hnd, Htx, #Hdr, %Hbnd⟩
  ihave #Hmv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc $$ []
  · iPkgInit
  iunfold txn.deleteRangeRequestIs at Hdr
  icases Hdr with ⟨%Hdnn, %ksl, %esl, %k, %e, %pk, #Hk, #Hks, #He, #Hes, #Hpk, %Ho⟩
  -- the facts of the transaction
  ihave ⟨%Hfx, Htx⟩ := txn.isTxnWrite_facts mw s γ ilog pend puts deletes putSize $$ Htx
  ihave Htx : mvcc.isTxn mw s γ (.write ilog pend puts deletes putSize) $$ [Htx]
  · simp only [mvcc.isTxn]; iexact Htx
  ihave ⟨%Hok, Htx⟩ := txn.isTxn_kindOk mw s γ _ $$ Htx
  have hks := txn.kindState_write ilog pend puts deletes putSize Hfx.1 Hfx.2
  have hK : o.key = k := by subst Ho; rfl
  have hRE : o.base.rangeEnd = txn.rangeEndOf esl e := by subst Ho; rfl
  have hPK : o.base.prevKV = pk := by subst Ho; rfl
  ihave %Hlen := ownSlice_len _ _ _ $$ Hes
  have hnil : esl = slice.nil → e = [] := by
    intro h; subst h
    have h1 := Hlen.1
    rw [show sint.nat (slice.nil : GoSlice).len = 0 from rfl] at h1
    exact List.length_eq_zero_iff.1 h1
  wp_auto
  irename «$r0» => Hresp
  irename «$r0» => Hhdr
  ihave %Hrn := typedPointsto_not_null _ _ _ $$ Hresp
  ihave %Hhn := typedPointsto_not_null _ _ _ $$ Hhdr
  iStructNamedPrefix Hresp "R"
  iStructNamedPrefix Hhdr "H"
  wp_apply (hGte esl e) $$ [$Hes] as %endk ⟨#Hend, %Hendk⟩
  have hE := txn.srvEnd_mkGte esl endk e hnil Hendk
  rw [← hRE] at hE
  have hE1 : decide (endk = slice.nil) = (txn.srvEnd o.base.rangeEnd).1 := congrArg Prod.fst hE
  have hE2 : (if e = [W8 0] then [] else e) = (txn.srvEnd o.base.rangeEnd).2 := congrArg Prod.snd hE
  rw [hE2]
  (try wp_auto)
  -- what mvcc's `DeleteRange` deletes: the client's range
  have hok' : LogOk (ilog ++ [pend]) := Hok.1
  have hD : (mvcc.delKeys ilog pend (decide (endk = slice.nil)) k
        (txn.srvEnd o.base.rangeEnd).2).map mvcc.Change.del =
      txn.delChanges (txn.pendState ilog pend) o := by
    rw [hE1, ← hK]; exact txn.delKeys_client ilog pend hok' Hfx.1 o
  have hDlen : (mvcc.delKeys ilog pend (decide (endk = slice.nil)) k
        (txn.srvEnd o.base.rangeEnd).2).length = (rangeIn (txn.pendState ilog pend) o).length := by
    have := congrArg List.length hD
    simp only [List.length_map, txn.delChanges] at this
    exact this
  rw [hPK]
  cases pk
  · -- no `PrevKv`
    (try wp_auto)
    ihave Htx : mvcc.isTxnWrite mw s γ ilog pend puts deletes putSize $$ [Htx]
    · simp only [mvcc.isTxn]; iexact Htx
    iapply wp_fupd
    wp_apply (hDel mw s γ ilog pend puts deletes putSize ksl endk k (txn.srvEnd o.base.rangeEnd).2)
      $$ [$Htx $Hks $Hend] as %n %rev ⟨Htx, %Hnr⟩
    · ipureintro; rw [hDlen]; exact Hbnd
    rw [hD, hDlen] at Hnr
    rw [hD]
    obtain ⟨rfl, rfl⟩ := Hnr
    (try wp_auto)
    ipersist RHeader
    ipersist RPrevKvs
    ipersist HRevision
    ipersist RDeleted
    imodintro
    iapply HΦ
    ileft
    isplitl []
    · ipureintro; rfl
    isplitl [Htx]
    · iexists _; iexact Htx
    iunfold txn.deleteRangeResponseIs
    isplitl []
    · ipureintro; exact Hrn
    iexists _, _, []
    iframe RHeader HRevision RDeleted RPrevKvs
    isplitl []
    · ipureintro; exact Hhn
    isplitl []
    · iapply ownSlice_nil
    simp only [Bool.false_eq_true, ↓reduceIte]
    iapply txn.kvsIs_nil
  · -- `PrevKv`: the range read first
    (try wp_auto)
    icases mvcc.txnCtx_rangeCtx nd ctx cd $$ Hctx Hnd with ⟨%td, %Htd, #Hctx'⟩
    wp_apply (hRange mw s γ (.write ilog pend puts deletes putSize) ctx cd td ksl endk k
        (txn.srvEnd o.base.rangeEnd).2 (zero_val RangeOptions)) $$ [$Htx $Hctx' $Hks $Hend]
      as %rr %rerr ⟨%Hrn', Htx, Hout⟩
    imod txn.rangeOutcome_sel rr rerr _ _ k _ (zero_val RangeOptions) Hok ⟨rfl, rfl, rfl, rfl⟩
      $$ Hout with Hout
    rw [hks, hE1, ← hK, txn.srvSel_srvEnd, hK]
    icases Hout with (⟨%Hrnull, %Hne⟩ | ⟨%Herr, %kvs, %rv, %cnt, %ps, Hrr, Hkvs, #Hsel⟩)
    · -- the context done: nothing deleted
      cases rerr with
      | nil => exact absurd rfl Hne
      | ok ei =>
        (try wp_auto)
        iapply HΦ
        iright
        isplitl []
        · ipureintro
          refine ⟨Hne, rfl, rfl, ?_⟩
          cases nd
          · rfl
          · exact absurd Hrnull (Hrn' (Htd rfl))
        simp only [mvcc.isTxn]
        iexact Htx
    · subst Herr
      ihave %Hrrn := typedPointsto_not_null _ _ _ $$ Hrr
      iStructNamedPrefix Hrr "Q"
      ihave %Hkl := ownSlice_len _ _ _ $$ Hkvs
      (try wp_auto)
      rw [decide_eq_false Hrrn]
      (try wp_auto)
      wp_apply wp_slice_make2 (V := Loc) kvs.len as %nsl ⟨Hnsl, -⟩
      · ipureintro; exact Hkl.2
      (try wp_auto)
      wp_apply wp_slice_copy nsl _ kvs ps (DFrac.own 1) $$ [$Hnsl $Hkvs] as %nc ⟨-, Hnsl, -⟩
      have hps : ps.take (List.replicate (sint.nat kvs.len) (zero_val Loc)).length ++
          (List.replicate (sint.nat kvs.len) (zero_val Loc)).drop ps.length = ps := by
        rw [List.length_replicate, ← Hkl.1, List.take_length, List.drop_of_length_le (by simp [Hkl.1]),
          List.append_nil]
      rw [hps]
      (try wp_auto)
      ihave Htx : mvcc.isTxnWrite mw s γ ilog pend puts deletes putSize $$ [Htx]
      · simp only [mvcc.isTxn]; iexact Htx
      ipersist Hnsl
      iapply wp_fupd
      wp_apply (hDel mw s γ ilog pend puts deletes putSize ksl endk k
          (txn.srvEnd o.base.rangeEnd).2) $$ [$Htx $Hks $Hend] as %n %rev ⟨Htx, %Hnr⟩
      · ipureintro; rw [hDlen]; exact Hbnd
      rw [hD, hDlen] at Hnr
      rw [hD]
      obtain ⟨rfl, rfl⟩ := Hnr
      (try wp_auto)
      ipersist RHeader
      ipersist RPrevKvs
      ipersist HRevision
      ipersist RDeleted
      imodintro
      iapply HΦ
      ileft
      isplitl []
      · ipureintro; rfl
      isplitl [Htx]
      · iexists _; iexact Htx
      iunfold txn.deleteRangeResponseIs
      isplitl []
      · ipureintro; exact Hrn
      iexists _, _, ps
      iframe RHeader HRevision RDeleted RPrevKvs Hnsl
      isplitl []
      · ipureintro; exact Hhn
      simp only [↓reduceIte]
      iexact Hsel

end proof

end EtcdGrove
end Perennial
