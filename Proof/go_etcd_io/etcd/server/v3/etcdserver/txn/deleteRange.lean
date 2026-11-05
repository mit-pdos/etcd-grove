/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).

Strict M1 (2026-11-05): over mvcc's API (`Txn.Range`, `Txn.DeleteRange` at the transaction's dynamic
type; gaps A and F fixed: the read log's facts from their posts).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.deleteRange
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.mkGteRange
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.ApiLemmas

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.server.v3.etcdserver.txn
  go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.storage.mvcc
open mvcc.api (MvccState MTxn MvccName)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

theorem txn.deleteRange.wp_proof
    (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (hGte : txn.mkGteRange.spec (GF := GF) (hG := hG))
    : txn.deleteRange.spec (GF := GF) (hG := hG) := by
  intro ctx cd nd tw γ trace te σ pend dr o L
  wp_start as ⟨#Hctx, #Hnd, Htx, Htrc, %Hreach, #Hdr, Hown⟩
  icases txn.mvccTxn_shape hsh tw γ trace (.write σ pend) $$ Htx with ⟨%Hsh, Htx⟩
  obtain ⟨tyX, vX, rfl, -, -, hRangeC, -, hDelC, -, -⟩ := Hsh
  have h2 := txn.reach_len _ Hreach.1
  have h3 := Hreach.2
  have hne : σ.log ≠ [] := by intro h0; rw [h0] at h2; simp at h2
  ihave #Hmv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc $$ []
  · iPkgInit
  iunfold txn.deleteRangeRequestIs at Hdr
  icases Hdr with ⟨%Hdnn, %ksl, %esl, %k, %e, %pk, #Hk, #Hks, #He, #Hes, #Hpk, %Ho, -⟩
  have hks := txn.kindState_write σ pend hne (by omega)
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
  have hD0 : LogOk (σ.log ++ [pend]) → (mvcc.delKeys σ.log pend (decide (endk = slice.nil)) k
        (txn.srvEnd o.base.rangeEnd).2).map mvcc.Change.del =
      txn.delChanges (txn.pendState σ.log pend) o := by
    intro hok'; rw [hE1, ← hK]; exact txn.delKeys_client σ.log pend hok' hne o
  have hDlen0 : LogOk (σ.log ++ [pend]) → (mvcc.delKeys σ.log pend (decide (endk = slice.nil)) k
        (txn.srvEnd o.base.rangeEnd).2).length = (rangeIn (txn.pendState σ.log pend) o).length := by
    intro hok'
    have := congrArg List.length (hD0 hok')
    simp only [List.length_map, txn.delChanges] at this
    exact this
  rw [hPK]
  cases pk
  · -- no `PrevKv`
    (try wp_auto)
    iapply wp_fupd
    wp_apply (hDelC γ trace σ pend ksl endk k (txn.srvEnd o.base.rangeEnd).2 L)
      $$ [$Htx $Hks $Hend $Hown] as %n %rev ⟨Htx, Hown, %Hnr, %Hlwf'⟩
    have hok' := txn.logOk_of_del σ pend _ Hreach Hlwf'.1 Hlwf'.2
    have hD := hD0 hok'
    rw [hD, show (txn.delChanges (txn.pendState σ.log pend) o).length =
      (rangeIn (txn.pendState σ.log pend) o).length by simp [txn.delChanges]] at Hnr
    rw [hD]
    obtain ⟨rfl, rfl⟩ := Hnr
    (try wp_auto)
    ipersist RHeader
    ipersist RPrevKvs
    ipersist HRevision
    ipersist RDeleted
    imodintro
    iapply HΦ
    iframe Htrc
    ileft
    iframe Hown
    isplitl []
    · ipureintro; rfl
    isplitl [Htx]
    · iexact Htx
    isplitr [HClusterId HMemberId HRaftTerm HLeaderId]
    rotate_left
    · iunfold txn.respHdrOwn; iexists _; iframe RHeader
      isplitr; · ipureintro; exact Hhn
      iexists _, _, _, _; iframe
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
    wp_apply (hRangeC γ trace te (.write σ pend) ctx cd td ksl endk k
        (txn.srvEnd o.base.rangeEnd).2 (zero_val RangeOptions)) $$ [$Htx $Htrc $Hctx' $Hks $Hend]
      as %rr %rerr ⟨%Hrn', Htx, Htrc, Hout, -, %Hlwf⟩
    have Hok := txn.kindOk_of (.write σ pend) Hreach Hlwf.1 Hlwf.2
    -- (M2, S1) a read at the transaction's revision is never compacted
    have Hcr := txn.crev_le_readRev (.write σ pend) Hreach
    ihave Hout := mvcc.rangeOutcomeC_latest _ _ _ _ _ _ _ _ (zero_val RangeOptions)
      (by rw [show (zero_val RangeOptions).Rev' = W64 0 from rfl]; decide) Hcr $$ Hout
    clear Hcr
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
        iframe Htrc
        iright
        iframe Hown Htx
        ipureintro
        refine ⟨Hne, rfl, rfl, ?_⟩
        cases nd
        · rfl
        · exact absurd Hrnull (Hrn' (Htd rfl))
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
      ipersist Hnsl
      iapply wp_fupd
      wp_apply (hDelC γ trace σ pend ksl endk k (txn.srvEnd o.base.rangeEnd).2 L)
        $$ [$Htx $Hks $Hend $Hown] as %n %rev ⟨Htx, Hown, %Hnr, %Hlwf'⟩
      have hok' := txn.logOk_of_del σ pend _ Hreach Hlwf'.1 Hlwf'.2
      have hD := hD0 hok'
      rw [hD, show (txn.delChanges (txn.pendState σ.log pend) o).length =
        (rangeIn (txn.pendState σ.log pend) o).length by simp [txn.delChanges]] at Hnr
      rw [hD]
      obtain ⟨rfl, rfl⟩ := Hnr
      (try wp_auto)
      ipersist RHeader
      ipersist RPrevKvs
      ipersist HRevision
      ipersist RDeleted
      imodintro
      iapply HΦ
      iframe Htrc
      ileft
      iframe Hown
      isplitl []
      · ipureintro; rfl
      isplitl [Htx]
      · iexact Htx
      isplitr [HClusterId HMemberId HRaftTerm HLeaderId]
      rotate_left
      · iunfold txn.respHdrOwn; iexists _; iframe RHeader
        isplitr; · ipureintro; exact Hhn
        iexists _, _, _, _; iframe
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
