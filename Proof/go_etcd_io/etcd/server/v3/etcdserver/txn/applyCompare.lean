/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.applyCompare
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.mkGteRange
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.compareKV
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.metricsTxnWrite__Range
public import Spec.context.TODO
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.RangeLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver
  go_etcd_io.etcd.server.v3.storage.mvcc go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

theorem txn.applyCompare.wp_proof
    (hTODO : context.TODO.spec (GF := GF) (hG := hG))
    (hGte : txn.mkGteRange.spec (GF := GF) (hG := hG))
    (hRange : mvcc.metricsTxnWrite.Range.spec (GF := GF) (hG := hG))
    (hKV : txn.compareKV.spec (GF := GF) (hG := hG)) :
    txn.applyCompare.spec (GF := GF) (hG := hG) := by
  have hRange := mvcc.metricsTxnWrite.Range.spec_frozen hRange
  intro mw s γ log rev c cm
  wp_start as ⟨Htx, #Hc⟩
  ihave #Hc2 := Hc
  iunfold txn.compareIs at Hc2
  icases Hc2 with ⟨%Hcn, %ksl, %esl, %e, %u, #Hres, #Htgt, #Hk, #Hks, #He, #Hes, %Hre, #Hu, #Hun⟩
  icases txn.isTxnRead_pure mw s γ log rev $$ Htx with ⟨Htx, %Hlog⟩
  ihave #Hmv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc $$ []
  · iPkgInit
  ihave %Hesl := ownSlice_len _ _ _ $$ Hes
  have hnil : esl = slice.nil → e = [] := by
    intro h; subst h
    have h1 := Hesl.1
    rw [show sint.nat (slice.nil : GoSlice).len = 0 from rfl] at h1
    exact List.length_eq_zero_iff.1 h1
  wp_auto
  wp_apply hTODO
  wp_apply (hGte esl e) $$ [$Hes] as %esl' ⟨#Hes', %Hgte⟩
  have Hend := (txn.srvEnd_mkGte esl esl' e hnil Hgte)
  rw [← Hre] at Hend
  generalize (if e = [W8 0] then [] else e) = e' at Hend ⊢
  ihave Htx : mvcc.isTxn mw s γ (.read log rev) $$ [Htx]
  · simp only [mvcc.isTxn]; iexact Htx
  ihave #Hctx : mvcc.rangeCtx true todoCtxVal txn.todoCd $$ []
  · simp only [mvcc.rangeCtx, ↓reduceIte]; ileft; iapply mvcc.doneNil_todo
  wp_apply (hRange mw s γ (.read log rev) todoCtxVal txn.todoCd true ksl esl' cm.key e'
      (zero_val go_etcd_io.etcd.server.v3.storage.mvcc.RangeOptions)) $$ [$Htx $Hctx $Hks $Hes']
    as %rr %err ⟨%Hrn, Htx, Hout⟩
  ihave ⟨%Hok, Htx⟩ := txn.isTxn_kindOk mw s γ _ $$ Htx
  imod txn.rangeOutcome_sel rr err _ _ cm.key _ _ Hok ⟨rfl, rfl, rfl, rfl⟩ $$ Hout with Hout
  icases Hout with (⟨%Hrnull, %Hne⟩ | ⟨%Herr, %kvs, %rv', %cnt, %ps, Hrr, Hkvs, #Hsel⟩)
  · exact absurd Hrnull (Hrn rfl)
  subst Herr
  have hst : txn.kindState (.read log rev) = mvcc.stateAfter log := by
    unfold txn.kindState
    simp only [mvcc.TxnKind.readLog, mvcc.TxnKind.readRev]
    rw [Hlog.2.2]
    exact txn.stateAt_lastRev log Hlog.2.1 (by have := Hlog.1.len; omega)
  have hsel : txn.srvSel (txn.kindState (.read log rev)) (decide (esl' = slice.nil)) cm.key e' =
      (mvcc.stateAfter log).filter (fun v => inRange cm.key cm.rangeEnd v.key) := by
    rw [hst]
    have h1 : decide (esl' = slice.nil) = (txn.srvEnd cm.rangeEnd).1 := congrArg Prod.fst Hend
    have h2 : e' = (txn.srvEnd cm.rangeEnd).2 := congrArg Prod.snd Hend
    rw [h1, h2]
    unfold txn.srvSel
    apply List.filter_congr
    intro v _
    exact txn.srvInRange_srvEnd _ _ _
  rw [hsel]
  have hH : cmpHolds (mvcc.stateAfter log) cm =
      let sel := (mvcc.stateAfter log).filter (fun v => inRange cm.key cm.rangeEnd v.key)
      if sel = [] then (cm.target != .value) && cmpKv cm (zeroKv cm.key) else sel.all (cmpKv cm) := by
    rfl
  rw [hH]
  simp only
  generalize (mvcc.stateAfter log).filter (fun v => inRange cm.key cm.rangeEnd v.key) = sel
  ihave Htx : mvcc.isTxnRead mw s γ log rev $$ [Htx]
  · simp only [mvcc.isTxn]; iexact Htx
  iStructNamedPrefix Hrr "Q"
  ihave #Hnil : (slice.nil ↦*□ ([] : List w8) : IProp GF) $$ []
  · iapply ownSlice_nil
  ihave %Hkl := ownSlice_len _ _ _ $$ Hkvs
  iunfold txn.kvsIs at Hsel
  icases Hsel with ⟨%Hpl, #Hsel⟩
  wp_auto
  wp_if_destruct
  · -- no key-value in the range
    have hsel0 : sel = [] := by
      have : ps.length = 0 := by rw [Hkl.1, Hif]; rfl
      exact List.length_eq_zero_iff.1 (by omega)
    simp only [hsel0, ↓reduceIte]
    cases ht : cm.target
    all_goals simp only [ht, CmpTarget.code] at *
    all_goals wp_auto
    all_goals first
      | (simp only [bne_self_eq_false, Bool.false_and]; iapply HΦ; iframe Htx; done)
      | (ihave Hz := «$a1»
         iStructNamedPrefix Hz "Z"
         ipersist ZKey
         ipersist ZCreateRevision
         ipersist ZModRevision
         ipersist ZVersion
         ipersist ZValue
         ipersist ZLease
         ihave #Hz : txn.kvIs «$a1_ptr» (zeroKv []) $$ []
         · iunfold txn.kvIs
           iexists slice.nil, slice.nil
           simp only [zeroKv]
           isplitr; · iexact ZKey
           isplitr; · iexact Hnil
           isplitr; · iExactEq ZCreateRevision; rfl
           isplitr; · iExactEq ZModRevision; rfl
           isplitr; · iExactEq ZVersion; rfl
           isplitr; · iexact ZValue
           isplitr; · iexact Hnil
           iExactEq ZLease; rfl
         wp_apply (hKV c «$a1_ptr» cm (zeroKv [])) $$ [$Hc $Hz]
         have hz : cmpKv cm (zeroKv []) = cmpKv cm (zeroKv cm.key) := by
           unfold cmpKv zeroKv; rfl
         ihave H := HΦ $$ Htx
         iExactEq H
         rw [hz]
         congr 2
         try simp (config := {decide := true}))
  · have hne : sel ≠ [] := by
      intro h
      apply Hif
      have h0 : ps.length = 0 := by rw [Hpl, h]; rfl
      have h1 := Hkl.1; have h2 := Hkl.2
      rw [h0] at h1
      word
    simp only [hne, ↓reduceIte]
    ihave IH : (∃ (n : w64) (kvv : Loc), "i" ∷ i_ptr ↦ n ∗ "kv" ∷ kv_ptr ↦ kvv ∗
        "Hkvs" ∷ kvs ↦* ps ∗
        "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z kvs.len ∧
          ∀ j < sint.nat n, ∀ v, sel[j]? = some v → cmpKv cm v = true⌝ : IProp GF) $$ [i kv Hkvs]
    · iexists W64 0, _
      iframe
      ipureintro; refine ⟨by decide, Hkl.2, fun j hj => by simp at hj; omega⟩
    wp_for IH
    wp_if_destruct
    · obtain ⟨hn0, hnl, hall⟩ := Hn
      have hlt : sint.nat n < ps.length := by have := Hkl.1; word
      list_elem ps (sint.nat n) as p
      list_elem sel (sint.nat n) as v
      simp only [show (0 ≤ sint.Z n ∧ sint.Z n < sint.Z kvs.len) from ⟨hn0, Hif⟩, _root_.and_self, ite_true]
      wp_apply wp_load_slice_index kvs (sint.Z n) ps (DFrac.own 1) p hn0 $$ [Hkvs] as Hkvs
      · iframe; ipureintro; exact Hp_lookup
      ihave #Hpv := Hsel $$ %(sint.nat n) %p %v %Hp_lookup %Hv_lookup
      wp_apply (hKV c p cm v) $$ [$Hc $Hpv]
      cases hb : cmpKv cm v
      · wp_auto
        wp_for_post
        have : sel.all (cmpKv cm) = false := by
          rw [Bool.eq_false_iff]
          intro h
          rw [List.all_eq_true] at h
          rw [h v (List.mem_of_getElem? Hv_lookup)] at hb
          cases hb
        rw [this]
        iapply HΦ
        iframe Htx
      · wp_auto
        wp_for_post
        iframe
        iexists n + W64 1, p
        iframe
        ipureintro
        refine ⟨by word, by word, ?_⟩
        intro j hj w hw
        have hsn : sint.nat (n + W64 1) = sint.nat n + 1 := by word
        rw [hsn] at hj
        by_cases hjn : j = sint.nat n
        · subst hjn; rw [Hv_lookup] at hw; cases hw; exact hb
        · exact hall j (by omega) w hw
    · obtain ⟨hn0, hnl, hall⟩ := Hn
      have : sel.all (cmpKv cm) = true := by
        rw [List.all_eq_true]
        intro w hw
        obtain ⟨j, hj, hjw⟩ := List.getElem_of_mem hw
        exact hall j (by have := Hkl.1; word) w (by rw [List.getElem?_eq_getElem hj, hjw])
      rw [this]
      iapply HΦ
      iframe Htx

end proof

end EtcdGrove
end Perennial
