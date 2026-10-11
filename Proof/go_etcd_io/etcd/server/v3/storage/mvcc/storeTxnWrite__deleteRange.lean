/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.storeTxnWrite__deleteRange
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.treeIndex__Range
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.storeTxnWrite__delete

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [go_etcd_io.etcd.cache.v3.Assumptions]

theorem mvcc.storeTxnWrite.deleteRange.wp_proof
    (hRange : mvcc.treeIndex.Range.spec (GF := GF) (hG := hG))
    (hDel : mvcc.storeTxnWrite.delete.spec (GF := GF) (hG := hG)) :
    mvcc.storeTxnWrite.deleteRange.spec (GF := GF) (hG := hG) := by
  intro tw s γ ilog pend key endk k e
  wp_start as ⟨Htw, #Hkey, #Hend, %Hb⟩
  generalize hks : mvcc.delKeys ilog pend (decide (endk = slice.nil)) k e = ks at *
  iunfold mvcc.storeTxnWriteIs at Htw
  iNamed Htw
  ihave #Hs0 : mvcc.isStore s γ $$ []
  · iexact Hs
  iunfold mvcc.isStore at Hs
  iNamedSuffix Hs "S"
  icombine Hidx HidxS gives %Hti_eq
  have Hti_eq' := mvcc.mkOk_loc_inj _ Hti_eq
  subst Hti_eq'
  -- package facts: `ErrRevisionNotFound`, the `Key` bucket, zap, protobuf, traceutil
  ihave Hmi : (mvccInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hmi with ⟨⟨%e0, #Herr⟩, -, -, -, -, -, -, -, -⟩
  ihave #Hsch : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema $$ []
  · iPkgInit
  ihave Hsi : (go_etcd_io.etcd.server.v3.storage.schema.schemaInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hsch
  icases Hsi with ⟨-, -, -, ⟨%bK, #HKeyG⟩⟩
  ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Hproto : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto $$ []
  · iPkgInit
  ihave #Htu : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil $$ []
  · iPkgInit
  -- the lessor and the batch transaction
  iunfold mvcc.isLessor at HlessorS
  icases HlessorS with ⟨%li, %Hli, #HGetL, #HAttach, #HDetach⟩
  subst Hli
  ihave #Hbt0 : mvcc.batchTxSpec bt (mvcc.bucketView γ) (mvcc.writerRes s γ) Locked $$ []
  · iexact Hbt
  iunfold mvcc.batchTxSpec at Hbt
  icases Hbt with ⟨-, #HSeqPut, -, -⟩
  -- the writer's log
  ihave %Hwf := mvcc.idxWriter_wf γ.idx ilog pend $$ Hw
  obtain ⟨Hwf', Hlen, Hplen, Hcs⟩ := Hwf
  have hpos : 0 < ilog.length := List.length_pos_iff.2 Hne
  have hwfL : mvcc.LogWf (ilog ++ [pend]) := mvcc.LogWf.of_wf' Hwf' (by simp)
  have hlenL : (ilog ++ [pend]).length < 2 ^ 63 := by simp; omega
  have hcsL : ∀ cs ∈ ilog ++ [pend], cs.length < 2 ^ 63 := by
    intro cs hcs'
    rcases List.mem_append.1 hcs' with h | h
    · exact Hcs cs h
    · rw [List.mem_singleton] at h; rw [h]; exact Hplen
  have hrev : (W64 ((ilog.length : Int) - 1) : w64) + W64 1 = W64 (ilog.length : Int) := by
    rw [← mvcc.W64_add_one]; simp
  ihave %Hlen := ownSlice_len chs (DFrac.own 1) ps $$ Hchs
  have hcl : chs.len = W64 (pend.length : Int) := by
    rw [← Hps, Hlen.1]; exact (mvcc.W64_sint_nat chs.len Hlen.2).symm
  (try wp_auto)
  -- `rrev := tw.beginRev; if len(tw.changes) > 0 { rrev++ }`
  wp_if_destruct
  · -- a change: the pending revision
    have hpend : pend ≠ [] := by
      intro h; subst h
      rw [hcl] at Hif
      first | (simp at Hif) | exact absurd Hif (by decide)
    (try wp_auto)
    rw [show (W64 ((ilog.length : Int) - 1) : w64) + W64 1 =
        W64 ((mvcc.writeRev ilog pend : Nat) : Int) by
      rw [hrev]; unfold mvcc.writeRev; rw [if_neg hpend]]
    -- `keys, _, _, _, _ := tw.s.kvindex.Range(key, end, rrev, 0, false)` by the writer
    ihave Hkn : mvcc.idxKnows γ.idx (.writer ilog pend) $$ [Hw]
    · rw [mvcc.idxKnows_writer]; iexact Hw
    wp_apply (hRange ti γ.idx (.writer ilog pend) key endk k e
      (W64 ((mvcc.writeRev ilog pend : Nat) : Int)) (W64 0) false e0)
      $$ [$HtiS $Hti $Hkn $Hkey $Hend $Herr]
      as %keys %modifies %creates %vers %total
        ⟨Hti, Hw, Hkeys, Hmod, Hmodcap, Hcre, Hcrecap, Hvers, Hverscap, %Htotal⟩
    · ipureintro
      rw [mvcc.IdxKnow.log_writer]
      have := mvcc.writeRev_lt ilog pend Hne
      constructor <;> word
    rw [mvcc.idxKnows_writer, mvcc.IdxKnow.log_writer]
    have hks' : (mvcc.rangeTaken (ilog ++ [pend]) (decide (endk = slice.nil)) k e
        (W64 ((mvcc.writeRev ilog pend : Nat) : Int)) (W64 0)).map Prod.fst = ks := hks
    rw [hks']
    (try wp_auto)
    iunfold mvcc.ownKeys at Hkeys
    icases Hkeys with ⟨%kss, Hkss, Hkscap, %Hklen, #Hkz⟩
    ihave %Hkl := ownSlice_len keys (DFrac.own 1) kss $$ Hkss
    have hkeyslen : keys.len = W64 (ks.length : Int) := by
      rw [← Hklen, Hkl.1]; exact (mvcc.W64_sint_nat keys.len Hkl.2).symm
    trace_state
    -- `if len(keys) == 0 { return 0 }`
    wp_if_destruct
    · -- no key
      have hnil : ks = [] := by
        apply List.length_eq_zero_iff.1
        have h := congrArg BitVec.toNat Hif
        rw [hkeyslen] at h
        first | (simpa using h) | sorry
      subst hnil
      simp only [List.map_nil, List.append_nil] at *
      (try wp_auto)
      iapply HΦ
      iunfold mvcc.storeTxnWriteIs
      iexists trace, ti, bt, Locked, chs, ps, ntok
      simp only [named]
      iframe Htoks Htok Htw Hchs Hcap Hkvs Hlocked Hw Hclog Hcur Hmu HrevMu Hti
      iframe #
      ipureintro; exact ⟨Hbudget, Hps, Hne⟩
    · -- the loop: `for _, key := range keys { tw.delete(key) }`
      have hpres := mvcc.delKeys_present ilog pend (decide (endk = slice.nil)) k e hwfL hlenL hcsL Hne
      have hnodup := mvcc.delKeys_nodup ilog pend (decide (endk = slice.nil)) k e
      rw [hks] at hpres hnodup
      ihave Htx : mvcc.storeTxnWriteIs tw s γ ilog pend
          $$ [Htoks Htok Htw Hchs Hcap Hkvs Hlocked Hw Hclog Hcur Hmu HrevMu Hti]
      · iunfold mvcc.storeTxnWriteIs
        iexists trace, ti, bt, Locked, chs, ps, ntok
        simp only [named]
        iframe Htoks Htok Htw Hchs Hcap Hkvs Hlocked Hw Hclog Hcur Hmu HrevMu Hti
        iframe #
        ipureintro; exact ⟨Hbudget, Hps, Hne⟩
      trace_state
      ihave IH : iprop(∃ j : Nat,
          "i" ∷ i_ptr ↦ (W64 (j : Int) : w64) ∗
          "%Hj" ∷ ⌜j ≤ ks.length⌝ ∗
          "Htx" ∷ mvcc.storeTxnWriteIs tw s γ ilog (pend ++ (ks.take j).map .del)) $$ [i Htx]
      · iexists 0
        simp only [named, List.take_zero, List.map_nil, List.append_nil]
        rw [show (W64 ((0 : Nat) : Int) : w64) = W64 0 from rfl]
        iframe i Htx
        ipureintro; omega
      wp_for IH
      wp_if_destruct
      · -- `i < len(keys)`: `tw.delete(keys[i])`
        have hjlt : j < ks.length := by
          rw [hkeyslen] at Hif
          word
        obtain ⟨kw, hkw⟩ : ∃ kw, kss[j]? = some kw := ⟨_, List.getElem?_eq_getElem (by omega)⟩
        obtain ⟨kj, hkj⟩ : ∃ kj, ks[j]? = some kj := ⟨_, List.getElem?_eq_getElem hjlt⟩
        have Hbnd : 0 ≤ sint.Z (W64 (j : Int) : w64) ∧ sint.Z (W64 (j : Int) : w64) < sint.Z keys.len := by
          rw [hkeyslen]; constructor <;> word
        simp only [Hbnd, and_self, ↓reduceIte]
        wp_apply wp_load_slice_index keys (sint.Z (W64 (j : Int) : w64)) _ (DFrac.own 1) kw Hbnd.1
          $$ [Hkss] as Hkss
        · iframe; ipureintro
          rw [show (sint.Z (W64 (j : Int) : w64)).toNat = j by word]; exact hkw
        ihave #Hkj : (kw ↦*□ kj : IProp GF) $$ []
        · iapply (BigSepL.bigSepL_lookup (l := kss.zip ks) (i := j) (x := (kw, kj)) ?_) $$ Hkz
          rw [List.getElem?_zip_eq_some]; exact ⟨hkw, hkj⟩
        (try wp_auto)
        have hmem : kj ∈ ks := List.mem_of_getElem? hkj
        have hnot : kj ∉ ks.take j := by
          intro hin
          have hnd := List.nodup_iff_getElem?_ne_getElem?.1 hnodup
          obtain ⟨j', hj', hget⟩ := List.mem_iff_getElem.1 hin
          rw [List.getElem_take] at hget
          rw [List.length_take] at hj'
          exact hnd j' j (by omega) (by omega) (by rw [List.getElem?_eq_getElem (by omega), hget, hkj])
        wp_apply (hDel tw s γ ilog (pend ++ (ks.take j).map .del) kw kj) $$ [$Htx $Hkj] as Htx
        · ipureintro
          refine ⟨?_, by simp [List.length_take]; omega⟩
          rw [show mvcc.applyChanges (W64 (ilog.length : Int)) (mvcc.stateAfter ilog)
              (pend ++ (ks.take j).map .del) =
            mvcc.applyChanges (W64 (ilog.length : Int))
              (mvcc.applyChanges (W64 (ilog.length : Int)) (mvcc.stateAfter ilog) pend)
              ((ks.take j).map .del) by unfold mvcc.applyChanges; rw [List.foldl_append]]
          rw [mvcc.findKey_applyChanges_dels _ _ _ _ hnot]
          exact hpres kj hmem
        (try wp_auto)
        wp_for_post
        iexists (j + 1)
        simp only [named]
        rw [List.take_succ, hkj, Option.toList_some, List.map_append, List.map_singleton,
          ← List.append_assoc]
        iframe Htx
        rw [show (W64 (j : Int) : w64) + W64 1 = W64 ((j + 1 : Nat) : Int) by
          rw [← mvcc.W64_add_one]; simp]
        iframe i
        ipureintro; omega
      · -- the loop is done: every key deleted
        have hj : j = ks.length := by
          rw [hkeyslen] at Hif
          have : ¬ (j : Int) < ks.length := fun h => Hif (by word)
          omega
        subst hj
        rw [List.take_length]
        (try wp_auto)
        rw [hkeyslen]
        iapply HΦ
        iexact Htx
  · -- no change yet: the committed log's last revision
    have hpend : pend = [] := by
      rw [hcl] at Hif
      first | (apply List.length_eq_zero_iff.1; word) | sorry
    (try wp_auto)
    rw [show (W64 ((ilog.length : Int) - 1) : w64) = W64 ((mvcc.writeRev ilog pend : Nat) : Int) by
      unfold mvcc.writeRev; rw [if_pos hpend]; exact congrArg W64 (by omega)]
    -- `keys, _, _, _, _ := tw.s.kvindex.Range(key, end, rrev, 0, false)` by the writer
    ihave Hkn : mvcc.idxKnows γ.idx (.writer ilog pend) $$ [Hw]
    · rw [mvcc.idxKnows_writer]; iexact Hw
    wp_apply (hRange ti γ.idx (.writer ilog pend) key endk k e
      (W64 ((mvcc.writeRev ilog pend : Nat) : Int)) (W64 0) false e0)
      $$ [$HtiS $Hti $Hkn $Hkey $Hend $Herr]
      as %keys %modifies %creates %vers %total
        ⟨Hti, Hw, Hkeys, Hmod, Hmodcap, Hcre, Hcrecap, Hvers, Hverscap, %Htotal⟩
    · ipureintro
      rw [mvcc.IdxKnow.log_writer]
      have := mvcc.writeRev_lt ilog pend Hne
      constructor <;> word
    rw [mvcc.idxKnows_writer, mvcc.IdxKnow.log_writer]
    have hks' : (mvcc.rangeTaken (ilog ++ [pend]) (decide (endk = slice.nil)) k e
        (W64 ((mvcc.writeRev ilog pend : Nat) : Int)) (W64 0)).map Prod.fst = ks := hks
    rw [hks']
    (try wp_auto)
    iunfold mvcc.ownKeys at Hkeys
    icases Hkeys with ⟨%kss, Hkss, Hkscap, %Hklen, #Hkz⟩
    ihave %Hkl := ownSlice_len keys (DFrac.own 1) kss $$ Hkss
    have hkeyslen : keys.len = W64 (ks.length : Int) := by
      rw [← Hklen, Hkl.1]; exact (mvcc.W64_sint_nat keys.len Hkl.2).symm
    trace_state
    -- `if len(keys) == 0 { return 0 }`
    wp_if_destruct
    · -- no key
      have hnil : ks = [] := by
        apply List.length_eq_zero_iff.1
        have h := congrArg BitVec.toNat Hif
        rw [hkeyslen] at h
        first | (simpa using h) | sorry
      subst hnil
      simp only [List.map_nil, List.append_nil] at *
      (try wp_auto)
      iapply HΦ
      iunfold mvcc.storeTxnWriteIs
      iexists trace, ti, bt, Locked, chs, ps, ntok
      simp only [named]
      iframe Htoks Htok Htw Hchs Hcap Hkvs Hlocked Hw Hclog Hcur Hmu HrevMu Hti
      iframe #
      ipureintro; exact ⟨Hbudget, Hps, Hne⟩
    · -- the loop: `for _, key := range keys { tw.delete(key) }`
      have hpres := mvcc.delKeys_present ilog pend (decide (endk = slice.nil)) k e hwfL hlenL hcsL Hne
      have hnodup := mvcc.delKeys_nodup ilog pend (decide (endk = slice.nil)) k e
      rw [hks] at hpres hnodup
      ihave Htx : mvcc.storeTxnWriteIs tw s γ ilog pend
          $$ [Htoks Htok Htw Hchs Hcap Hkvs Hlocked Hw Hclog Hcur Hmu HrevMu Hti]
      · iunfold mvcc.storeTxnWriteIs
        iexists trace, ti, bt, Locked, chs, ps, ntok
        simp only [named]
        iframe Htoks Htok Htw Hchs Hcap Hkvs Hlocked Hw Hclog Hcur Hmu HrevMu Hti
        iframe #
        ipureintro; exact ⟨Hbudget, Hps, Hne⟩
      trace_state
      ihave IH : iprop(∃ j : Nat,
          "i" ∷ i_ptr ↦ (W64 (j : Int) : w64) ∗
          "%Hj" ∷ ⌜j ≤ ks.length⌝ ∗
          "Htx" ∷ mvcc.storeTxnWriteIs tw s γ ilog (pend ++ (ks.take j).map .del)) $$ [i Htx]
      · iexists 0
        simp only [named, List.take_zero, List.map_nil, List.append_nil]
        rw [show (W64 ((0 : Nat) : Int) : w64) = W64 0 from rfl]
        iframe i Htx
        ipureintro; omega
      wp_for IH
      wp_if_destruct
      · -- `i < len(keys)`: `tw.delete(keys[i])`
        have hjlt : j < ks.length := by
          rw [hkeyslen] at Hif
          word
        obtain ⟨kw, hkw⟩ : ∃ kw, kss[j]? = some kw := ⟨_, List.getElem?_eq_getElem (by omega)⟩
        obtain ⟨kj, hkj⟩ : ∃ kj, ks[j]? = some kj := ⟨_, List.getElem?_eq_getElem hjlt⟩
        have Hbnd : 0 ≤ sint.Z (W64 (j : Int) : w64) ∧ sint.Z (W64 (j : Int) : w64) < sint.Z keys.len := by
          rw [hkeyslen]; constructor <;> word
        simp only [Hbnd, and_self, ↓reduceIte]
        wp_apply wp_load_slice_index keys (sint.Z (W64 (j : Int) : w64)) _ (DFrac.own 1) kw Hbnd.1
          $$ [Hkss] as Hkss
        · iframe; ipureintro
          rw [show (sint.Z (W64 (j : Int) : w64)).toNat = j by word]; exact hkw
        ihave #Hkj : (kw ↦*□ kj : IProp GF) $$ []
        · iapply (BigSepL.bigSepL_lookup (l := kss.zip ks) (i := j) (x := (kw, kj)) ?_) $$ Hkz
          rw [List.getElem?_zip_eq_some]; exact ⟨hkw, hkj⟩
        (try wp_auto)
        have hmem : kj ∈ ks := List.mem_of_getElem? hkj
        have hnot : kj ∉ ks.take j := by
          intro hin
          have hnd := List.nodup_iff_getElem?_ne_getElem?.1 hnodup
          obtain ⟨j', hj', hget⟩ := List.mem_iff_getElem.1 hin
          rw [List.getElem_take] at hget
          rw [List.length_take] at hj'
          exact hnd j' j (by omega) (by omega) (by rw [List.getElem?_eq_getElem (by omega), hget, hkj])
        wp_apply (hDel tw s γ ilog (pend ++ (ks.take j).map .del) kw kj) $$ [$Htx $Hkj] as Htx
        · ipureintro
          refine ⟨?_, by simp [List.length_take]; omega⟩
          rw [show mvcc.applyChanges (W64 (ilog.length : Int)) (mvcc.stateAfter ilog)
              (pend ++ (ks.take j).map .del) =
            mvcc.applyChanges (W64 (ilog.length : Int))
              (mvcc.applyChanges (W64 (ilog.length : Int)) (mvcc.stateAfter ilog) pend)
              ((ks.take j).map .del) by unfold mvcc.applyChanges; rw [List.foldl_append]]
          rw [mvcc.findKey_applyChanges_dels _ _ _ _ hnot]
          exact hpres kj hmem
        (try wp_auto)
        wp_for_post
        iexists (j + 1)
        simp only [named]
        rw [List.take_succ, hkj, Option.toList_some, List.map_append, List.map_singleton,
          ← List.append_assoc]
        iframe Htx
        rw [show (W64 (j : Int) : w64) + W64 1 = W64 ((j + 1 : Nat) : Int) by
          rw [← mvcc.W64_add_one]; simp]
        iframe i
        ipureintro; omega
      · -- the loop is done: every key deleted
        have hj : j = ks.length := by
          rw [hkeyslen] at Hif
          have : ¬ (j : Int) < ks.length := fun h => Hif (by word)
          omega
        subst hj
        rw [List.take_length]
        (try wp_auto)
        rw [hkeyslen]
        iapply HΦ
        iexact Htx

end proof

end EtcdGrove
end Perennial
