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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
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
  icases HlessorS with ⟨%li, %Hli, #HGetL, #HAttach, #HDetach, -⟩
  subst Hli
  ihave #Hbt0 : mvcc.batchTxSpec bt (mvcc.bucketView γ) (mvcc.writerRes s γ) Locked $$ []
  · iexact Hbt
  iunfold mvcc.batchTxSpec at Hbt
  icases Hbt with ⟨-, #HSeqPut, -, -, -⟩
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
  ihave %Hchl := ownSlice_len chs (DFrac.own 1) ps $$ Hchs
  have hcl : chs.len = W64 (pend.length : Int) := by
    rw [← Hps, Hchl.1]; exact (mvcc.W64_sint_nat chs.len Hchl.2).symm
  (try wp_auto)
  -- `rrev := tw.beginRev; if len(tw.changes) > 0 { rrev++ }`
  wp_if_destruct
  · -- a change: the pending revision
    have hpend : pend ≠ [] := by
      intro h; subst h
      rw [hcl] at Hif
      first | (simp at Hif) | exact absurd Hif (by decide)
    (try wp_auto)
    (try rw [hrev])
    have hwr : (W64 ((mvcc.writeRev ilog pend : Nat) : Int) : w64) = W64 (ilog.length : Int) := by
      unfold mvcc.writeRev; rw [if_neg hpend]
    have hks' : (mvcc.rangeTaken (ilog ++ [pend]) (decide (endk = slice.nil)) k e (W64 (ilog.length : Int)) (W64 0)).map
        Prod.fst = ks := by
      rw [← hwr]; exact hks
    have hrr : 0 ≤ sint.Z ((W64 (ilog.length : Int)) : w64) ∧ sint.Z ((W64 (ilog.length : Int)) : w64) < ((ilog ++ [pend]).length : Int) := by
      have := mvcc.writeRev_lt ilog pend Hne
      rw [← hwr]
      have hw : sint.Z (W64 ((mvcc.writeRev ilog pend : Nat) : Int) : w64) = mvcc.writeRev ilog pend := by
        unfold sint.Z W64
        rw [BitVec.toInt_ofInt_eq_self (by decide)
          (by rw [show (64 - 1 : Nat) = 63 from rfl]; omega)
          (by rw [show (64 - 1 : Nat) = 63 from rfl]; omega)]
      rw [hw]; constructor <;> omega
    -- `keys, _, _, _, _ := tw.s.kvindex.Range(key, end, rrev, 0, false)` by the writer
    ihave Hkn : mvcc.idxKnows γ.idx (.writer ilog pend) $$ [Hw]
    · rw [mvcc.idxKnows_writer]; iexact Hw
    wp_apply (hRange ti γ.idx (.writer ilog pend) key endk k e (W64 (ilog.length : Int)) (W64 0) false e0)
      $$ [$HtiS $Hti $Hkn $Hkey $Hend $Herr]
      as %keys %modifies %creates %vers %total
        ⟨Hti, Hw, Hkeys, Hmod, Hmodcap, Hcre, Hcrecap, Hvers, Hverscap, %Htotal⟩
    · ipureintro; rw [mvcc.IdxKnow.log_writer]; exact hrr
    rw [mvcc.idxKnows_writer, mvcc.IdxKnow.log_writer, hks']
    (try wp_auto)
    iunfold mvcc.ownKeys at Hkeys
    icases Hkeys with ⟨%kss, Hkss, Hkscap, %Hklen, #Hkz⟩
    ihave %Hkl := ownSlice_len keys (DFrac.own 1) kss $$ Hkss
    have hkeyslen : keys.len = W64 (ks.length : Int) := by
      rw [← Hklen, Hkl.1]; exact (mvcc.W64_sint_nat keys.len Hkl.2).symm
    have hkslt : ks.length < 2 ^ 63 := by omega
    have hksZ : sint.Z keys.len = ks.length := by
      rw [hkeyslen]; unfold sint.Z W64
      rw [BitVec.toInt_ofInt_eq_self (by decide)
        (by rw [show (64 - 1 : Nat) = 63 from rfl]; omega)
        (by rw [show (64 - 1 : Nat) = 63 from rfl]; omega)]
    -- `if len(keys) == 0 { return 0 }`
    wp_if_destruct
    · -- no key
      have hnil : ks = [] := by
        apply List.length_eq_zero_iff.1
        have h := congrArg sint.Z Hif
        rw [hksZ] at h
        simpa using h
      have h0 : (W64 (ks.length : Int) : w64) = W64 0 := by rw [hnil]; rfl
      rw [h0, hnil, List.map_nil, List.append_nil]
      (try wp_auto)
      iapply HΦ
      iunfold mvcc.storeTxnWriteIs
      iexists trace, ti, bt, Locked, chs, ps, ntok
      simp only [named]
      iframe Htoks Htok Htw Hchs Hcap Hkvs Hlocked Hw Hclog Hcur Hbv Hmu HrevMu Hti
      iframe #
      ipureintro; exact ⟨Hbudget, Hps, Hne⟩
    · -- the loop: `for _, key := range keys { tw.delete(key) }`
      have hpres := mvcc.delKeys_present ilog pend (decide (endk = slice.nil)) k e hwfL hlenL hcsL Hne
      have hnodup := mvcc.delKeys_nodup ilog pend (decide (endk = slice.nil)) k e
      rw [hks] at hpres hnodup
      ihave Htx : mvcc.storeTxnWriteIs tw s γ ilog pend
          $$ [Htoks Htok Htw Hchs Hcap Hkvs Hlocked Hw Hclog Hcur Hbv Hmu HrevMu Hti]
      · iunfold mvcc.storeTxnWriteIs
        iexists trace, ti, bt, Locked, chs, ps, ntok
        simp only [named]
        iframe Htoks Htok Htw Hchs Hcap Hkvs Hlocked Hw Hclog Hcur Hbv Hmu HrevMu Hti
        iframe #
        ipureintro; exact ⟨Hbudget, Hps, Hne⟩
      (try wp_auto)
      ihave IH : (∃ (j : Nat) (kv0 : GoSlice),
          "Hri" ∷ i_ptr ↦ (W64 (j : Int) : w64) ∗
          "Hk" ∷ key_ptr ↦ kv0 ∗
          "%Hj" ∷ ⌜j ≤ ks.length⌝ ∗
          "Htx" ∷ mvcc.storeTxnWriteIs tw s γ ilog (pend ++ (ks.take j).map .del)) $$ [i key Htx]
      · iexists 0, zero_val GoSlice
        simp only [named, List.take_zero, List.map_nil, List.append_nil]
        rw [show (W64 ((0 : Nat) : Int) : w64) = W64 0 from rfl]
        iframe i key Htx
        ipureintro; omega
      wp_for IH
      have hj : sint.Z (W64 (j : Int) : w64) = j := by
        unfold sint.Z W64
        rw [BitVec.toInt_ofInt_eq_self (by decide)
          (by rw [show (64 - 1 : Nat) = 63 from rfl]; omega)
          (by rw [show (64 - 1 : Nat) = 63 from rfl]; omega)]
      have hjN : (sint.Z (W64 (j : Int) : w64)).toNat = j := by rw [hj]; rfl
      wp_if_destruct
      · -- `i < len(keys)`: `tw.delete(keys[i])`
        have hlt : sint.Z (W64 (j : Int) : w64) < sint.Z keys.len := by
          first | exact Hif | (have := go.intoVal_inj Hif; simpa using this)
        have hjlt : j < ks.length := by rw [hj, hksZ] at hlt; omega
        obtain ⟨kw, hkw⟩ : ∃ kw, kss[j]? = some kw := ⟨_, List.getElem?_eq_getElem (by omega)⟩
        obtain ⟨kj, hkj⟩ : ∃ kj, ks[j]? = some kj := ⟨_, List.getElem?_eq_getElem hjlt⟩
        have Hbnd : 0 ≤ sint.Z (W64 (j : Int) : w64) ∧ sint.Z (W64 (j : Int) : w64) < sint.Z keys.len := by
          rw [hj]; constructor <;> omega
        simp only [Hbnd, _root_.and_self, ite_true]
        wp_apply wp_load_slice_index keys (sint.Z (W64 (j : Int) : w64)) kss (DFrac.own 1) kw Hbnd.1
          $$ [$Hkss] as Hkss
        · ipureintro; rw [hjN]; exact hkw
        have hz : (kw, kj) ∈ kss.zip ks :=
          List.mem_iff_getElem?.2 ⟨j, List.getElem?_zip_eq_some.2 ⟨hkw, hkj⟩⟩
        icases BigSepL.bigSepL_mem_acc hz $$ Hkz with ⟨#Hkj, -⟩
        (try wp_auto)
        have hmem : kj ∈ ks := List.mem_of_getElem? hkj
        have hnot : kj ∉ ks.take j := by
          intro hin
          obtain ⟨j', hj', hget⟩ := List.mem_iff_getElem.1 hin
          rw [List.getElem_take] at hget
          rw [List.length_take] at hj'
          have h1 : ks[j']? = ks[j]? := by
            rw [List.getElem?_eq_getElem (by omega), hget, hkj]
          have := (List.Nodup.getElem?_inj (by omega) hnodup).1 h1
          omega
        wp_apply (hDel tw s γ ilog (pend ++ (ks.take j).map .del) kw kj) $$ [$Htx $Hkj] as Htx
        · ipureintro
          refine ⟨?_, by simp only [List.length_append, List.length_map, List.length_take]; omega⟩
          rw [show mvcc.applyChanges (W64 (ilog.length : Int)) (mvcc.stateAfter ilog)
              (pend ++ (ks.take j).map .del) =
            mvcc.applyChanges (W64 (ilog.length : Int))
              (mvcc.applyChanges (W64 (ilog.length : Int)) (mvcc.stateAfter ilog) pend)
              ((ks.take j).map .del) by unfold mvcc.applyChanges; rw [List.foldl_append]]
          rw [mvcc.findKey_applyChanges_dels _ _ _ _ hnot]
          exact hpres kj hmem
        (try wp_auto)
        wp_for_post
        (try wp_auto)
        (try simp only [named])
        iframe HΦ tw Hmod Hmodcap Hcre Hcrecap Hvers Hverscap keys Hkss Hkscap
        iexists (j + 1), kw
        (try simp only [named])
        rw [List.take_succ, hkj, Option.toList_some, List.map_append, List.map_singleton,
          ← List.append_assoc]
        rw [show (W64 ((j + 1 : Nat) : Int) : w64) = W64 (j : Int) + W64 1 by
          rw [← mvcc.W64_add_one]; simp]
        iframe Hri Hk Htx
        ipureintro; omega
      · -- the loop is done: every key deleted
        have hge : ¬ sint.Z (W64 (j : Int) : w64) < sint.Z keys.len := by
          first | exact Hif | exact fun h => Hif (by rw [decide_eq_true h])
        have hjeq : j = ks.length := by rw [hj, hksZ] at hge; omega
        subst hjeq
        rw [List.take_length]
        (try rw [decide_eq_false hge, if_pos (by simp)])
        (try wp_auto)
        rw [hkeyslen]
        iapply HΦ
        iexact Htx
  · -- no change yet: the committed log's last revision
    have hpend : pend = [] := by
      rw [hcl] at Hif
      apply List.length_eq_zero_iff.1
      have hpz : sint.Z (W64 (pend.length : Int) : w64) = pend.length := by
        unfold sint.Z W64
        rw [BitVec.toInt_ofInt_eq_self (by decide)
          (by rw [show (64 - 1 : Nat) = 63 from rfl]; omega)
          (by rw [show (64 - 1 : Nat) = 63 from rfl]; omega)]
      have h0 : sint.Z (W64 0 : w64) = 0 := by decide
      first
        | (rw [hpz, h0] at Hif; omega)
        | (have h := congrArg sint.Z Hif; rw [hpz, h0] at h; omega)
    (try wp_auto)
    have hwr : (W64 ((mvcc.writeRev ilog pend : Nat) : Int) : w64) = W64 ((ilog.length : Int) - 1) := by
      unfold mvcc.writeRev; rw [if_pos hpend]; congr 1; omega
    have hks' : (mvcc.rangeTaken (ilog ++ [pend]) (decide (endk = slice.nil)) k e (W64 ((ilog.length : Int) - 1)) (W64 0)).map
        Prod.fst = ks := by
      rw [← hwr]; exact hks
    have hrr : 0 ≤ sint.Z ((W64 ((ilog.length : Int) - 1)) : w64) ∧ sint.Z ((W64 ((ilog.length : Int) - 1)) : w64) < ((ilog ++ [pend]).length : Int) := by
      have := mvcc.writeRev_lt ilog pend Hne
      rw [← hwr]
      have hw : sint.Z (W64 ((mvcc.writeRev ilog pend : Nat) : Int) : w64) = mvcc.writeRev ilog pend := by
        unfold sint.Z W64
        rw [BitVec.toInt_ofInt_eq_self (by decide)
          (by rw [show (64 - 1 : Nat) = 63 from rfl]; omega)
          (by rw [show (64 - 1 : Nat) = 63 from rfl]; omega)]
      rw [hw]; constructor <;> omega
    -- `keys, _, _, _, _ := tw.s.kvindex.Range(key, end, rrev, 0, false)` by the writer
    ihave Hkn : mvcc.idxKnows γ.idx (.writer ilog pend) $$ [Hw]
    · rw [mvcc.idxKnows_writer]; iexact Hw
    wp_apply (hRange ti γ.idx (.writer ilog pend) key endk k e (W64 ((ilog.length : Int) - 1)) (W64 0) false e0)
      $$ [$HtiS $Hti $Hkn $Hkey $Hend $Herr]
      as %keys %modifies %creates %vers %total
        ⟨Hti, Hw, Hkeys, Hmod, Hmodcap, Hcre, Hcrecap, Hvers, Hverscap, %Htotal⟩
    · ipureintro; rw [mvcc.IdxKnow.log_writer]; exact hrr
    rw [mvcc.idxKnows_writer, mvcc.IdxKnow.log_writer, hks']
    (try wp_auto)
    iunfold mvcc.ownKeys at Hkeys
    icases Hkeys with ⟨%kss, Hkss, Hkscap, %Hklen, #Hkz⟩
    ihave %Hkl := ownSlice_len keys (DFrac.own 1) kss $$ Hkss
    have hkeyslen : keys.len = W64 (ks.length : Int) := by
      rw [← Hklen, Hkl.1]; exact (mvcc.W64_sint_nat keys.len Hkl.2).symm
    have hkslt : ks.length < 2 ^ 63 := by omega
    have hksZ : sint.Z keys.len = ks.length := by
      rw [hkeyslen]; unfold sint.Z W64
      rw [BitVec.toInt_ofInt_eq_self (by decide)
        (by rw [show (64 - 1 : Nat) = 63 from rfl]; omega)
        (by rw [show (64 - 1 : Nat) = 63 from rfl]; omega)]
    -- `if len(keys) == 0 { return 0 }`
    wp_if_destruct
    · -- no key
      have hnil : ks = [] := by
        apply List.length_eq_zero_iff.1
        have h := congrArg sint.Z Hif
        rw [hksZ] at h
        simpa using h
      have h0 : (W64 (ks.length : Int) : w64) = W64 0 := by rw [hnil]; rfl
      rw [h0, hnil, List.map_nil, List.append_nil]
      (try wp_auto)
      iapply HΦ
      iunfold mvcc.storeTxnWriteIs
      iexists trace, ti, bt, Locked, chs, ps, ntok
      simp only [named]
      iframe Htoks Htok Htw Hchs Hcap Hkvs Hlocked Hw Hclog Hcur Hbv Hmu HrevMu Hti
      iframe #
      ipureintro; exact ⟨Hbudget, Hps, Hne⟩
    · -- the loop: `for _, key := range keys { tw.delete(key) }`
      have hpres := mvcc.delKeys_present ilog pend (decide (endk = slice.nil)) k e hwfL hlenL hcsL Hne
      have hnodup := mvcc.delKeys_nodup ilog pend (decide (endk = slice.nil)) k e
      rw [hks] at hpres hnodup
      ihave Htx : mvcc.storeTxnWriteIs tw s γ ilog pend
          $$ [Htoks Htok Htw Hchs Hcap Hkvs Hlocked Hw Hclog Hcur Hbv Hmu HrevMu Hti]
      · iunfold mvcc.storeTxnWriteIs
        iexists trace, ti, bt, Locked, chs, ps, ntok
        simp only [named]
        iframe Htoks Htok Htw Hchs Hcap Hkvs Hlocked Hw Hclog Hcur Hbv Hmu HrevMu Hti
        iframe #
        ipureintro; exact ⟨Hbudget, Hps, Hne⟩
      (try wp_auto)
      ihave IH : (∃ (j : Nat) (kv0 : GoSlice),
          "Hri" ∷ i_ptr ↦ (W64 (j : Int) : w64) ∗
          "Hk" ∷ key_ptr ↦ kv0 ∗
          "%Hj" ∷ ⌜j ≤ ks.length⌝ ∗
          "Htx" ∷ mvcc.storeTxnWriteIs tw s γ ilog (pend ++ (ks.take j).map .del)) $$ [i key Htx]
      · iexists 0, zero_val GoSlice
        simp only [named, List.take_zero, List.map_nil, List.append_nil]
        rw [show (W64 ((0 : Nat) : Int) : w64) = W64 0 from rfl]
        iframe i key Htx
        ipureintro; omega
      wp_for IH
      have hj : sint.Z (W64 (j : Int) : w64) = j := by
        unfold sint.Z W64
        rw [BitVec.toInt_ofInt_eq_self (by decide)
          (by rw [show (64 - 1 : Nat) = 63 from rfl]; omega)
          (by rw [show (64 - 1 : Nat) = 63 from rfl]; omega)]
      have hjN : (sint.Z (W64 (j : Int) : w64)).toNat = j := by rw [hj]; rfl
      wp_if_destruct
      · -- `i < len(keys)`: `tw.delete(keys[i])`
        have hlt : sint.Z (W64 (j : Int) : w64) < sint.Z keys.len := by
          first | exact Hif | (have := go.intoVal_inj Hif; simpa using this)
        have hjlt : j < ks.length := by rw [hj, hksZ] at hlt; omega
        obtain ⟨kw, hkw⟩ : ∃ kw, kss[j]? = some kw := ⟨_, List.getElem?_eq_getElem (by omega)⟩
        obtain ⟨kj, hkj⟩ : ∃ kj, ks[j]? = some kj := ⟨_, List.getElem?_eq_getElem hjlt⟩
        have Hbnd : 0 ≤ sint.Z (W64 (j : Int) : w64) ∧ sint.Z (W64 (j : Int) : w64) < sint.Z keys.len := by
          rw [hj]; constructor <;> omega
        simp only [Hbnd, _root_.and_self, ite_true]
        wp_apply wp_load_slice_index keys (sint.Z (W64 (j : Int) : w64)) kss (DFrac.own 1) kw Hbnd.1
          $$ [$Hkss] as Hkss
        · ipureintro; rw [hjN]; exact hkw
        have hz : (kw, kj) ∈ kss.zip ks :=
          List.mem_iff_getElem?.2 ⟨j, List.getElem?_zip_eq_some.2 ⟨hkw, hkj⟩⟩
        icases BigSepL.bigSepL_mem_acc hz $$ Hkz with ⟨#Hkj, -⟩
        (try wp_auto)
        have hmem : kj ∈ ks := List.mem_of_getElem? hkj
        have hnot : kj ∉ ks.take j := by
          intro hin
          obtain ⟨j', hj', hget⟩ := List.mem_iff_getElem.1 hin
          rw [List.getElem_take] at hget
          rw [List.length_take] at hj'
          have h1 : ks[j']? = ks[j]? := by
            rw [List.getElem?_eq_getElem (by omega), hget, hkj]
          have := (List.Nodup.getElem?_inj (by omega) hnodup).1 h1
          omega
        wp_apply (hDel tw s γ ilog (pend ++ (ks.take j).map .del) kw kj) $$ [$Htx $Hkj] as Htx
        · ipureintro
          refine ⟨?_, by simp only [List.length_append, List.length_map, List.length_take]; omega⟩
          rw [show mvcc.applyChanges (W64 (ilog.length : Int)) (mvcc.stateAfter ilog)
              (pend ++ (ks.take j).map .del) =
            mvcc.applyChanges (W64 (ilog.length : Int))
              (mvcc.applyChanges (W64 (ilog.length : Int)) (mvcc.stateAfter ilog) pend)
              ((ks.take j).map .del) by unfold mvcc.applyChanges; rw [List.foldl_append]]
          rw [mvcc.findKey_applyChanges_dels _ _ _ _ hnot]
          exact hpres kj hmem
        (try wp_auto)
        wp_for_post
        (try wp_auto)
        (try simp only [named])
        iframe HΦ tw Hmod Hmodcap Hcre Hcrecap Hvers Hverscap keys Hkss Hkscap
        iexists (j + 1), kw
        (try simp only [named])
        rw [List.take_succ, hkj, Option.toList_some, List.map_append, List.map_singleton,
          ← List.append_assoc]
        rw [show (W64 ((j + 1 : Nat) : Int) : w64) = W64 (j : Int) + W64 1 by
          rw [← mvcc.W64_add_one]; simp]
        iframe Hri Hk Htx
        ipureintro; omega
      · -- the loop is done: every key deleted
        have hge : ¬ sint.Z (W64 (j : Int) : w64) < sint.Z keys.len := by
          first | exact Hif | exact fun h => Hif (by rw [decide_eq_true h])
        have hjeq : j = ks.length := by rw [hj, hksZ] at hge; omega
        subst hjeq
        rw [List.take_length]
        (try rw [decide_eq_false hge, if_pos (by simp)])
        (try wp_auto)
        rw [hkeyslen]
        iapply HΦ
        iexact Htx

end proof

end EtcdGrove
end Perennial
