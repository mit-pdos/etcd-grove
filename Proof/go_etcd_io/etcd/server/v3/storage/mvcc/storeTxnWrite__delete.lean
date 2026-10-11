/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.storeTxnWrite__delete
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.NewRevBytes
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.newBucketKey
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.BucketKeyToBytes
public import Spec.google_golang_org.protobuf.proto.Marshal
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.treeIndex__Tombstone
public import Spec.go_uber_org.zap.Error
public import Spec.go_uber_org.zap.Logger__Error

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

theorem mvcc.storeTxnWrite.delete.wp_proof
    (hNewRev : mvcc.NewRevBytes.spec (GF := GF) (hG := hG))
    (hNewBK : mvcc.newBucketKey.spec (GF := GF) (hG := hG))
    (hBKTo : mvcc.BucketKeyToBytes.spec (GF := GF) (hG := hG))
    (hMarshal : proto.Marshal.spec (GF := GF) (hG := hG))
    (hTomb : mvcc.treeIndex.Tombstone.spec (GF := GF) (hG := hG))
    (hZapErr : zap.Error.spec (GF := GF) (hG := hG))
    (hLogErr : zap.Logger.Error.spec (GF := GF) (hG := hG)) :
    mvcc.storeTxnWrite.delete.spec (GF := GF) (hG := hG) := by
  intro tw s γ ilog pend key k
  wp_start as ⟨Htw, #Hkey, %Hpre⟩
  obtain ⟨Hpresent, Hb⟩ := Hpre
  simp only [go_etcd_io.etcd.server.v3.lease.NoLease]
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
  have hkvm' : mvcc.changeKv (W64 (ilog.length : Int)) (mvcc.stateAfter ilog) (pend ++ [.del k])
      pend.length = some (zeroKv k) := by
    unfold mvcc.changeKv
    rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  ihave #Hnil : (slice.nil ↦*□ ([] : GoString) : IProp GF) $$ []
  · iapply (ownSlice_nil DFrac.discard)
  (try wp_auto)
  -- `ibytes := NewRevBytes()`
  wp_apply hNewRev as %ib ⟨Hib, Hibcap, -⟩
  (try wp_auto)
  -- `idxRev := newBucketKey(tw.beginRev+1, int64(len(tw.changes)), true)`
  wp_apply (hNewBK _ _ true)
  (try wp_auto)
  (try rw [hrev])
  (try rw [hcl])
  trace_state
  -- `ibytes = BucketKeyToBytes(idxRev, ibytes)`
  wp_apply (hBKTo _ ib _ (Or.inl (by simp))) $$ [$Hib $Hibcap] as %ib' ⟨Hib, Hibcap⟩
  (try wp_auto)
  rw [mvcc.bucketKeyBytes_true]
  trace_state
  -- `kv := &mvccpb.KeyValue{Key: key}`; `d, err := proto.Marshal(kv)`
  wp_apply (hMarshal «$r0_ptr» _ (zeroKv k) DFrac.discard DFrac.discard) $$ [$«$r0» $Hkey $Hnil]
    as %d ⟨⟨%sc, Hkv⟩, -, -, Hd, Hdcap⟩
  · ipureintro; exact ⟨rfl, rfl, rfl, rfl⟩
  (try wp_auto)
  -- `if err != nil { Fatal }`: not taken
  wp_if_destruct
  rotate_left
  · exfalso; exact Hif rfl
  (try wp_auto)
  -- `tw.tx.UnsafeSeqPut(schema.Key, ibytes, d)`
  wp_apply (HSeqPut (mvcc.pendPuts ilog pend) bK ib' d _ _ (DFrac.own 1) (DFrac.own 1))
    $$ [$HKeyG $Hlocked $Hib $Hd] as ⟨Hlocked, Hib, Hd⟩
  (try wp_auto)
  -- `err = tw.s.kvindex.Tombstone(key, idxRev.Revision)`
  wp_apply (hTomb ti γ.idx ilog pend key k _) $$ [$HtiS $Hw $Hkey] as Hw
  · ipureintro
    refine ⟨rfl, hpos, Hb, mvcc.LogWf'.append_change Hwf' Hne _ (fun k' h => ?_)⟩
    rw [← mvcc.Change.del.inj h]; exact Hpresent
  (try wp_auto)
  -- `if err != nil { Fatal }`: not taken
  wp_if_destruct
  rotate_left
  · exfalso; exact Hif rfl
  (try wp_auto)
  -- `tw.changes = append(tw.changes, kv)`
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %lit ⟨Hlit, -⟩
  wp_apply (wp_slice_append chs ps lit [«$r0_ptr»] (DFrac.own 1)) $$ [$Hchs $Hcap $Hlit]
    as %chs' ⟨Hchs, Hcap, -⟩
  (try wp_auto)
  -- the transaction with the delete, for every lease outcome
  ihave Htw' : mvcc.storeTxnWriteIs tw s γ ilog (pend ++ [.del k])
      $$ [Htoks Htok Htw Hchs Hcap Hkvs Hlocked Hw Hclog Hcur Hmu HrevMu Hti Hkv]
  · iunfold mvcc.storeTxnWriteIs
    iexists trace, ti, bt, Locked, chs', (ps ++ [«$r0_ptr»]), ntok
    simp only [named]
    rw [mvcc.pendPuts_append ilog pend (.del k) _ hkvm']
    iframe Htoks Htok Htw Hchs Hcap Hlocked Hw Hclog Hcur Hmu HrevMu Hti
    iframe #
    isplitl []
    · ipureintro; exact Hbudget
    isplitl []
    · ipureintro; simp [Hps]
    isplitl [Hkvs Hkv]
    · iunfold mvcc.changesAre
      iapply BigSepL.bigSepL_snoc.2
      isplitl [Hkvs]
      · iapply (BigSepL.bigSepL_mono ?_) $$ Hkvs
        intro i p hi
        rw [mvcc.changeKv_append_lt _ _ _ _ (by have := (List.getElem?_eq_some_iff.1 hi).1; omega)]
        exact BIBase.Entails.refl _
      · rw [Hps]
        iexists _
        isplitl []
        · ipureintro; exact hkvm'
        iunfold mvcc.kvPtrIs
        iexists key, _, _, sc
        iframe Hkey
        simp only [↓reduceIte]
        iexists slice.nil
        isplitl []
        · iexact Hnil
        iexact Hkv
    ipureintro; exact Hne
  -- `item := lease.LeaseItem{Key: string(key)}`; `leaseID := tw.s.le.GetLease(item)`
  wp_apply (wp_bytes_to_string key k DFrac.discard) $$ [$Hkey] as -
  (try wp_auto)
  wp_apply HGetL as %lid -
  (try wp_auto)
  -- `if leaseID != lease.NoLease { Detach }`: the first goal is `leaseID == NoLease`
  wp_if_destruct
  · (try wp_auto)
    iapply HΦ; iexact Htw'
  · (try wp_auto)
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %items ⟨Hitems, -⟩
    wp_apply (HDetach _ items _ (DFrac.own 1)) $$ [$Hitems] as %err -
    (try wp_auto)
    -- `if err != nil { Error }`: the first goal is `err == nil`
    wp_if_destruct
    · (try wp_auto)
      iapply HΦ; iexact Htw'
    · (try wp_auto)
      wp_apply (hZapErr err) as %f -
      (try wp_auto)
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %fl ⟨Hfl, -⟩
      wp_apply (hLogErr lg _ fl)
      · ipureintro; exact HlgnnS
      (try wp_auto)
      iapply HΦ; iexact Htw'

end proof

end EtcdGrove
end Perennial
