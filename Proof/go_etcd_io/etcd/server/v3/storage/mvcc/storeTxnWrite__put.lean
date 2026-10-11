/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.storeTxnWrite__put
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.treeIndex__Get
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Trace__Step
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.NewRevBytes
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.RevToBytes
public import Spec.google_golang_org.protobuf.proto.Marshal
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.treeIndex__Put
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

theorem mvcc.storeTxnWrite.put.wp_proof
    (hGet : mvcc.treeIndex.Get.spec (GF := GF) (hG := hG))
    (hStep : traceutil.Trace.Step.spec (GF := GF) (hG := hG))
    (hNewRev : mvcc.NewRevBytes.spec (GF := GF) (hG := hG))
    (hRevTo : mvcc.RevToBytes.spec (GF := GF) (hG := hG))
    (hMarshal : proto.Marshal.spec (GF := GF) (hG := hG))
    (hPutI : mvcc.treeIndex.Put.spec (GF := GF) (hG := hG))
    (hZapErr : zap.Error.spec (GF := GF) (hG := hG))
    (hLogErr : zap.Logger.Error.spec (GF := GF) (hG := hG)) :
    mvcc.storeTxnWrite.put.spec (GF := GF) (hG := hG) := by
  intro tw s γ ilog pend key value k v leaseID
  wp_start as ⟨Htw, #Hkey, #Hval, Hlease, %Hb⟩
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
  have hkvm := mvcc.changeKv_put ilog pend k v leaseID hwfL hlenL hcsL
  (try wp_auto)
  (try rw [hrev])
  -- `tw.s.kvindex.Get(key, rev)` by the writer
  ihave Hkn : mvcc.idxKnows γ.idx (.writer ilog pend) $$ [Hw]
  · rw [mvcc.idxKnows_writer]; iexact Hw
  trace_state
  wp_apply (hGet ti γ.idx (.writer ilog pend) key k (W64 (ilog.length : Int)) e0)
    $$ [$HtiS $Hti $Hkn $Hkey $Herr] as ⟨Hti, Hw, -⟩
  · ipureintro; rw [mvcc.IdxKnow.log_writer]; constructor <;> word
  rw [mvcc.idxKnows_writer, mvcc.IdxKnow.log_writer]
  cases hg : mvcc.kiGet (mvcc.kiOfKey (mvcc.evsOf (ilog ++ [pend])) k) (W64 (ilog.length : Int)) with
  | some a =>
    obtain ⟨m, c, ver⟩ := a
    simp only [mvcc.kiGetVal, hg]
    (try wp_auto)
    -- `err == nil`: the key exists
    wp_if_destruct
    · (try wp_auto)
      trace_state
      -- `oldLease = tw.s.le.GetLease(lease.LeaseItem{Key: string(key)})`
      wp_apply (wp_bytes_to_string key k DFrac.discard) $$ [$Hkey] as -
      (try wp_auto)
      wp_apply HGetL as %oldL -
      (try wp_auto)
      wp_apply (hStep trace _ _)
      (try wp_auto)
      have hkvm' : mvcc.changeKv (W64 (ilog.length : Int)) (mvcc.stateAfter ilog)
          (pend ++ [.put k v leaseID]) pend.length = some {
            key := k, createRev := (mvcc.revVal c).Main', modRev := W64 (ilog.length : Int),
            version := ver + W64 1, value := v, lease := leaseID } := by
        rw [hkvm, hg]; rfl
      -- `ibytes := NewRevBytes()`; `idxRev := Revision{Main: rev, Sub: int64(len(tw.changes))}`
      wp_apply hNewRev as %ib ⟨Hib, Hibcap, -⟩
      (try wp_auto)
      trace_state
      -- `ibytes = RevToBytes(idxRev, ibytes)`
      wp_apply (hRevTo _ ib _ (Or.inl (by simp))) $$ [$Hib $Hibcap] as %ib' ⟨Hib, Hibcap⟩
      (try wp_auto)
      rw [List.drop_of_length_le (by simp), List.append_nil, hcl] at Hib
      -- `kv := &mvccpb.KeyValue{...}`
      wp_alloc kvp as Hkv
      (try wp_auto)
      -- `d, err := proto.Marshal(kv)`
      wp_apply (hMarshal kvp _ _ DFrac.discard DFrac.discard) $$ [$Hkv $Hkey $Hval]
        as %d ⟨⟨%sc, Hkv⟩, -, -, Hd, Hdcap⟩
      · ipureintro; exact ⟨rfl, rfl, rfl, rfl⟩
      (try wp_auto)
      -- `if err != nil { Fatal }`: not taken
      wp_if_destruct
      rotate_left
      · exfalso; exact Hif rfl
      (try wp_auto)
      wp_apply (hStep trace _ _)
      (try wp_auto)
      -- `tw.tx.UnsafeSeqPut(schema.Key, ibytes, d)`
      wp_apply (HSeqPut (mvcc.pendPuts ilog pend) bK ib' d _ _ (DFrac.own 1) (DFrac.own 1))
        $$ [$HKeyG $Hlocked $Hib $Hd] as ⟨Hlocked, Hib, Hd⟩
      (try wp_auto)
      -- `tw.s.kvindex.Put(key, idxRev)`
      wp_apply (hPutI ti γ.idx ilog pend key k _ v leaseID) $$ [$HtiS $Hw $Hkey] as Hw
      · ipureintro
        refine ⟨rfl, hpos, Hb, mvcc.LogWf'.append_change Hwf' Hne _ (fun _ h => by cases h)⟩
      (try wp_auto)
      -- `tw.changes = append(tw.changes, kv)`
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %lit ⟨Hlit, -⟩
      wp_apply (wp_slice_append chs ps lit [kvp] (DFrac.own 1)) $$ [$Hchs $Hcap $Hlit]
        as %chs' ⟨Hchs, Hcap, -⟩
      (try wp_auto)
      wp_apply (hStep trace _ _)
      (try wp_auto)
      -- the transaction with the put, for every lease outcome
      ihave Htw' : mvcc.storeTxnWriteIs tw s γ ilog (pend ++ [.put k v leaseID])
          $$ [Htoks Htok Htw Hchs Hcap Hkvs Hlocked Hw Hclog Hcur Hmu HrevMu Hti Hkv]
      · iunfold mvcc.storeTxnWriteIs
        iexists trace, ti, bt, Locked, chs', (ps ++ [kvp]), ntok
        simp only [named]
        rw [mvcc.pendPuts_append ilog pend (.put k v leaseID) _ hkvm']
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
            iexists value
            iframe Hval
            iexact Hkv
        ipureintro; exact Hne
      -- `if oldLease == leaseID { trace.Step; return }`
      wp_if_destruct
      · (try wp_auto)
        wp_apply (hStep trace _ _)
        (try wp_auto)
        iapply HΦ; iexact Htw'
      (try wp_auto)
      -- `if oldLease != lease.NoLease { Detach }`: the first goal is `oldLease == NoLease`
      wp_if_destruct
      · (try wp_auto)
        -- `if leaseID != lease.NoLease { Attach }`: the first goal is `leaseID == NoLease`
        wp_if_destruct
        · (try wp_auto)
          wp_apply (hStep trace _ _)
          (try wp_auto)
          iapply HΦ; iexact Htw'
        · (try wp_auto)
          wp_if_destruct
          · exfalso; exact Hif rfl
          (try wp_auto)
          icases Hlease with (%h0 | #Hknown)
          · exfalso; subst h0; exact Hif rfl
          wp_apply (wp_bytes_to_string key k DFrac.discard) $$ [$Hkey] as -
          (try wp_auto)
          wp_apply wp_slice_literal
          isplitr
          · ipureintro; rfl
          iintro %items ⟨Hitems, -⟩
          wp_apply (HAttach leaseID items _ (DFrac.own 1)) $$ [$Hknown $Hitems] as -
          (try wp_auto)
          wp_if_destruct
          rotate_left
          · exfalso; exact Hif rfl
          (try wp_auto)
          wp_apply (hStep trace _ _)
          (try wp_auto)
          iapply HΦ; iexact Htw'
      · (try wp_auto)
        wp_if_destruct
        · exfalso; exact Hif rfl
        (try wp_auto)
        wp_apply (wp_bytes_to_string key k DFrac.discard) $$ [$Hkey] as -
        (try wp_auto)
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %items ⟨Hitems, -⟩
        wp_apply (HDetach _ items _ (DFrac.own 1)) $$ [$Hitems] as %err -
        (try wp_auto)
        -- `if err != nil { Error }`: the first goal is `err == nil`
        wp_if_destruct
        · (try wp_auto)
          -- `if leaseID != lease.NoLease { Attach }`: the first goal is `leaseID == NoLease`
          wp_if_destruct
          · (try wp_auto)
            wp_apply (hStep trace _ _)
            (try wp_auto)
            iapply HΦ; iexact Htw'
          · (try wp_auto)
            wp_if_destruct
            · exfalso; exact Hif rfl
            (try wp_auto)
            icases Hlease with (%h0 | #Hknown)
            · exfalso; subst h0; exact Hif rfl
            wp_apply (wp_bytes_to_string key k DFrac.discard) $$ [$Hkey] as -
            (try wp_auto)
            wp_apply wp_slice_literal
            isplitr
            · ipureintro; rfl
            iintro %items ⟨Hitems, -⟩
            wp_apply (HAttach leaseID items _ (DFrac.own 1)) $$ [$Hknown $Hitems] as -
            (try wp_auto)
            wp_if_destruct
            rotate_left
            · exfalso; exact Hif rfl
            (try wp_auto)
            wp_apply (hStep trace _ _)
            (try wp_auto)
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
          -- `if leaseID != lease.NoLease { Attach }`: the first goal is `leaseID == NoLease`
          wp_if_destruct
          · (try wp_auto)
            wp_apply (hStep trace _ _)
            (try wp_auto)
            iapply HΦ; iexact Htw'
          · (try wp_auto)
            wp_if_destruct
            · exfalso; exact Hif rfl
            (try wp_auto)
            icases Hlease with (%h0 | #Hknown)
            · exfalso; subst h0; exact Hif rfl
            wp_apply (wp_bytes_to_string key k DFrac.discard) $$ [$Hkey] as -
            (try wp_auto)
            wp_apply wp_slice_literal
            isplitr
            · ipureintro; rfl
            iintro %items ⟨Hitems, -⟩
            wp_apply (HAttach leaseID items _ (DFrac.own 1)) $$ [$Hknown $Hitems] as -
            (try wp_auto)
            wp_if_destruct
            rotate_left
            · exfalso; exact Hif rfl
            (try wp_auto)
            wp_apply (hStep trace _ _)
            (try wp_auto)
            iapply HΦ; iexact Htw'
    · exfalso; first | exact Hif rfl | simp at Hif
  | none =>
    simp only [mvcc.kiGetVal, hg]
    (try wp_auto)
    wp_if_destruct
    · exfalso; first | exact Hif rfl | simp at Hif
    · (try wp_auto)
      trace_state
      have hkvm' : mvcc.changeKv (W64 (ilog.length : Int)) (mvcc.stateAfter ilog)
          (pend ++ [.put k v leaseID]) pend.length = some {
            key := k, createRev := W64 (ilog.length : Int), modRev := W64 (ilog.length : Int),
            version := W64 0 + W64 1, value := v, lease := leaseID } := by
        rw [hkvm, hg]; rfl
      -- `ibytes := NewRevBytes()`; `idxRev := Revision{Main: rev, Sub: int64(len(tw.changes))}`
      wp_apply hNewRev as %ib ⟨Hib, Hibcap, -⟩
      (try wp_auto)
      trace_state
      -- `ibytes = RevToBytes(idxRev, ibytes)`
      wp_apply (hRevTo _ ib _ (Or.inl (by simp))) $$ [$Hib $Hibcap] as %ib' ⟨Hib, Hibcap⟩
      (try wp_auto)
      rw [List.drop_of_length_le (by simp), List.append_nil, hcl] at Hib
      -- `kv := &mvccpb.KeyValue{...}`
      wp_alloc kvp as Hkv
      (try wp_auto)
      -- `d, err := proto.Marshal(kv)`
      wp_apply (hMarshal kvp _ _ DFrac.discard DFrac.discard) $$ [$Hkv $Hkey $Hval]
        as %d ⟨⟨%sc, Hkv⟩, -, -, Hd, Hdcap⟩
      · ipureintro; exact ⟨rfl, rfl, rfl, rfl⟩
      (try wp_auto)
      -- `if err != nil { Fatal }`: not taken
      wp_if_destruct
      rotate_left
      · exfalso; exact Hif rfl
      (try wp_auto)
      wp_apply (hStep trace _ _)
      (try wp_auto)
      -- `tw.tx.UnsafeSeqPut(schema.Key, ibytes, d)`
      wp_apply (HSeqPut (mvcc.pendPuts ilog pend) bK ib' d _ _ (DFrac.own 1) (DFrac.own 1))
        $$ [$HKeyG $Hlocked $Hib $Hd] as ⟨Hlocked, Hib, Hd⟩
      (try wp_auto)
      -- `tw.s.kvindex.Put(key, idxRev)`
      wp_apply (hPutI ti γ.idx ilog pend key k _ v leaseID) $$ [$HtiS $Hw $Hkey] as Hw
      · ipureintro
        refine ⟨rfl, hpos, Hb, mvcc.LogWf'.append_change Hwf' Hne _ (fun _ h => by cases h)⟩
      (try wp_auto)
      -- `tw.changes = append(tw.changes, kv)`
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %lit ⟨Hlit, -⟩
      wp_apply (wp_slice_append chs ps lit [kvp] (DFrac.own 1)) $$ [$Hchs $Hcap $Hlit]
        as %chs' ⟨Hchs, Hcap, -⟩
      (try wp_auto)
      wp_apply (hStep trace _ _)
      (try wp_auto)
      -- the transaction with the put, for every lease outcome
      ihave Htw' : mvcc.storeTxnWriteIs tw s γ ilog (pend ++ [.put k v leaseID])
          $$ [Htoks Htok Htw Hchs Hcap Hkvs Hlocked Hw Hclog Hcur Hmu HrevMu Hti Hkv]
      · iunfold mvcc.storeTxnWriteIs
        iexists trace, ti, bt, Locked, chs', (ps ++ [kvp]), ntok
        simp only [named]
        rw [mvcc.pendPuts_append ilog pend (.put k v leaseID) _ hkvm']
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
            iexists value
            iframe Hval
            iexact Hkv
        ipureintro; exact Hne
      -- `if oldLease == leaseID { trace.Step; return }`
      wp_if_destruct
      · (try wp_auto)
        wp_apply (hStep trace _ _)
        (try wp_auto)
        iapply HΦ; iexact Htw'
      (try wp_auto)
      -- `if oldLease != lease.NoLease { Detach }`: the first goal is `oldLease == NoLease`
      wp_if_destruct
      · (try wp_auto)
        -- `if leaseID != lease.NoLease { Attach }`: the first goal is `leaseID == NoLease`
        wp_if_destruct
        · (try wp_auto)
          wp_apply (hStep trace _ _)
          (try wp_auto)
          iapply HΦ; iexact Htw'
        · (try wp_auto)
          wp_if_destruct
          · exfalso; exact Hif rfl
          (try wp_auto)
          icases Hlease with (%h0 | #Hknown)
          · exfalso; subst h0; exact Hif rfl
          wp_apply (wp_bytes_to_string key k DFrac.discard) $$ [$Hkey] as -
          (try wp_auto)
          wp_apply wp_slice_literal
          isplitr
          · ipureintro; rfl
          iintro %items ⟨Hitems, -⟩
          wp_apply (HAttach leaseID items _ (DFrac.own 1)) $$ [$Hknown $Hitems] as -
          (try wp_auto)
          wp_if_destruct
          rotate_left
          · exfalso; exact Hif rfl
          (try wp_auto)
          wp_apply (hStep trace _ _)
          (try wp_auto)
          iapply HΦ; iexact Htw'
      · (try wp_auto)
        wp_if_destruct
        · exfalso; exact Hif rfl
        (try wp_auto)
        wp_apply (wp_bytes_to_string key k DFrac.discard) $$ [$Hkey] as -
        (try wp_auto)
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %items ⟨Hitems, -⟩
        wp_apply (HDetach _ items _ (DFrac.own 1)) $$ [$Hitems] as %err -
        (try wp_auto)
        -- `if err != nil { Error }`: the first goal is `err == nil`
        wp_if_destruct
        · (try wp_auto)
          -- `if leaseID != lease.NoLease { Attach }`: the first goal is `leaseID == NoLease`
          wp_if_destruct
          · (try wp_auto)
            wp_apply (hStep trace _ _)
            (try wp_auto)
            iapply HΦ; iexact Htw'
          · (try wp_auto)
            wp_if_destruct
            · exfalso; exact Hif rfl
            (try wp_auto)
            icases Hlease with (%h0 | #Hknown)
            · exfalso; subst h0; exact Hif rfl
            wp_apply (wp_bytes_to_string key k DFrac.discard) $$ [$Hkey] as -
            (try wp_auto)
            wp_apply wp_slice_literal
            isplitr
            · ipureintro; rfl
            iintro %items ⟨Hitems, -⟩
            wp_apply (HAttach leaseID items _ (DFrac.own 1)) $$ [$Hknown $Hitems] as -
            (try wp_auto)
            wp_if_destruct
            rotate_left
            · exfalso; exact Hif rfl
            (try wp_auto)
            wp_apply (hStep trace _ _)
            (try wp_auto)
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
          -- `if leaseID != lease.NoLease { Attach }`: the first goal is `leaseID == NoLease`
          wp_if_destruct
          · (try wp_auto)
            wp_apply (hStep trace _ _)
            (try wp_auto)
            iapply HΦ; iexact Htw'
          · (try wp_auto)
            wp_if_destruct
            · exfalso; exact Hif rfl
            (try wp_auto)
            icases Hlease with (%h0 | #Hknown)
            · exfalso; subst h0; exact Hif rfl
            wp_apply (wp_bytes_to_string key k DFrac.discard) $$ [$Hkey] as -
            (try wp_auto)
            wp_apply wp_slice_literal
            isplitr
            · ipureintro; rfl
            iintro %items ⟨Hitems, -⟩
            wp_apply (HAttach leaseID items _ (DFrac.own 1)) $$ [$Hknown $Hitems] as -
            (try wp_auto)
            wp_if_destruct
            rotate_left
            · exfalso; exact Hif rfl
            (try wp_auto)
            wp_apply (hStep trace _ _)
            (try wp_auto)
            iapply HΦ; iexact Htw'

end proof

end EtcdGrove
end Perennial
