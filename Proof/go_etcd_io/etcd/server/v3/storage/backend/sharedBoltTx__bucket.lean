/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/sharedBoltTx__bucket.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.sharedBoltTx__bucket
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.sharedBoltTx__lock
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.sharedBoltTx__unlock
public import Spec.go_etcd_io.bbolt.Tx__Bucket_kvr

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend backend

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

theorem backend.sharedBoltTx.bucket.wp_proof
    (hLock : backend.sharedBoltTx.lock.spec (GF := GF) (hG := hG))
    (hUnlock : backend.sharedBoltTx.unlock.spec (GF := GF) (hG := hG))
    (hBucket : bbolt.Tx.Bucket_kvr.spec (GF := GF) (hG := hG)) :
    backend.sharedBoltTx.bucket.spec (GF := GF) (hG := hG) := by
  intro γ P st dq rtx D q bk bi Hhas
  wp_start as ⟨Hrd, #Hbk⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  unfold stRd
  icases Hrd with ⟨%cm, %tm, Hrtx, Hcm, #Htm, Hown, #Hg, Hlive, #Hsnap, #Hintv, %HPwf⟩
  unfold isBucket
  icases Hbk with ⟨%bo, %hbo, #Hid, #Hname, #Hsafe'⟩
  subst hbo
  wp_auto
  wp_apply Hid
  -- the buckets cache, under `txMu.RLock()`
  wp_apply sync.RWMutex.wp_RLock $$ [$Hown] as ⟨Hrl, HP⟩
  unfold tmTok
  icases HP with ⟨Hta, Htb⟩
  imod intv_borrow γ P rtx cm D sync.rfrac ⊤ (by solve_ndisj) $$ [$Hintv $Hta]
    with ⟨%M, HM, #Hf⟩
  wp_apply wp_map_lookup2 $$ HM as HM
  imod intv_return γ P rtx cm D sync.rfrac M ⊤ (by solve_ndisj) $$ [$Hintv $HM $Hf] with Hta
  wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl Hta Htb] as Hown
  · iframe
  -- not cached: under `st.lock()`, the bucket from the transaction, cached
  wp_join iprop(∃ bkv : Loc, bucket_ptr ↦ bkv ∗ bktFact rtx D bi.name bkv ∗
      rtxOf st ↦{dq} rtx ∗ txLive rtx q ∗ st_ptr ↦ st ∗ bucketType_ptr ↦ GoInterface.ok bo ∗
      bn_ptr ↦ bi.id ∗ rbktOf st ↦{dq} cm)
    with [bucket Hrtx Hlive st bucketType bn Hcm]
    as ⟨%bkv, bucket, #Hbf, Hrtx, Hlive, st, bucketType, bn, Hcm⟩
  · -- in the cache
    have hsome : ∃ bk0, M.lookup bi.id = some bk0 := by
      cases h : M.lookup bi.id with
      | none => rw [show M !! bi.id = M.lookup bi.id from rfl, h] at Hif; simp at Hif
      | some bk0 => exact ⟨bk0, rfl⟩
    obtain ⟨bk0, hbk0⟩ := hsome
    ihave #Hbf := cmFacts_lookup P rtx D M bi bk0 HPwf Hhas hbk0 $$ Hf
    rw [show M !! bi.id = M.lookup bi.id from rfl, hbk0]
    iexists bk0
    iframe; iframe #
  · -- not in the cache
    wp_apply hLock st tm _ $$ [$Htm $Hg] as ⟨Hwl, HP⟩
    icases HP with ⟨Hta, Htb⟩
    imod stats_take γ P rtx cm D ⊤ (by solve_ndisj) $$ [$Hintv $Htb] with Hst
    wp_apply Hname as %sn #Hsn
    wp_apply hBucket $$ [$Hlive $Hsnap $Hst $Hsn] as %bkv ⟨Hlive, Hst, -, #Hbf⟩
    imod intv_borrow γ P rtx cm D 1 ⊤ (by solve_ndisj) $$ [$Hintv $Hta]
      with ⟨%M', HM, #Hf'⟩
    wp_apply +noauto wp_mapInsert $$ HM as HM
    ihave #Hf'' := cmFacts_insert P rtx D M' bi bkv Hhas $$ [Hf' Hbf]
    · iframe #; unfold bktFact; iexact Hbf
    imod intv_return γ P rtx cm D 1 _ ⊤ (by solve_ndisj) $$ [$Hintv $HM $Hf''] with Hta
    imod stats_give γ P rtx cm D ⊤ (by solve_ndisj) $$ [$Hintv $Hst] with Htb
    wp_auto
    wp_apply hUnlock st tm _ $$ [$Htm $Hwl Hta Htb]
    · iframe
    wp_join_done
    iexists bkv
    iframe; iframe #
    unfold bktFact; iexact Hbf
  iapply HΦ
  iframe #
  iframe
  ipureintro; exact HPwf

end proof

end EtcdGrove
end Perennial
