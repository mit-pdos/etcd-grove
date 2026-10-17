/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/baseReadTx__UnsafeRange.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.baseReadTx__UnsafeRange
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.ReadLemmas
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.txReadBuffer__Range
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.unsafeRange
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.sharedBoltTx__bucket
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.sharedBoltTx__lock
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.sharedBoltTx__unlock
public import Spec.go_etcd_io.bbolt.Bucket__Cursor_kvr

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

theorem backend.bktEnts_empty : bktEnts (∅ : BktData) = [] := by
  unfold bktEnts; rw [GMap.toList_empty]; simp

theorem backend.cursorRange_nil (kb eb : GoString) (limit : w64) : cursorRange [] kb eb limit = [] := by
  unfold cursorRange seekIdx; split <;> simp

theorem backend.rtRange_full (rv : RView) (bi : BucketInfo) (kb eb : GoString) (limit : w64)
    (h : ((bbRange (bkOf rv.2.bks bi.id) kb eb (rangeLimit eb limit)).length : Int) =
      sint.Z (rangeLimit eb limit)) :
    rtRange rv bi kb eb limit = bbRange (bkOf rv.2.bks bi.id) kb eb (rangeLimit eb limit) := by
  unfold rtRange; simp only [h, ite_true]

theorem backend.rtRange_rest (rv : RView) (bi : BucketInfo) (kb eb : GoString) (limit : w64)
    (h : ¬ ((bbRange (bkOf rv.2.bks bi.id) kb eb (rangeLimit eb limit)).length : Int) =
      sint.Z (rangeLimit eb limit)) :
    rtRange rv bi kb eb limit =
      cursorRange (bktEnts (bktOf rv.1 bi.name)) kb eb (rangeLimit eb limit -
        W64 (bbRange (bkOf rv.2.bks bi.id) kb eb (rangeLimit eb limit)).length) ++
      bbRange (bkOf rv.2.bks bi.id) kb eb (rangeLimit eb limit) := by
  unfold rtRange; simp only [h, ite_false]

theorem backend.baseReadTx.UnsafeRange.wp_proof
    (hRange : backend.txReadBuffer.Range.spec (GF := GF) (hG := hG))
    (hbucket : backend.sharedBoltTx.bucket.spec (GF := GF) (hG := hG))
    (hLock : backend.sharedBoltTx.lock.spec (GF := GF) (hG := hG))
    (hCursor : bbolt.Bucket.Cursor_kvr.spec (GF := GF) (hG := hG))
    (hUnlock : backend.sharedBoltTx.unlock.spec (GF := GF) (hG := hG))
    (hur : backend.unsafeRange.spec (GF := GF) (hG := hG)) :
    backend.baseReadTx.UnsafeRange.spec (GF := GF) (hG := hG) := by
  intro γ P W Pk b base dq rtx rv q bk bi key endKey kb eb dk de limit Hnil Hsafe Hhas
  wp_start as ⟨Hrd, #Hbk, Hk, He⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  unfold baseRd
  icases Hrd with ⟨%m, %Pb, %st, Hrb, #Hst, Hsr, %Hwf⟩
  ihave %Hel := ownSlice_len _ _ _ $$ He
  unfold isBucket
  icases Hbk with ⟨%bo, %hbo, #Hid, #Hname, #Hsafe'⟩
  subst hbo
  wp_auto
  -- the limit: `rangeLimit`
  wp_join iprop(limit_ptr ↦ (if eb = [] then W64 1 else limit)) with [limit] as limit
  · rw [if_pos (Hnil.1 rfl)]; iframe
  · rw [if_neg (fun h => Hif (Hnil.2 h))]; iframe
  wp_join iprop(limit_ptr ↦ rangeLimit eb limit) with [limit] as limit
  · unfold rangeLimit
    by_cases heb : eb = []
    · simp only [heb, ite_true] at Hif ⊢; exfalso; revert Hif; decide
    · simp only [heb, ite_false] at Hif ⊢; rw [if_pos (by word)]; iframe
  · unfold rangeLimit
    by_cases heb : eb = []
    · simp only [heb, ite_true] at Hif ⊢; iframe
    · simp only [heb, ite_false] at Hif ⊢; rw [if_neg (by word)]; iframe
  -- the safe-range check: no panic
  wp_join with [limit bucketType]
  · wp_apply Hsafe'
    cases hs : bi.safe
    · exfalso; rcases Hsafe with h | h
      · word
      · rw [hs] at h; cases h
    · wp_auto
      wp_join_done
  wp_apply hRange _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hwf.1 $$ [$Hrb $Hk $He]
    as %keys %vals ⟨Hrb, Hk, He, Hout⟩
  · unfold isBucket; iexists bo; iframe #; ipureintro; rfl
  unfold kvsOut
  icases Hout with ⟨%ks, %vs, Hks, Hksc, Hvs, Hvsc, #Hka, #Hva⟩
  ihave %Hksl := ownSlice_len _ _ _ $$ Hks
  ihave %Hkal := slicesAre_len _ _ $$ Hka
  simp only [List.length_map] at Hkal
  wp_if_destruct
  · -- the read buffer has `limit` entries
    rw [rtRange_full rv bi kb eb limit (by rw [← Hkal, Hksl.1, Hif]; word)]
    iapply HΦ
    isplitl [Hrb Hsr]
    · iexists m, Pb, st; iframe; iframe #; ipureintro; exact Hwf
    iframe
    iapply kvsOutRd_of_kvsOut
    unfold kvsOut
    iexists ks, vs
    iframe; iframe #
  have hne : ¬ ((bbRange (bkOf rv.2.bks bi.id) kb eb (rangeLimit eb limit)).length : Int) =
      sint.Z (rangeLimit eb limit) := by
    intro h; apply Hif; apply BitVec.eq_of_toInt_eq
    show sint.Z keys.len = sint.Z (rangeLimit eb limit); rw [← h, ← Hkal, Hksl.1]; word
  rw [rtRange_rest rv bi kb eb limit hne]
  -- the bucket, from the shared transaction
  wp_apply hbucket γ P st dq rtx rv.1 q (GoInterface.ok bo) bi Hhas $$ [$Hsr]
    as %bkv ⟨Hsr, #Hbf⟩
  · unfold isBucket; iexists bo; iframe #; ipureintro; rfl
  wp_if_destruct
  · -- no such bucket in the transaction's snapshot: the read buffer's entries
    unfold bktFact
    icases Hbf with (%Hnone | ⟨%m', %Hsome, -⟩)
    rotate_left
    · exfalso; exact Hsome.2 rfl
    rw [show bktOf rv.1 bi.name = ∅ by unfold bktOf; rw [Hnone.1]; rfl, bktEnts_empty,
      cursorRange_nil, List.nil_append]
    iapply HΦ
    isplitl [Hrb Hsr]
    · iexists m, Pb, st; iframe; iframe #; ipureintro; exact Hwf
    iframe
    iapply kvsOutRd_of_kvsOut
    unfold kvsOut
    iexists ks, vs
    iframe; iframe #
  -- the bucket is there: a cursor, under `tx.lock()`
  unfold bktFact
  icases Hbf with (%Hnone | ⟨%mb, %Hsome, #Hrb'⟩)
  · exfalso; exact Hif Hnone.2
  unfold stRd
  icases Hsr with ⟨%cm, %tm, Hrtx, Hcm, #Htm, Hown, #Hg, Hlive, #Hsnap, #Hintv, %HPwf⟩
  wp_apply hLock st tm _ $$ [$Htm $Hg] as ⟨Hwl, HP⟩
  unfold tmTok
  icases HP with ⟨Hta, Htb⟩
  imod stats_take γ P rtx cm rv.1 ⊤ (by solve_ndisj) $$ [$Hintv $Htb] with Hstt
  wp_apply hCursor $$ [$Hrb' $Hstt $Hlive] as %c ⟨Hc, Hstt, Hlive⟩
  imod stats_give γ P rtx cm rv.1 ⊤ (by solve_ndisj) $$ [$Hintv $Hstt] with Htb
  wp_apply hUnlock st tm _ $$ [$Htm $Hwl Hta Htb]
  · iframe
  have hkl : keys.len = W64 ((bbRange (bkOf rv.2.bks bi.id) kb eb (rangeLimit eb limit)).length : Int) := by
    rw [← Hkal, Hksl.1]; word
  rw [hkl, show bktOf rv.1 bi.name = mb by unfold bktOf; rw [Hsome.1]; rfl]
  wp_apply hur $$ [$Hc $Hlive $Hk $He] as %k2 %v2 ⟨-, Hlive, Hk, He, Hout2⟩
  unfold kvsOutRd
  icases Hout2 with ⟨%kl2, %vl2, Hk2, Hk2c, Hv2, Hv2c, #Hka2, #Hva2⟩
  wp_apply (wp_slice_append k2 kl2 keys ks (DFrac.own 1)) $$ [Hk2 Hk2c Hks] as %ko ⟨Hko, Hkoc, -⟩
  · iframe
  wp_apply (wp_slice_append v2 vl2 vals vs (DFrac.own 1)) $$ [Hv2 Hv2c Hvs] as %vo ⟨Hvo, Hvoc, -⟩
  · iframe
  iapply HΦ
  isplitl [Hrb Hrtx Hcm Hown Hlive]
  · iexists m, Pb, st; iframe; iframe #
    ipureintro; exact ⟨HPwf, Hwf⟩
  iframe
  simp only [List.map_append]
  isplitl
  · iapply rdSlices_append; iframe #; iapply rdSlices_of_slicesAre $$ Hka
  · iapply rdSlices_append; iframe #; iapply rdSlices_of_slicesAre $$ Hva


end proof

end EtcdGrove
end Perennial
