/-
**The store's steps on its tracked compaction** (stage 2, the snapshot image's (a) and (c),
2026-11-05). Lean-first (no Rocq counterpart).

* `cmpRest_sched`: `Compact`'s scheduled record at `rev` re-pins the tracked compaction
  (`snap.cmpOk_sched`), the records' compaction revision moved to `rev` (the placeholder
  `rcvSched_M1`: the writer's half, with the compactor's share, is `KV.Compact.contract`'s).
* `compactLend_sched`: `updateCompactRev`'s loan of the compaction keys' write right at its values
  for `SetScheduledCompact`'s put (`mwLend`): the registration opened (a loan to a freezer excluded:
  `regLent_excl_M1`), the key swapped for the right's flag (`mwSwap_of_inv`), the values' halves
  from the tracked compaction; at the put's values, the record updated and the compaction re-pinned.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.M1Placeholders
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.CmpTrack

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section steps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **`Compact`'s scheduled record re-pins the tracked compaction** at `rev`, the records'
compaction revision's lower bounds raised to it (one minted for the job, `cmpLb`). -/
theorem cmpRest_sched (γ : StoreNames) (L : Log) (hb : LogB L) (m : Bucket) (fin sched : Option w64)
    (X : backend.VData) (rev : w64) :
    ⊢ cmpRest (GF := GF) γ L m ⟨fin, sched⟩ X ==∗
      cmpRest γ L m ⟨fin, some rev⟩ X ∗ cmpLb γ (sint.Z rev) := by
  unfold cmpRest cmpLb
  split
  · split
    · iintro ⟨Hr, Hl, %jc, Hj, %Hok⟩
      ihave ⟨%Hb, Hr⟩ := rcvSched_M1 γ L _ (sint.Z rev) $$ Hr
      obtain ⟨h1, hcr, hrl⟩ := Hb
      have hw : (W64 (sint.Z rev) : w64) = rev := by word
      obtain ⟨hok, hc⟩ := snap.cmpOk_sched hb Hok (sint.Z rev) h1 hcr hrl
      rw [hw] at hok hc
      simp only at hc ⊢
      rw [hc]
      have hn : crevN (CmpRecs.crev ⟨fin, sched⟩) ≤ crevN (sint.Z rev) := by
        unfold crevN; omega
      imod mono_nat_own_update (crevN (sint.Z rev)) hn $$ Hl with ⟨Hl, #Hlb⟩
      imodintro
      iframe Hr Hl Hlb
      isplitl
      · iexists jc; iframe Hj; ipureintro; exact hok
      ipureintro; exact h1
    · iintro -; imodintro; isplitl <;> itrivial
  · iintro -; imodintro; isplitl <;> itrivial

/-- **A commit keeps the tracked compaction** (`storeTxnWrite.End`'s new revision `pend` above
`L`: `snap.cmpOk_append`). -/
theorem cmpTrack_append (γ : StoreNames) (L : Log) (pend : List Change) (hb : LogB (L ++ [pend]))
    (hne : L ≠ []) (m : Bucket) (rc : CmpRecs) :
    cmpTrack (GF := GF) γ L m rc ⊢
      cmpTrack γ (L ++ [pend]) ((pendPuts L pend).foldl (fun m p => GMap.insert p.1 p.2 m) m) rc := by
  unfold cmpTrack
  split
  · split
    · iintro ⟨Hf, Hr, Hl, %X, %jc, Hd, Hj, %Hok⟩
      iframe Hf Hr Hl
      iexists X, jc
      iframe Hd Hj
      ipureintro; exact snap.cmpOk_append hb hne Hok
    · iintro -; itrivial
  · iintro -; itrivial

/-- The bucket's full view from `s.revMu`'s half, a write transaction's part and the compaction's
part's eighth. -/
theorem bucketView_join3 (γ : StoreNames) (m : Bucket) :
    bucketView (GF := GF) γ (1 : Qp).half m ∗ bucketView γ txQ m ∗
      bucketView γ (1 : Qp).half.half.half m ⊢ bucketView γ 1 m := by
  have h := (bucketView_fractional (GF := GF) γ m).fractional (1 : Qp).half
    (txQ + (1 : Qp).half.half.half)
  have h2 := (bucketView_fractional (GF := GF) γ m).fractional txQ (1 : Qp).half.half.half
  rw [txQ_one] at h
  iintro ⟨H1, H2, H3⟩
  iapply h.2; iframe H1
  iapply h2.2; iframe H2 H3

/-- Two parts of the view, at any logs, join at the first's (they hold one bucket), the second's
fraction first. -/
theorem bucketViewL_join2 (γ : StoreNames) (q1 q2 : Qp) (L1 L2 : Log) :
    bucketViewL (GF := GF) γ q1 L1 ∗ bucketViewL γ q2 L2 ⊢ bucketViewL γ (q2 + q1) L1 := by
  have hf := fun m => (bucketView_fractional (GF := GF) γ m).fractional q2 q1
  unfold bucketViewL
  iintro ⟨⟨%m1, H1, #Hl1⟩, ⟨%m2, H2, -⟩⟩
  ihave %Heq := bucketView_agree γ _ _ m1 m2 $$ [H1 H2]
  · iframe H1 H2
  subst Heq
  iexists m1
  iframe Hl1
  iapply (hf m1).2
  iframe H1 H2

/-- The records' compaction revision's part, from its ghost variable (dropped for a backend that does
not track it). -/
theorem rcvW_intro (γ : StoreNames) (q : Qp) (c : Int) :
    ghostVar (GF := GF) γ.rcv q c ⊢ rcvW γ q c := by
  unfold rcvW
  split
  · split
    · iintro H; iexact H
    · iintro -; itrivial
  · iintro -; itrivial

/-- The write right's flag part, of the write right at some values. -/
theorem kbMW_flag (kb : Option KBReal) (γb : GName) : kbMW (GF := GF) kb γb ⊢ kbMWf kb γb := by
  unfold kbMW
  iintro ⟨%w, %X, H⟩
  icases (kbMWv_split kb γb w X).1 $$ H with ⟨H, -⟩
  iexact H

/-- The put of the scheduled record's bytes is the record's. -/
theorem fkPutV_sched (fin sched : Option w64) (rev : w64) :
    fkPutV (recBytes fin, recBytes sched) schedKeyBytes (revBytes ⟨rev, W64 0⟩ false) =
      (recBytes fin, recBytes (some rev)) := by
  have h : schedKeyBytes ≠ finKeyBytes := by decide
  unfold fkPutV
  simp only [h, ↓reduceIte]
  rfl

/-- **`updateCompactRev`'s loan of the write right for `SetScheduledCompact`'s put** (see the file
header): the record updated to `rev` and the tracked compaction re-pinned when the right comes
back at the put's values. -/
theorem compactLend_sched (s : Loc) (γ : StoreNames) (h : kbCmpM γ.kb) (rev : w64) :
    physCmp (GF := GF) s γ ⊢ mwLend (storeW s γ) (kbMWv γ.kb γ.bucket)
      (fun w => fkPutV w schedKeyBytes (revBytes ⟨rev, W64 0⟩ false))
      iprop(cmpLb γ (sint.Z rev) ∗ storeRegd s γ) := by
  iintro #HmwP
  icases (physCmp_on s γ h).1 $$ HmwP with ⟨#Hmwi, #Hrg⟩
  ihave #Hswk := mwSwap_of_inv γ iprop(True) $$ Hmwi
  iunfold mwLend
  iintro !> ⟨HW, Hlc⟩
  ihave HE : iprop(emp) $$ []
  · iempintro
  imod storeW_open s γ ⊤ (by solve_ndisj) iprop(emp) (regLent_excl_M1 γ) $$ Hrg HE HW
    with ⟨HWr, #Hreg, -⟩
  iunfold writerRes at HWr
  icases HWr with ⟨%L, Hwk, Hwv, Hbv, #Hcert, %Hne, Hcres⟩
  ihave #Hc2 := Hcert
  iunfold idxCert at Hc2
  icases Hc2 with ⟨-, %Hlwf, -⟩
  have hb : LogB L := ⟨Hlwf.2.1, Hlwf.2.2⟩
  iunfold compactRes at Hcres
  icases Hcres with ⟨%sched, %fin, %n, %m, Hmeta, Hfin, %Hn, Hmk, Hbm, Htr⟩
  ihave Hmk := (mwSlot_on γ h).1 $$ Hmk
  iunfold mwSwap at Hswk
  imod Hswk $$ [Hmk Hlc] with ⟨Hf, Hfback⟩
  · iframe Hmk Hlc
  icases (cmpTrack_split γ h L m ⟨fin, sched⟩).1 $$ Htr with ⟨%X, Hv, Hrest⟩
  imodintro
  iexists (recBytes fin, recBytes sched), X
  isplitl [Hf Hv]
  · iapply (kbMWv_split γ.kb γ.bucket _ X).2; iframe Hf Hv
  simp only [fkPutV_sched fin sched rev]
  iintro HMW
  icases (kbMWv_split γ.kb γ.bucket _ X).1 $$ HMW with ⟨Hf, Hv⟩
  imod Hfback $$ Hf with ⟨Hmk, -⟩
  ihave Hmk := (mwSlot_on γ h).2 $$ Hmk
  iunfold metaCompact at Hmeta
  imod ghostVar_update (some rev, fin) γ.cmeta _ $$ Hmeta with Hmeta
  imod cmpRest_sched γ L hb m fin sched X rev $$ Hrest with ⟨Hrest, #Hlb⟩
  imodintro
  iframe Hlb Hreg
  iapply storeW_put s γ
  iframe Hreg
  iunfold writerRes
  iexists L
  iframe Hwk Hwv Hbv Hcert
  isplitr
  · ipureintro; exact Hne
  iunfold compactRes
  iexists (some rev), fin, n, m
  iunfold metaCompact
  iframe Hmeta Hfin Hmk Hbm
  isplitr
  · ipureintro; exact Hn
  iapply (cmpTrack_split γ h L m ⟨fin, some rev⟩).2
  iexists X
  iframe Hv Hrest

end steps

end mvcc
end EtcdGrove
end Perennial
