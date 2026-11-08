/-
**The store's steps on its tracked compaction** (stage 2, the snapshot image's (a) and (c),
2026-11-05). Lean-first (no Rocq counterpart).

* `cmpRest_sched`: `Compact`'s scheduled record at `rev` re-pins the tracked compaction
  (`snap.cmpOk_sched`), the records' compaction revision moved to `rev` with the writer's half
  (`KV.Compact.contract`, 2026-11-06: until then the placeholder `rcvSched_M1`).
* `compactLend_sched`: `updateCompactRev`'s one-shot loan of the compaction keys' write right at its
  values for `SetScheduledCompact`'s put (`mwLend`): the writer's invariant opened, its state found
  checked in (the frozen and restoring states excluded by the caller's `S`), so a freezer's loan of
  the registration is excluded by the frozen flag (until 2026-11-06 the placeholder
  `regLent_excl_M1`); the caller's ghost step `cmpCb` fired there (the API's update); the key swapped
  for the right's flag (`mwSwap_of_inv`), the values' halves from the tracked compaction; at the
  put's values, the record updated and the compaction re-pinned.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchStore
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.CmpTrack
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.LockArm

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
compaction revision moved to `rev` with the writer's half (`rcvW`, the writer's slot's: it agrees with
the records' at `c`, above which `rev` is), the lower bounds raised to it (one minted for the job,
`cmpLb`). (`KV.Compact.contract`, 2026-11-06: until then from the records' half only, by the
placeholder `rcvSched_M1`.) -/
theorem cmpRest_sched (γ : StoreNames) (L : Log) (hb : LogB L) (m : Bucket) (fin sched : Option w64)
    (X : backend.VData) (c : Int) (rev : w64) (h1 : 1 ≤ sint.Z rev) (hc : c ≤ sint.Z rev)
    (hrl : sint.Z rev < L.length) :
    ⊢ rcvW (GF := GF) γ (1 : Qp).half c ∗ cmpRest γ L m ⟨fin, sched⟩ X ==∗
      rcvW γ (1 : Qp).half (sint.Z rev) ∗ cmpRest γ L m ⟨fin, some rev⟩ X ∗ cmpLb γ (sint.Z rev) := by
  unfold rcvW cmpRest cmpLb
  cases hk : γ.kb with
  | none => simp only; iintro -; imodintro; isplitl <;> (try isplitl) <;> itrivial
  | some d =>
    simp only
    by_cases hd : d.cm = true
    · simp only [hd, ↓reduceIte]
      iintro ⟨HY, Hr, Hl, %jc, Hj, %Hok⟩
      ihave %Hcc := ghostVar_agree γ.rcv _ _ _ _ $$ HY Hr
      imod ghostVar_update_2 (sint.Z rev) γ.rcv _ _ _ _ (Qp.half_add_half 1) $$ HY Hr with ⟨HY, Hr⟩
      have hw : (W64 (sint.Z rev) : w64) = rev := by word
      obtain ⟨hok, hcr⟩ := snap.cmpOk_sched hb Hok (sint.Z rev) h1 (by rw [← Hcc]; exact hc) hrl
      rw [hw] at hok hcr
      simp only at hcr ⊢
      rw [hcr]
      have hn : crevN (CmpRecs.crev ⟨fin, sched⟩) ≤ crevN (sint.Z rev) := by
        unfold crevN; rw [← Hcc]; omega
      imod mono_nat_own_update (crevN (sint.Z rev)) hn $$ Hl with ⟨Hl, #Hlb⟩
      imodintro
      iframe HY Hr Hl Hlb
      isplitl
      · iexists jc; iframe Hj; ipureintro; exact hok
      ipureintro; exact h1
    · simp only [hd, Bool.false_eq_true, ↓reduceIte]
      iintro -; imodintro; isplitl <;> (try isplitl) <;> itrivial

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

/-- A frozen flag down excludes a freezer's loan of the registration (its quarter of the flag up). -/
theorem slotFl_regLent (γ : StoreNames) : slotFl (GF := GF) γ 1 false ∗ regLent γ ⊢ False := by
  unfold slotFl regLent
  cases γ.kb with
  | none => simp only; iintro ⟨-, H⟩; iexact H
  | some d =>
    simp only
    iintro ⟨H1, -, H2⟩
    ihave %Hv := ghostVar_valid_2 γ.api.frz false 1 true (1 : Qp).half.half $$ H1 H2
    exact absurd Hv.1 (Qp_one_add_not_le _)

/-- **`updateCompactRev`'s loan of the write right for `SetScheduledCompact`'s put** (see the file
header; one-shot since `KV.Compact.contract`, 2026-11-06): the batch lock's resource opened with the
writer's invariant, the writer's state found checked in (the open writer's state excluded by the
lock's key, the frozen and restoring states by the caller's excluder `S`: the API compactor's share of
the backend token, or `restore()`'s holder of `s.mu`'s deposit ghost), so its frozen flag down
excludes a freezer's loan of the registration; the caller's ghost step (`cmpCb`) fired there, moving
`s.revMu`'s slot and the writer's view to `rev`, and the records' compaction revision with it
(`cmpRest_sched`); the key swapped for the right's flag, the values' halves from the tracked
compaction; at the put's values, the record updated and the compaction re-pinned. -/
theorem compactLend_sched (s : Loc) (γ : StoreNames) (h : kbCmpM γ.kb) (rev : w64) (L : Log)
    (c cp : Int) (S Fok Fce Ffr : IProp GF) (dq : DFrac) (o : StoreObjs)
    (hS1 : slotF γ ∗ S ⊢ False) (hS2 : ghostVar γ.wr 1 () ∗ slotFr γ ∗ S ⊢ False)
    (hcp : cp < sint.Z rev) (hc : c ≤ sint.Z rev) (hr : sint.Z rev < L.length)
    (h1 : 1 ≤ sint.Z rev) :
    physCmp (GF := GF) s γ ∗ writerInv s γ ∗ £ 1 ∗ S ∗ curAt γ dq o ∗ slotX γ 1 L c ∗
        api.wcrPart γ.api (1 : Qp).half c ∗ cmpCb γ c cp (sint.Z rev) Fok Fce Ffr ⊢
      mwLend (storeW s γ) (kbMWv γ.kb γ.bucket)
        (fun w => fkPutV w schedKeyBytes (revBytes ⟨rev, W64 0⟩ false))
        iprop(cmpLb γ (sint.Z rev) ∗ storeRegd s γ ∗ S ∗ curAt γ dq o ∗ slotX γ 1 L (sint.Z rev) ∗
          api.wcrPart γ.api (1 : Qp).half (sint.Z rev) ∗ Fok) := by
  iintro ⟨#HmwP, #Hwi, Hlc0, HS, Hpin, HX, HwcM, Hcb⟩
  icases (physCmp_on s γ h).1 $$ HmwP with ⟨#Hmwi, #Hrg⟩
  ihave #Hswk := mwSwap_of_inv γ iprop(True) $$ Hmwi
  iunfold mwLend
  iintro ⟨HW, Hlc⟩
  -- the writer's invariant: the writer's state checked in
  ihave #Hwi' := Hwi
  iunfold writerInv at Hwi'
  imod inv_acc (E := ⊤) (N := writerN) (P := writerInvBody (GF := GF) s γ)
    (by exact CoPset.subseteq_top) $$ Hwi' with ⟨HP, Hclose⟩
  imod (lc_fupd_elim_later (P := writerInvBody (GF := GF) s γ)) $$ Hlc0 HP with HP
  iunfold writerInvBody at HP
  icases HP with (⟨%p, %o', Hc, HP⟩ | ⟨Hwr, -, HFr, -⟩)
  rotate_left 1
  · iexfalso; iapply hS2; iframe Hwr HFr HS
  ihave %Hv := curAt_pin γ p _ _ o o' $$ [Hpin Hc]
  · iframe Hpin Hc
  obtain ⟨rfl, rfl⟩ := Hv
  rw [StoreNames.withPhys_self]
  icases HP with (⟨Hfz, HT⟩ | ⟨-, HF⟩)
  rotate_left 1
  · iexfalso; iapply hS1; iframe HF HS
  -- the registration opened, a freezer's loan excluded by the frozen flag down
  imod storeW_open s γ (⊤ \ ↑writerN) (by solve_ndisj) (slotFl γ 1 false) (slotFl_regLent γ)
    $$ Hrg Hfz HW with ⟨HWr, #Hreg, Hfz⟩
  iunfold writerRes at HWr
  icases HWr with ⟨%Lb, HwkB, HwvB, HbvB, #HcertB, %HneB, Hcres, HpinB⟩
  icases HT with (⟨Hwl, #Hwreg⟩ | ⟨Hwk', -, -⟩)
  rotate_left 1
  · iexfalso
    iunfold writerKey at HwkB Hwk'
    ihave %Hv := ghostVar_valid_2 γ.wk () 1 () 1 $$ HwkB Hwk'
    exact absurd Hv.1 (Qp_one_add_not_le _)
  iunfold writerL at Hwl
  icases Hwl with ⟨%ilog, %ntok, Hwl⟩
  iNamed Hwl
  ihave %HL1 := ghostVar_agree γ.wv _ _ _ _ $$ HwvB Hwv
  subst HL1
  iunfold slotY at HY
  icases HY with ⟨%cY, HYa, HYp, HYr, HYw⟩
  iunfold slotX at HX
  iunfold api.revMuAbs at HX
  icases HX with ⟨HXa, HXc⟩
  ihave %Hag := api.absPart_agree γ.api _ _ _ _ _ _ $$ [HXa HYa]
  · iframe HXa HYa
  obtain ⟨HL2, Hcc⟩ := Hag
  subst HL2 Hcc
  ihave HX : slotX (GF := GF) γ 1 L c $$ [HXa HXc]
  · iunfold slotX; iunfold api.revMuAbs; iframe HXa HXc
  ihave #Hc2 := HcertB
  iunfold idxCert at Hc2
  icases Hc2 with ⟨-, %Hlwf, -⟩
  have hb : LogB L := ⟨Hlwf.2.1, Hlwf.2.2⟩
  iunfold compactRes at Hcres
  icases Hcres with ⟨%sched, %fin, %n, %m, Hmeta, Hfin, %Hn, Hmk, Hbm, Htr⟩
  icases (cmpTrack_split γ h L m ⟨fin, sched⟩).1 $$ Htr with ⟨%X, Hv, Hrest⟩
  -- the records' compaction revision moved with the writer's, the lower bounds raised
  imod cmpRest_sched γ L hb m fin sched X c rev h1 hc hr $$ [HYr Hrest] with ⟨HYr, Hrest, #Hlb⟩
  · iframe HYr Hrest
  -- the caller's ghost step: the lock's slot and the writer's view at `rev`
  iunfold cmpCb at Hcb
  icases Hcb with ⟨Hok, -⟩
  imod Hok $$ %L [] [HX HYa HYp] with ⟨HX, HYa, HYp, HFok⟩
  · ipureintro; exact ⟨hcp, hc, hr⟩
  · iframe HX HYa HYp
  -- the writer's and `s.mu`'s compaction revision moved with it (M4, track B)
  imod api.wcrPart_update γ.api _ _ (Qp.half_add_half 1) _ _ (sint.Z rev) $$ [HYw HwcM]
    with ⟨HYw, HwcM⟩
  · iframe HYw HwcM
  -- the writer's state back, at the moved view
  imod Hclose $$ [Hc Hfz HYa HYp HYr HYw Htoks Hw Hclog Hwv Hcur Hlrd Hrtk] with -
  · inext
    iunfold writerInvBody
    ileft
    iexists γ.phys, o'
    rw [StoreNames.withPhys_self]
    iframe Hc
    ileft
    iframe Hfz
    ileft
    iframe Hwreg
    iunfold writerL
    iexists L, ntok
    simp only [named]
    iframe Htoks Hw Hclog Hwv Hcur Hlrd Hcert Hrtk
    isplitr
    · ipureintro; exact Hbudget
    isplitr
    · ipureintro; exact Hne
    iunfold slotY
    iexists (sint.Z rev)
    iframe HYa HYp HYr HYw
  -- the key swapped for the right's flag
  ihave Hmk := (mwSlot_on γ h).1 $$ Hmk
  iunfold mwSwap at Hswk
  imod Hswk $$ [Hmk Hlc] with ⟨Hf, Hfback⟩
  · iframe Hmk Hlc
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
  imodintro
  iframe Hlb Hreg HS Hpin HX HwcM HFok
  iapply storeW_put s γ
  iframe Hreg
  iunfold writerRes
  iexists L
  iframe HwkB HwvB HbvB HcertB HpinB
  isplitr
  · ipureintro; exact HneB
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
