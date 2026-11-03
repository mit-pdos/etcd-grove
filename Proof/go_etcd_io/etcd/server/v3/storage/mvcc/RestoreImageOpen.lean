/-
**The received image, by the mode, from the backend's open** (M2's item 15, stage B;
`notes/m2-storage-plan.md`, "Step 2: restore in compaction mode", (e)): the apply side's fact on a
snapshot's backend file (`keyImageM`: off, today's `keyImage`, the whole bucket of the restored log
and no compaction record; on, a bucket of entries cut at the records' revision, with the records in
the `Meta` bucket's compaction keys), and what `store.Restore` takes of the image
(`restoreImageM`), made from what the backend's constructor gives over the file (`bViewC`, `fkCl`):
`restoreImageM_of_open`. Moved here from the step's Draft (`M2StorageDraftRestore`: `keyImageM`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RestoreVocab
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Image

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

/-- **The image's facts, by the mode** (the apply side's obligations on the snapshot's file `D`,
S-j1's; review round 4): off, today's `keyImage` (the `Key` bucket the restored log's, no
compaction record) and no record; on, the `Key` bucket the entries `ents` cut at the records'
revision (a finished compaction or a leader's bucket mid-job), the `Meta` bucket's two compaction
keys holding the records' bytes, the records of `L` and past revision `0` (`recsPos`). (Until
#7-cmp's Freeze, 2026-11-02, also `NoDelPutAt L r.crev`: false of a legitimate image, a revision
deleting a key and putting it again compacted at itself, and used by no proof.) -/
def mvcc.keyImageM (cm : Bool) (L : mvcc.Log) (r : mvcc.CmpRecs) (D : backend.Data) : Prop :=
  if cm then ∃ ents : List mvcc.KvEnt,
      (∀ k, backend.dget D mvcc.keyName k = (mvcc.bucketOfEnts ents).lookup k) ∧
      backend.dget D go_etcd_io.etcd.server.v3.storage.schema.metaName mvcc.finKeyBytes =
        mvcc.recBytes r.fin ∧
      backend.dget D go_etcd_io.etcd.server.v3.storage.schema.metaName mvcc.schedKeyBytes =
        mvcc.recBytes r.sched ∧
      mvcc.recsOk L r ∧ mvcc.recsPos r ∧ mvcc.entsCutAt L r.crev ents
  else mvcc.keyImage L D ∧ r = mvcc.CmpRecs.empty

theorem mvcc.keyImageM_off (L : mvcc.Log) (r : mvcc.CmpRecs) (D : backend.Data) :
    mvcc.keyImageM false L r D ↔ mvcc.keyImage L D ∧ r = mvcc.CmpRecs.empty := by
  unfold mvcc.keyImageM; simp

/-! ### The image and the compaction tracking (F2, stage 2; review round 2's T2-3) -/

section tracked
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]

/-- **The tracked facts are the image** (pure; moved from `ImageCmpF2Draft`): a committed `D` whose
`Key` bucket, as the real instance `d`'s clients see it, is a cut physical view and whose
compaction keys hold the records' bytes is the image `keyImageM true` (what a snapshot's
observation gives the snapshot's sender). -/
theorem mvcc.keyImageM_of_tracked (d : mvcc.KBReal) (L : mvcc.Log) (r : mvcc.CmpRecs)
    (D : backend.Data) (hcut : mvcc.physCut L r (backend.sData d.P D))
    (hv : backend.fkVals D = (mvcc.recBytes r.fin, mvcc.recBytes r.sched)) :
    mvcc.keyImageM true L r D := by
  obtain ⟨ents, hk, hok, hpos, hc⟩ := hcut
  unfold mvcc.keyImageM
  simp only [↓reduceIte]
  refine ⟨ents, fun k => ?_, ?_, ?_, hok, hpos, hc⟩
  · rw [← hk k, backend.sData_lookup]; simp [mvcc.KBReal.P]
  · have := congrArg Prod.fst hv
    simp only [backend.fkVals] at this
    exact this
  · have := congrArg Prod.snd hv
    simp only [backend.fkVals] at this
    exact this

/-- **The image is tracked facts** (the converse, for the snapshot walk's open: `snap_create` takes
the image, the supplier's terms, and gives the lock's tracking its cut): the image `keyImageM true`
of `D` makes the instance's clients' view of `D` a physical cut at the records, whose bytes the
compaction keys hold. -/
theorem mvcc.tracked_of_keyImageM (d : mvcc.KBReal) (L : mvcc.Log) (r : mvcc.CmpRecs)
    (D : backend.Data) (h : mvcc.keyImageM true L r D) :
    mvcc.physCut L r (backend.sData d.P D) ∧
      backend.fkVals D = (mvcc.recBytes r.fin, mvcc.recBytes r.sched) := by
  unfold mvcc.keyImageM at h
  simp only [↓reduceIte] at h
  obtain ⟨ents, hk, hf, hs, hok, hpos, hc⟩ := h
  refine ⟨⟨ents, fun k => ?_, hok, hpos, hc⟩, Prod.ext hf hs⟩
  rw [backend.sData_lookup]; simp [mvcc.KBReal.P, hk k]

end tracked

/-! ### The image between the modes (#7-cmp's Freeze, 2026-11-02) -/

section modes
variable [GooseExts]

/-- The finished record is at most the restored revision. -/
theorem mvcc.CmpRecs.finRev_le_crev (r : mvcc.CmpRecs) : r.finRev ≤ r.crev := by
  unfold mvcc.CmpRecs.crev mvcc.CmpRecs.resumes
  split
  · rename_i h; simp only [decide_eq_true_eq] at h; omega
  · exact Int.le_refl _

/-- **No record at revision `-1`** (under `recsPos`, which `keyImageM` on gives). -/
theorem mvcc.CmpRecs.empty_of_crev (r : mvcc.CmpRecs) (hp : mvcc.recsPos r) (hc : r.crev = -1) :
    r = mvcc.CmpRecs.empty := by
  have hf : ∀ x, r.fin = some x → 1 ≤ sint.Z x := hp.1
  have hs : ∀ x, r.sched = some x → 1 ≤ sint.Z x := hp.2
  unfold mvcc.CmpRecs.crev mvcc.CmpRecs.resumes mvcc.CmpRecs.schedRev mvcc.CmpRecs.finRev at hc
  rcases r with ⟨_ | x, _ | y⟩ <;>
    simp only [Option.map_none, Option.map_some, Option.getD_none, Option.getD_some] at hf hs hc
  · rfl
  · have := hs y rfl
    have h0 : sint.Z y ≠ 0 := by omega
    have h1 : (-1 : Int) < sint.Z y := by omega
    simp [h0, h1] at hc; omega
  · have := hf x rfl; simp at hc; omega
  · have := hf x rfl; have := hs y rfl
    have h0 : sint.Z y ≠ 0 := by omega
    by_cases h : sint.Z x < sint.Z y <;> simp [h0, h] at hc <;> omega

/-- The mode on's records are past revision `0`. -/
theorem mvcc.keyImageM_recsPos (L : mvcc.Log) (r : mvcc.CmpRecs) (D : backend.Data)
    (h : mvcc.keyImageM true L r D) : mvcc.recsPos r := by
  unfold mvcc.keyImageM at h; simp only [↓reduceIte] at h
  obtain ⟨-, -, -, -, -, h, -⟩ := h; exact h

/-- **The mode off's image is the mode on's** (the whole bucket, no record: the cut at `-1`). -/
theorem mvcc.keyImageM_on_of_off (L : mvcc.Log) (r : mvcc.CmpRecs) (D : backend.Data)
    (h : mvcc.keyImageM false L r D) : mvcc.keyImageM true L r D := by
  obtain ⟨⟨hk, hs, hf⟩, rfl⟩ := (mvcc.keyImageM_off L r D).1 h
  unfold mvcc.keyImageM
  simp only [↓reduceIte]
  refine ⟨mvcc.logEnts L 0 L.length, fun k => by rw [mvcc.bucketOfEnts_logEnts]; exact hk k,
    hf, hs, ⟨(fun x hx => by simp [mvcc.CmpRecs.empty] at hx),
      (fun x hx => by simp [mvcc.CmpRecs.empty] at hx)⟩,
    ⟨(fun x hx => by simp [mvcc.CmpRecs.empty] at hx),
      (fun x hx => by simp [mvcc.CmpRecs.empty] at hx)⟩, ?_⟩
  exact mvcc.entsCutAt_full _ _

/-- **The mode on's image at no compaction is the mode off's**: records at `-1` are none
(`recsPos`), and the cut at `-1` deletes nothing (`KeyDel_neg`), so the bucket is the log's. -/
theorem mvcc.keyImageM_off_of_on (L : mvcc.Log) (r : mvcc.CmpRecs) (D : backend.Data)
    (hb : mvcc.LogB L) (h : mvcc.keyImageM true L r D) (hc : r.crev = -1) :
    mvcc.keyImageM false L r D := by
  have hpos := mvcc.keyImageM_recsPos L r D h
  unfold mvcc.keyImageM at h
  simp only [↓reduceIte] at h
  obtain ⟨ents, hk, hfin, hsched, -, -, hcut⟩ := h
  have hr := mvcc.CmpRecs.empty_of_crev r hpos hc
  subst hr
  rw [mvcc.keyImageM_off]
  refine ⟨⟨fun k => ?_, hsched, hfin⟩, rfl⟩
  rw [hk k, ← mvcc.bucketOfEnts_logEnts]
  have hall : ∀ e ∈ mvcc.logEnts L 0 L.length, e ∈ ents := by
    intro e he
    exact Classical.byContradiction fun hn => mvcc.KeyDel_neg (by decide) (hcut.2.1 e he hn)
  apply Option.ext
  intro v
  have h1 := mvcc.bucketOfEnts_lookup_iff L hb hcut.1 k v
  have h2 := mvcc.bucketOfEnts_lookup_iff L hb (List.Sublist.refl (mvcc.logEnts L 0 L.length)) k v
  change (mvcc.bucketOfEnts ents).lookup k = some v ↔ _ at h1
  change (mvcc.bucketOfEnts (mvcc.logEnts L 0 L.length)).lookup k = some v ↔ _ at h2
  rw [h1, h2]
  constructor
  · intro hm
    exact (hcut.1.map mvcc.KvEnt.pair).subset hm
  · intro hm
    obtain ⟨e, he, hpe⟩ := List.mem_map.1 hm
    exact List.mem_map.2 ⟨e, hall e he, hpe⟩

/-- **An image moves between the modes** when, for the mode off, the records' revision is `-1`. -/
theorem mvcc.keyImageM_mode (b b' : Bool) (L : mvcc.Log) (r : mvcc.CmpRecs) (D : backend.Data)
    (hb : mvcc.LogB L) (h : mvcc.keyImageM b L r D) (hc : b = true → b' = false → r.crev = -1) :
    mvcc.keyImageM b' L r D := by
  cases b <;> cases b'
  · exact h
  · exact mvcc.keyImageM_on_of_off L r D h
  · exact mvcc.keyImageM_off_of_on L r D hb h (hc rfl rfl)
  · exact h

end modes

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [backend_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- **The image's records' revision is at least `-1`**, and off there is no record. -/
theorem mvcc.keyImageM_crev (cm : Bool) (L : mvcc.Log) (r : mvcc.CmpRecs) (D : backend.Data)
    (h : mvcc.keyImageM cm L r D) : -1 ≤ r.crev ∧ (cm = false → r = mvcc.CmpRecs.empty) := by
  cases cm with
  | false =>
    obtain ⟨-, hr⟩ := (mvcc.keyImageM_off L r D).1 h
    subst hr
    exact ⟨by rw [mvcc.CmpRecs.crev_empty]; exact Int.le_refl _, fun _ => rfl⟩
  | true =>
    unfold mvcc.keyImageM at h
    simp only [↓reduceIte] at h
    obtain ⟨-, -, -, -, -, hpos, -⟩ := h
    refine ⟨?_, fun h => absurd h (by decide)⟩
    rcases mvcc.recsPos_crev r hpos with h | h <;> omega

/-- A record's bytes are a value the store writes at a compaction key. -/
theorem mvcc.recBytes_metaRevVal {x : Option w64} {v : GoString} (hx : ∀ y, x = some y → 1 ≤ sint.Z y)
    (h : mvcc.recBytes x = some v) : mvcc.metaRevVal v := by
  cases hxs : x with
  | none => simp [hxs, mvcc.recBytes] at h
  | some y =>
    simp only [hxs, mvcc.recBytes, Option.map_some, Option.some.injEq] at h
    subst h
    exact ⟨y, by have := hx y hxs; omega, rfl⟩

/-- **On, the image `Restore` takes, from the backend's open** (the walk's step after
`OpenSnapshotBackend`): the view of the opened data (`bViewC`) is the cut entries' bucket, and the
constructor's compaction-key resource (`fkCl`) gives the records' write right at the flag the open
left (`kbRecs`) and the bit (`fkVM`): the records are revisions, so the keys are well formed. -/
theorem mvcc.restoreImageM_of_openOn (d' : mvcc.KBReal) (γb : GName) (L : mvcc.Log)
    (r : mvcc.CmpRecs) (D : backend.Data) (hcm : d'.cm = true) (hbr : mvcc.bridgeParams d'.P)
    (h : mvcc.keyImageM true L r D) :
    backend.bViewC d'.γB 1 (backend.vData d'.P (D, ⟨∅, W64 0⟩)) true ∗ backend.fkCl d'.γB d'.P D ⊢
      mvcc.restoreImageM (GF := GF) d' γb L r := by
  unfold mvcc.keyImageM at h
  simp only [↓reduceIte] at h
  obtain ⟨ents, hk, hfin, hsched, hok, hpos, hcut⟩ := h
  have hfin' : backend.dget D go!"meta" go!"finishedCompactRev" = mvcc.recBytes r.fin := hfin
  have hsched' : backend.dget D go!"meta" go!"scheduledCompactRev" = mvcc.recBytes r.sched := hsched
  have hfv : backend.fkVals D = (mvcc.recBytes r.fin, mvcc.recBytes r.sched) := by
    unfold backend.fkVals; rw [hfin', hsched']
  have hwf : backend.fkWfD d'.P D := by
    intro n k v hk' hv
    obtain ⟨rfl, hk'⟩ := hk'
    show mvcc.metaRevVal v
    rcases hk' with rfl | rfl
    · rw [hsched'] at hv; exact mvcc.recBytes_metaRevVal hpos.2 hv
    · rw [hfin'] at hv; exact mvcc.recBytes_metaRevVal hpos.1 hv
  iintro ⟨Hv, Hfk⟩
  icases backend.fkCl_open d'.γB d'.P D $$ Hfk with ⟨Ho, Hw, #Hop⟩
  rw [backend.fkWInit_of_wf hwf, hfv]
  unfold mvcc.restoreImageM
  simp only [hcm, ↓reduceIte]
  iexists ents
  isplitl [Hv]
  · simp only [mvcc.kbViewC, mvcc.bkViewC]
    iexists _
    iframe Hv
    ipureintro; exact mvcc.keyView_of_dget hbr hk
  isplitl [Ho]
  · unfold mvcc.kbRecs
    by_cases hr : r = mvcc.CmpRecs.empty
    · have habs : backend.fkAbsD D := by
        intro n k hk'
        obtain ⟨rfl, hk'⟩ := hk'
        subst hr
        rcases hk' with rfl | rfl
        · rw [hsched']; rfl
        · rw [hfin']; rfl
      simp only [hr, ↓reduceIte]
      rw [mvcc.kbNoCmp_some, backend.fkInit_of_abs habs]
      unfold mvcc.bkNoCmp
      iexact Ho
    · simp only [hr, ↓reduceIte]
      iexists _
      iframe Ho
      unfold backend.fkOpenD backend.fkVD
      iunfold backend.fkOpen at Hop
      icases Hop with ⟨%w, Hop⟩
      iexists w
      iunfold backend.fkVR at Hop
      iexact Hop
  isplitl [Hw]
  · unfold backend.fkVM backend.fkVD
    iunfold backend.fkV at Hw
    icases Hw with ⟨%n, %v, Hw⟩
    iexists n, v
    iexact Hw
  ipureintro; exact ⟨hok, hpos, hcut⟩

/-- **Off, the image `Restore` takes, from the backend's open** (what the walk built inline until
stage B): the whole bucket of the restored log and the no-compaction token. -/
theorem mvcc.restoreImageM_of_openOff (d' : mvcc.KBReal) (γb : GName) (L : mvcc.Log)
    (r : mvcc.CmpRecs) (D : backend.Data) (hcm : d'.cm = false) (hbr : mvcc.bridgeParams d'.P)
    (h : mvcc.keyImageM false L r D) :
    backend.bViewC d'.γB 1 (backend.vData d'.P (D, ⟨∅, W64 0⟩)) true ∗ backend.fkCl d'.γB d'.P D ⊢
      mvcc.restoreImageM (GF := GF) d' γb L r := by
  obtain ⟨hkI, hr⟩ := (mvcc.keyImageM_off L r D).1 h
  iintro ⟨Hv, Hfk⟩
  unfold mvcc.restoreImageM
  simp only [hcm, Bool.false_eq_true, ↓reduceIte]
  isplitl [Hv]
  · simp only [mvcc.kbViewC, mvcc.bkViewC]
    iexists _
    iframe Hv
    ipureintro; exact mvcc.keyView_of_keyImage hbr hkI
  isplitl [Hfk]
  · rw [mvcc.kbNoCmp_some]
    iapply mvcc.bkNoCmp_of_fkCl d'.γB _ (mvcc.keyImage_noCmp hkI) $$ Hfk
  ipureintro; exact hr

/-- **The image `Restore` takes, from the backend's open, in either mode.** -/
theorem mvcc.restoreImageM_of_open (d' : mvcc.KBReal) (γb : GName) (L : mvcc.Log)
    (r : mvcc.CmpRecs) (D : backend.Data) (hbr : mvcc.bridgeParams d'.P)
    (h : mvcc.keyImageM d'.cm L r D) :
    backend.bViewC d'.γB 1 (backend.vData d'.P (D, ⟨∅, W64 0⟩)) true ∗ backend.fkCl d'.γB d'.P D ⊢
      mvcc.restoreImageM (GF := GF) d' γb L r := by
  cases hcm : d'.cm
  · rw [hcm] at h; exact mvcc.restoreImageM_of_openOff d' γb L r D hcm hbr h
  · rw [hcm] at h; exact mvcc.restoreImageM_of_openOn d' γb L r D hcm hbr h

end laws

end EtcdGrove
end Perennial
