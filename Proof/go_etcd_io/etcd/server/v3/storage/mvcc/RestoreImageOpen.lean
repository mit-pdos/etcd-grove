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
keys holding the records' bytes, the records of `L` and past revision `0` (`recsPos`) and
`r.crev` safe for readers (`NoDelPutAt`). -/
def mvcc.keyImageM (cm : Bool) (L : mvcc.Log) (r : mvcc.CmpRecs) (D : backend.Data) : Prop :=
  if cm then ∃ ents : List mvcc.KvEnt,
      (∀ k, backend.dget D mvcc.keyName k = (mvcc.bucketOfEnts ents).lookup k) ∧
      backend.dget D go_etcd_io.etcd.server.v3.storage.schema.metaName mvcc.finKeyBytes =
        mvcc.recBytes r.fin ∧
      backend.dget D go_etcd_io.etcd.server.v3.storage.schema.metaName mvcc.schedKeyBytes =
        mvcc.recBytes r.sched ∧
      mvcc.recsOk L r ∧ mvcc.recsPos r ∧ mvcc.entsCutAt L r.crev ents ∧
      mvcc.NoDelPutAt L r.crev
  else mvcc.keyImage L D ∧ r = mvcc.CmpRecs.empty

theorem mvcc.keyImageM_off (L : mvcc.Log) (r : mvcc.CmpRecs) (D : backend.Data) :
    mvcc.keyImageM false L r D ↔ mvcc.keyImage L D ∧ r = mvcc.CmpRecs.empty := by
  unfold mvcc.keyImageM; simp

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [backend_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

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
  obtain ⟨ents, hk, hfin, hsched, hok, hpos, hcut, hnd⟩ := h
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
  ipureintro; exact ⟨hok, hpos, hcut, hnd⟩

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
