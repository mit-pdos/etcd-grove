/-
**`store.Restore` in either mode: the pieces** (M2's item 15, step A2; `notes/m2-storage-plan.md`,
"Step 2: restore in compaction mode"). What `store.Restore`'s proof uses of the store's right to
close by the mode (`restoreRightM`): the scheduler's stop and the fields' quarter back.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RestoreVocab
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RestoreMoves

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **The new index's lock at the restored compaction level** (`newTreeIndex` gives the lock's ghost
part and the compactor's token at `-1`): the compactor's state raised to `c`, with the compaction
revision's lower bound there and a committed log past it. -/
theorem idxLockG_raise (γ : IdxNames) (n : Nat) (c : Int) (log₀ : Log) (hl : c < log₀.length) :
    ⊢ idxLockG (GF := GF) γ n -∗ idxCompactor γ (-1) -∗ crevLb γ c -∗ monoListLbOwn γ.log log₀ ==∗
      idxLockGAt γ n c ∗ idxCompactor γ c := by
  iintro Hg Hc #Hlb #Hll
  iunfold idxLockG at Hg
  icases Hg with ⟨Hn, -, -, Hcmp⟩
  iunfold idxCmpOwn at Hcmp
  icases Hcmp with ⟨%cc, %P, Hg, -⟩
  iunfold idxCompactor at Hc
  imod ghostVar_update_halves (c, ([] : List Loc)) γ.cmp _ _ $$ Hg Hc with ⟨Hg, Hc⟩
  imodintro
  iunfold idxCompactor
  iframe Hc
  iunfold idxLockGAt
  iframe Hn Hlb
  isplitl []
  · iexists log₀
    iframe Hll
    ipureintro; exact hl
  iunfold idxCmpOwn
  iexists c, []
  iframe Hg
  ipureintro
  exact ⟨Int.le_refl c, by simp, by simp⟩

/-- **The compaction revision raised during the restore** (`store.Restore` holds all of its authority:
the right's half, `s.mu`'s quarter and, after the takeover, `s.revMu`'s quarter, in `restoreHeld`). -/
theorem restoreHeld_raise (γ : StoreNames) (L' : Log) (c c2 : Int) (h : c ≤ c2) :
    ⊢ crevUB (GF := GF) γ.idx (1 : Qp).half c -∗ crevUB γ.idx (1 : Qp).half.half c -∗
      restoreHeld γ L' c ==∗
      crevUB γ.idx (1 : Qp).half c2 ∗ crevUB γ.idx (1 : Qp).half.half c2 ∗ restoreHeld γ L' c2 ∗
        crevLb γ.idx c2 ∗ monoListLbOwn γ.idx.log L' := by
  iintro H1 H2 Hh
  iunfold restoreHeld at Hh
  iNamed Hh
  imod crevUB_raise γ.idx c c2 h $$ H1 H2 Hcrev with ⟨H1, H2, H3, #Hlb⟩
  imodintro
  iframe H1 H2 Hlb Hllb
  iunfold restoreHeld
  simp only [named]
  iframe Hclog Hlog Htoks H3 Hlrd Hhist
  iframe #

/-- **A cut image's bucket is a thin bucket of the log** (`entsCutAt`): every key it has is the
log's, and every key of the log it lacks is deletable at the cut's revision. -/
theorem bucketOfEnts_cut (L : Log) (hb : LogB L) (c : Int) (ents : List KvEnt)
    (hcut : entsCutAt L c ents) :
    (∀ k v, (bucketOfEnts ents).lookup k = some v → (bucketMap L).lookup k = some v) ∧
    (∀ k v, (bucketMap L).lookup k = some v → (bucketOfEnts ents).lookup k = none → KeyDel L c k) := by
  have hfull := bucketOfEnts_lookup_iff L hb (List.Sublist.refl (logEnts L 0 L.length))
  rw [bucketOfEnts_logEnts] at hfull
  refine ⟨fun k v h => ?_, fun k v h hn => ?_⟩
  · have hm := (bucketOfEnts_lookup_iff L hb hcut.1 k v).1 h
    exact (hfull k v).2 ((hcut.1.map KvEnt.pair).subset hm)
  · have hm := (hfull k v).1 h
    obtain ⟨e, he, hpe⟩ := List.mem_map.1 hm
    by_cases hin : e ∈ ents
    · exfalso
      have := (bucketOfEnts_lookup_iff L hb hcut.1 k v).2 (List.mem_map.2 ⟨e, hin, hpe⟩)
      change (bucketOfEnts ents).lookup k = some v at this
      rw [hn] at this; cases this
    · have hk : k = revBytes e.rev e.tomb := by
        have := congrArg Prod.fst hpe; simp [KvEnt.pair] at this; exact this.symm
      rw [hk]
      exact hcut.2.1 e he hin

/-- **The view of a cut image is a thin view of the log** (`bucketViewL`): its missing keys are
deletable, at the cut's revision `c` (a lower bound of the compaction revision) of the certified
log. -/
theorem bucketViewL_ofCut (γ : StoreNames) (q : Qp) (L : Log) (hb : LogB L) (c : Int)
    (ents : List KvEnt) (hcut : entsCutAt L c ents) (hc : -1 ≤ c) :
    bucketView (GF := GF) γ q (bucketOfEnts ents) ∗ crevLb γ.idx c ∗ idxCert γ.idx L ∗
      ⌜kbCmpM γ.kb⌝ ⊢ bucketViewL γ q L := by
  obtain ⟨h1, h2⟩ := bucketOfEnts_cut L hb c ents hcut
  iintro ⟨Hv, #Hlb, #Hc, %Hm⟩
  iunfold bucketViewL
  iexists bucketOfEnts ents
  iframe Hv
  iunfold bucketLog
  isplitl
  · iunfold snapThin
    isplitl
    · ipureintro; exact h1
    iintro !> %k %v %Hkv
    iunfold delKey
    iexists c, L
    iframe Hlb Hc
    ipureintro
    exact ⟨hc, h2 k v Hkv.1 Hkv.2⟩
  · ipureintro; intro hn; exact absurd Hm hn

/-! ## The pieces of the compaction-mode proof -/

theorem crevLb_to (γ : StoreNames) (p : PhysNames) (c : Int) :
    crevLb (GF := GF) γ.idx c ⊢ crevLb (γ.withPhys p).idx c := .rfl

/-- `bucketViewL_ofCut` at new physical names, the revision's bound and the certificate the
logical names' (`crevLb_withPhys`, `idxCert_withPhys`). -/
theorem bucketViewL_ofCutW (γ : StoreNames) (p : PhysNames) (q : Qp) (L : Log) (hb : LogB L)
    (c : Int) (ents : List KvEnt) (hcut : entsCutAt L c ents) (hc : -1 ≤ c) :
    bucketView (GF := GF) (γ.withPhys p) q (bucketOfEnts ents) ∗ crevLb γ.idx c ∗ idxCert γ.idx L ∗
      ⌜kbCmpM (γ.withPhys p).kb⌝ ⊢ bucketViewL (γ.withPhys p) q L :=
  bucketViewL_ofCut (γ.withPhys p) q L hb c ents hcut hc

theorem W64_sint' (x : w64) : W64 (sint.Z x) = x := by simp [W64, sint.Z]

/-- **What `store.Restore` takes of the store's right in compaction mode, opened**: at the current
objects `o`, the stop channel and its close, the scheduler's stop token and the jobs' queue (what
`Scheduler.Stop` takes), the closer's eighth of the fields (which reads `s.stopc` and `s.fifoSched`
before the stop), the jobs' share (reclaimed after it: `storeStopR_reclaim`), and half the
compaction revision's authority at `c`. -/
theorem restoreRightM_openOn (s : Loc) (γ : StoreNames) (c : Int) (h : kbCmpM γ.kb) :
    restoreRightM (GF := GF) s γ c ⊢ ∃ o : StoreObjs,
      isStopChan o.sstop ∗ stopCloser o.sstop ∗ schedule.schedStopTok γ.sch ∗ compactQueue γ c ∗
      fieldShareAt s γ q8 o ∗ storeStopR s γ o ∗ crevUB γ.idx (1 : Qp).half c := by
  iintro H
  icases (restoreRightM_on s γ c h).1 $$ H with H
  icases (compactRightR_iff s γ c).1 $$ H with ⟨Hcu, Hq, %o, ⟨Hf, #Hsc, Hstc, Htok⟩, #HsR⟩
  iexists o
  iframe Hsc Hstc Htok Hq Hcu Hf HsR

/-- A compaction revision below `-1` is `-1`'s (`crevN`). -/
theorem crevUB_max (γ : IdxNames) (q : Qp) (c : Int) :
    crevUB (GF := GF) γ q c ⊣⊢ crevUB γ q (max c (-1)) := by
  unfold crevUB
  rw [show crevN c = crevN (max c (-1)) by unfold crevN; omega]
  exact .rfl

/-- `crevUB_agree`, the two parts kept. -/
theorem crevUB_agree' (γ : IdxNames) (q1 q2 : Qp) (c1 c2 : Int) (h1 : -1 ≤ c1) (h2 : -1 ≤ c2) :
    crevUB (GF := GF) γ q1 c1 ∗ crevUB γ q2 c2 ⊢ crevUB γ q1 c1 ∗ crevUB γ q2 c2 ∗ ⌜c1 = c2⌝ := by
  unfold crevUB
  iintro ⟨H1, H2⟩
  ihave %h := monoNatAuthOwn_agree γ.crev q1 q2 _ _ $$ H1 H2
  iframe H1 H2
  ipureintro
  have := h.2
  unfold crevN at this
  omega

/-- **The last job's token, after the scheduler's stop** (its post: the last name's saved `P`,
later): the queue's saved `Q` is `P`, and with the queue's `R` it gives the token. -/
theorem compactQueue_stopped (γ : StoreNames) (c : Int) (Ps : List GName) (p : GName)
    (Q R : IProp GF) :
    ⊢ (match (Ps ++ [p]).getLast? with
        | none => iprop(True)
        | some p => iprop(∃ P : IProp GF, schedule.savedProp p P ∗ ▷ P)) -∗
      schedule.savedProp p Q -∗ R -∗ (Q ∗ R -∗ compactTok γ c) -∗ £ 1 ={⊤}=∗ compactTok γ c := by
  rw [List.getLast?_concat]
  iintro ⟨%P, #HP, HPl⟩ #HQ HR Hw Hlc
  iunfold schedule.savedProp at HP HQ
  ihave #Heq := saved_prop_agree p DFrac.discard DFrac.discard P Q $$ HP HQ
  ihave HQl : ▷ Q $$ [HPl]
  · inext
    ihave Hiff := internalEq_iff _ _ $$ Heq
    icases Hiff with ⟨Hiff, -⟩
    iapply Hiff $$ HPl
  imod (lc_fupd_elim_later (E := ⊤) (P := Q)) $$ Hlc HQl with HQ'
  imodintro
  iapply Hw
  iframe HQ' HR

/-- The `RWMutex` admits at least three readers: the restored store's pool, its writer and its
compaction job. -/
theorem nReaders_ge_3 : 3 ≤ nReaders := by
  rw [nReaders_val]; decide

/-- Three readers out of the pool. -/
theorem rep_take3 (P : IProp GF) :
    ([∗list] _x ∈ List.replicate nReaders (), P) ⊢
      P ∗ P ∗ P ∗ ([∗list] _x ∈ List.replicate (nReaders - 3) (), P) := by
  obtain ⟨m, hm⟩ : ∃ m, nReaders = m + 3 := ⟨nReaders - 3, by have := nReaders_ge_3; omega⟩
  rw [hm, show m + 3 - 3 = m by omega]
  simp only [List.replicate_succ]
  iintro H
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H1, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H2, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H3, H⟩
  iframe H1 H2 H3 H

/-- One reader back with the pool's (`nReaders - 1 - 1`: a compacting store's old readers). -/
theorem rep_back3 (P : IProp GF) :
    P ∗ ([∗list] _x ∈ List.replicate (nReaders - 3) (), P) ⊢
      [∗list] _x ∈ List.replicate (nReaders - 1 - 1) (), P := by
  obtain ⟨m, hm⟩ : ∃ m, nReaders = m + 3 := ⟨nReaders - 3, by have := nReaders_ge_3; omega⟩
  rw [hm, show m + 3 - 3 = m by omega, show m + 3 - 1 - 1 = m + 1 by omega, List.replicate_succ]
  iintro ⟨H1, H⟩
  iapply BigSepL.bigSepL_cons.2
  iframe H1 H

/-- On, the image is the cut entries' view with the records. -/
theorem restoreImageM_on (d' : KBReal) (γb' : GName) (L : Log) (r : CmpRecs) (h : d'.cm = true) :
    restoreImageM (GF := GF) d' γb' L r ⊣⊢
      ∃ ents : List KvEnt, kbViewC (some d') γb' 1 (bucketOfEnts ents) ∗
        kbRecs (some d') γb' r ∗ backend.fkVM d'.γB true ∗
        ⌜recsOk L r ∧ recsPos r ∧ entsCutAt L r.crev ents ∧ NoDelPutAt L r.crev⌝ := by
  unfold restoreImageM; simp only [h, ↓reduceIte]; exact .rfl

theorem kbSRM_on (kb : Option KBReal) (h : kbCmpM kb) :
    kbSRM (GF := GF) kb ⊣⊢ kbSR kb := by
  unfold kbSRM; simp only [h, ↓reduceIte]; exact .rfl

/-- On, a resumed compaction's lent hook is the new backend's unset one. -/
theorem resumeHookM_yes (d' : KBReal) (r : CmpRecs) (h : d'.cm = true) (hr : r.resumes = true) :
    resumeHookM (GF := GF) d' r ⊣⊢ kbHookNil (some d') := by
  unfold resumeHookM; simp only [h, hr, and_self, ↓reduceIte]; exact .rfl

/-- A compacting store's writer keeps the pool's two retired tokens and the job's. -/
theorem writerOwn_on (γ : StoreNames) (h : nJobRd γ.kb = 1) :
    writerOwn (GF := GF) γ ⊣⊢ iprop(storeRT γ ∗ retiredAt γ 3) := by
  unfold writerOwn; rw [h]; exact .rfl

theorem crevPermAt_withPhys (γ : StoreNames) (p : PhysNames) (c : Int) :
    crevPermAt (GF := GF) (γ.withPhys p) c = crevPermAt γ c := rfl

theorem lagTok_withPhys (γ : StoreNames) (p : PhysNames) (c cp : Int) :
    lagTok (GF := GF) (γ.withPhys p) c cp = lagTok γ c cp := rfl

/-- The lag's token and what `Restore` keeps when there is no lag make the watchable store's
quarter. -/
theorem lagTok_rest (γ : StoreNames) (c cp : Int) :
    lagTok (GF := GF) γ c cp ∗ (if cp = c then ghostVar γ.wsd (1 : Qp).half.half () else iprop(True))
      ⊢ ghostVar γ.wsd (1 : Qp).half.half () := by
  unfold lagTok
  by_cases h : cp = c
  · simp only [h, ↓reduceIte]; iintro ⟨-, H⟩; iexact H
  · simp only [h, ↓reduceIte]; iintro ⟨H, -⟩; iexact H

/-- The finished record is `-1` or a revision, at most the restored one. -/
theorem CmpRecs.finRev_bounds (L : Log) (r : CmpRecs) (h : recsOk L r) :
    -1 ≤ r.finRev ∧ r.finRev ≤ r.crev := by
  have hf : -1 ≤ r.finRev := by
    unfold CmpRecs.finRev
    cases hfin : r.fin with
    | none => simp
    | some x => have := (h.1 x hfin).1; simp; omega
  refine ⟨hf, ?_⟩
  unfold CmpRecs.crev CmpRecs.resumes
  split
  · rename_i hr; simp only [decide_eq_true_eq] at hr; omega
  · omega

/-- A resumed compaction is past the finished one, at the scheduled record. -/
theorem CmpRecs.resumes_lt (r : CmpRecs) (h : r.resumes = true) :
    r.finRev < r.crev ∧ r.crev = r.schedRev := by
  have h' := h
  unfold CmpRecs.resumes at h'
  simp only [decide_eq_true_eq] at h'
  unfold CmpRecs.crev
  simp only [h, ↓reduceIte]
  exact ⟨h'.2, trivial⟩

/-- Without a resume, the restored revision is the finished one. -/
theorem CmpRecs.crev_noResume (r : CmpRecs) (h : r.resumes = false) : r.crev = r.finRev := by
  unfold CmpRecs.crev; simp [h]

end laws

end mvcc
end EtcdGrove
end Perennial
