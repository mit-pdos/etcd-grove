/-
**`store.Restore` in either mode: the pieces** (M2's item 15, step A2; `notes/m2-storage-plan.md`,
"Step 2: restore in compaction mode"). What `store.Restore`'s proof uses of the store's right to
close by the mode (`restoreRightM`): the scheduler's stop and the fields' quarter back.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.M2StorageDraftRestore
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

/-- **What `store.Restore` takes of the store's right, opened, in either mode**: at the current
objects `o`, the stop channel and its close, the scheduler's stop token and the jobs' queue (what
`Scheduler.Stop` takes), the closer's quarter of the fields once the scheduler is done (on, the
closer's eighth and the jobs' reclaimed: `fieldShare_reclaim`), and the compaction revision's part
the right holds: off, the frozen revision at `-1`; on, half the authority at `c`. -/
theorem restoreRightM_open (s : Loc) (γ : StoreNames) (c : Int) :
    restoreRightM (GF := GF) s γ c ⊢ ∃ o : StoreObjs,
      isStopChan o.sstop ∗ stopCloser o.sstop ∗ schedule.schedStopTok γ.sch ∗ compactQueue γ c ∗
      (schedule.schedDone γ.sch -∗ £ 1 ={⊤}=∗ fieldShareAt s γ (1 : Qp).half.half o) ∗
      (if kbCmpM γ.kb then crevUB γ.idx (1 : Qp).half c else iprop(crevFrozen γ ∗ ⌜c = -1⌝)) := by
  iintro H
  by_cases hm : kbCmpM γ.kb
  · icases (restoreRightM_on s γ c hm).1 $$ H with H
    icases (compactRightR_iff s γ c).1 $$ H with ⟨Hcu, Hq, %o, ⟨Hf, #Hsc, Hstc, Htok⟩, #HsR⟩
    iexists o
    simp only [hm, ↓reduceIte]
    iframe Hsc Hstc Htok Hq Hcu
    iintro Hd Hlc
    iapply fieldShare_reclaim s γ o $$ Hf HsR Hd Hlc
  · icases (restoreRightM_off s γ c hm).1 $$ H with ⟨H, #Hfrz, %Hc⟩
    subst Hc
    iunfold storeCloser at H
    icases H with ⟨%o, Hf, #Hsc, Hstc, Htok, Hq⟩
    iexists o
    simp only [hm, ↓reduceIte]
    iframe Hsc Hstc Htok Hq Hfrz
    iintro - -; imodintro; iexact Hf

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
        crevLb γ.idx c2 := by
  iintro H1 H2 Hh
  iunfold restoreHeld at Hh
  iNamed Hh
  imod crevUB_raise γ.idx c c2 h $$ H1 H2 Hcrev with ⟨H1, H2, H3, #Hlb⟩
  imodintro
  iframe H1 H2 Hlb
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

end laws

end mvcc
end EtcdGrove
end Perennial
