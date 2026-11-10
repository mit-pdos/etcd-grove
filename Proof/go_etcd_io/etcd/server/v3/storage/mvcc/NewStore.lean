/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.NewStore
public import Spec.go_uber_org.zap.NewNop
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.newTreeIndex
public import Spec.go_etcd_io.etcd.pkg.v3.schedule.NewFIFOScheduler
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.NewHashStorage
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.UnsafeCreateMetaBucket
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__restore
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RestoreNC
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.CmpSteps

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [go_etcd_io.etcd.cache.v3.Assumptions]

omit package_sem in
/-- **The fresh store's cut** (M3, 2026-11-06): at the initial log, nothing in the bucket, nothing
deleted, no record and no job, the tracked compaction's pure fact holds (no entry at all). -/
theorem mvcc.cmpOk_fresh :
    mvcc.snap.cmpOk [[], []] (∅ : mvcc.Bucket) (∅ : backend.VData) ⟨none, none⟩
      ((-1 : Int), (⟨W64 0, W64 0⟩ : mvcc.Rev)) := by
  have hle : mvcc.logEnts [[], []] 0 2 = [] := by
    simp [mvcc.logEnts, mvcc.entsOfRev, List.range']
  have hc : (⟨none, none⟩ : mvcc.CmpRecs).crev = -1 := mvcc.CmpRecs.crev_empty
  have hf : (⟨none, none⟩ : mvcc.CmpRecs).finRev = -1 := mvcc.CmpRecs.finRev_empty
  refine ⟨[], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · exact List.nil_sublist _
    · intro e he; simp [hle] at he
    · intro e₁ he₁; simp [hle] at he₁
  · intro k
    simp [mvcc.snap.physLookup, mvcc.bucketOfEnts]
    rfl
  · simp [mvcc.recsOk]
  · simp [mvcc.recsPos]
  · intro k h; simp at h
  · intro e he; simp [hle] at he
  · exact Int.le_refl _
  · simp [hc]
  · simp [hf]

/-- **The fresh store's tracked compaction** (M3, 2026-11-06; in place of `cmpTrack_new_M1` at
`NewStore`): the no-compaction token's values' halves at none (`kbNoCmp_split`, from the open's
exact `fkCl`) and the store's fresh ghost state (the records' compaction revision's half, the job
cursor's half and the lower bounds' authority, all at `-1`); the values given back for a store that
does not compact (its writer's loan keeps the whole token). -/
theorem mvcc.cmpTrack_fresh (γ : mvcc.StoreNames) :
    mvcc.kbVals (GF := GF) γ.kb (none, none) ∅ ∗ ghostVar γ.rcv (1 : Qp).half (-1 : Int) ∗
      ghostVar γ.jc (1 : Qp).half ((-1 : Int), (⟨W64 0, W64 0⟩ : mvcc.Rev)) ∗
      monoNatAuthOwn γ.rcl 1 (mvcc.crevN (-1)) ⊢
      mvcc.cmpTrack γ [[], []] ∅ ⟨none, none⟩ ∗
        (⌜¬ mvcc.kbCmpM γ.kb⌝ -∗ mvcc.kbVals γ.kb (none, none) ∅) := by
  have hc : (⟨none, none⟩ : mvcc.CmpRecs).crev = -1 := mvcc.CmpRecs.crev_empty
  unfold mvcc.cmpTrack mvcc.kbCmpM
  cases hk : γ.kb with
  | none =>
    simp only
    iintro -
    isplitl
    · itrivial
    · iintro %h; exact absurd trivial h
  | some d =>
    cases hcm : d.cm with
    | false =>
      simp only [hcm, Bool.false_eq_true, ↓reduceIte]
      iintro ⟨Hv, -, -, -⟩
      isplitr
      · itrivial
      · iintro -; iexact Hv
    | true =>
      simp only [hcm, ↓reduceIte, mvcc.kbVals]
      iintro ⟨⟨Hf, Hd⟩, Hr, Hj, Hl⟩
      rw [hc]
      isplitl
      · iframe Hr Hl
        isplitl [Hf]
        · simp only [mvcc.recBytes, Option.map_none]; iexact Hf
        iexists ∅, ((-1 : Int), (⟨W64 0, W64 0⟩ : mvcc.Rev))
        iframe Hd Hj
        ipureintro; exact mvcc.cmpOk_fresh
      · iintro %h; exact absurd trivial h

/-- One of the backend's reader tokens the store takes (`nReaders`, the backend's stock), and the
rest back from it. -/
theorem mvcc.slot_take (Q : IProp GF) :
    ([∗list] _x ∈ List.replicate mvcc.nReaders (), Q) ⊢
      Q ∗ (Q -∗ [∗list] _x ∈ List.replicate mvcc.nReaders (), Q) := by
  obtain ⟨m, hm⟩ : ∃ m, mvcc.nReaders = m + 1 := ⟨mvcc.nReaders - 1, by rw [mvcc.nReaders_val]⟩
  rw [hm, List.replicate_succ]
  iintro H
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H1, Hs⟩
  iframe H1
  iintro H1
  iapply BigSepL.bigSepL_cons.2
  iframe H1 Hs

/-- The store's reader handles (of a store that may be compacted) from the reader slots of its
two locks and the readers' tickets (D22 receiver epochs, S4: the index's slots are in the readers'
pool; S5a: so are the backend's reader tokens). -/
theorem mvcc.storeReaders_of_slots (s : Loc) (γ : mvcc.StoreNames) : ∀ (n : Nat),
    ([∗list] _x ∈ List.replicate n (), sync.ownRWMutex (mvcc.muAddr s) (mvcc.muInv (GF := GF) s γ)) ∗
      ([∗list] _x ∈ List.replicate n (), sync.ownRWMutex (mvcc.revMuAddr s) (mvcc.revMuInv s γ)) ∗
      ([∗list] _x ∈ List.replicate n (), ownToks γ.tk 1) ⊢
      [∗list] _x ∈ List.replicate n (), mvcc.storeReaderC s γ
  | 0 => by rw [List.replicate_zero]; iintro _; iapply BigSepL.bigSepL_nil_intro; iempintro
  | n + 1 => by
    rw [List.replicate_succ]
    iintro ⟨Hm, Hr, Hk⟩
    icases BigSepL.bigSepL_cons.1 $$ Hm with ⟨Hm1, Hm⟩
    icases BigSepL.bigSepL_cons.1 $$ Hr with ⟨Hr1, Hr⟩
    icases BigSepL.bigSepL_cons.1 $$ Hk with ⟨Hk1, Hk⟩
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hm1 Hr1 Hk1]
    · iunfold mvcc.storeReaderC
      simp only [named]
      iframe Hm1 Hr1 Hk1
    · iapply mvcc.storeReaders_of_slots s γ n
      iframe Hm Hr Hk

/-- `n` tokens, one by one. -/
theorem mvcc.ownToks_ones (γ : GName) : ∀ (n : Nat),
    ownToks (GF := GF) γ n ⊢ [∗list] _x ∈ List.replicate n (), ownToks γ 1
  | 0 => by rw [List.replicate_zero]; iintro _; iapply BigSepL.bigSepL_nil_intro; iempintro
  | n + 1 => by
    rw [List.replicate_succ]
    iintro H
    icases (ownToks_add 1 n γ).1 $$ H with ⟨Hn, H1⟩
    iapply BigSepL.bigSepL_cons.2
    iframe H1
    iapply mvcc.ownToks_ones γ n
    iexact Hn

theorem mvcc.NewStore.wp_proof
    (hNop : zap.NewNop.spec (GF := GF) (hG := hG))
    (hNewIdx : mvcc.newTreeIndex.spec (GF := GF) (hG := hG))
    (hFifo : schedule.NewFIFOScheduler.spec (GF := GF) (hG := hG))
    (hHash : mvcc.NewHashStorage.spec (GF := GF) (hG := hG))
    (hMeta : schema.UnsafeCreateMetaBucket.spec (GF := GF) (hG := hG))
    (hRestore : mvcc.store.restore.spec (GF := GF) (hG := hG)) :
    mvcc.NewStore.spec (GF := GF) (hG := hG) := by
  -- B3 Prove (mvccfull's Freeze, 2026-11-10): `mvcc.NewStore.spec` is now over a backend holding an
  -- image (`restoreImageM`, the records `r`, the lessor's owner part lent, the resumed compaction).
  -- The proof of the fresh statement is at commit `ae30739dde` (this file): its batch session and
  -- `store.restore` call at `ns = false` carry over, with `NewStoreSess.lean`'s session contract, the
  -- registration fixed after `restore()` (`storeSess_fix`) and `store.Restore`'s image vocabulary
  -- (`RestoreVocab.lean`), as in `notes/mvccfull-proof-plan.md`'s "Draft: B3's internal chain".
  sorry

end proof

end EtcdGrove
end Perennial
