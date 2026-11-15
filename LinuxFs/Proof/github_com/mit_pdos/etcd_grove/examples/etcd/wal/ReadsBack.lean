/-
Lean-first (no Rocq counterpart).

# The tester's histories read back where `ReadAll` succeeds (W4c U5, tenth session)

`member.restart` takes `tReadsBackOk` of the member's WAL state (`RestartOk.lean`): wherever `ReadAll`
succeeds on it, the history reads back (`walReadsBack`). Its strong form, `walReadsBack` of every image,
is false (eighth session: a received snapshot's record, then its `Save` torn). This file gives the
invariant that implies the weak form for every image at the candidate's mark, and that every operation
keeps:

* **`TDisc σ B σ'`, the raft discipline of the operations since the last restart** (`B`, folded from the
  restart's read `σ` to `σ'`): a `Save` whose fold succeeds with the commit at most the last index, the
  commit not going down, every entry above the old commit (`tDSave`); an own snapshot at or below the
  commit; a received one above the last index immediately followed by its `Save` (commit at least the
  record's index, entries above it).
* **`tSimAt H n σ`**: the history is `A ++ B`, `A` (at most the mark `n` long) the image the last restart
  read, whose restart read (its guide re-marked by its own commit, `SimFold.gFold`) is `σA`, and `B` is
  disciplined from `σA` to `σ` (`σ`: the member's raft-like fields' view). **`tSim H n`**: that, or such a
  history followed by a received snapshot's record whose `Save` has not come yet.

Results: `tSim_readsBack` (every image at the mark: `ReadAll`'s success gives `walReadsBack`, through
`SimFold.gFold_remask` and `gFold_readsBack`, the torn `Save` after a received record failing `ReadAll`,
`SimFold.readAll_bad`), `tSim_restart` (an image `ReadAll` succeeds on starts a new `tSimAt` at its own
length, at its `walRead`), and the steps (`tSimAt_save`, `_own`, `_recv`, `tSim_snapT`, `_mark`).
-/
module

public import LinuxFs.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.SimFold

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open go_etcd_io.raft.v3 WalEnc

section pure
variable [GooseExts]

/-- **A disciplined `Save`** from the fold `σ1` to `σ2`. -/
def tDSave (σ1 : StorContents) (h : HardStateM) (es : List EntryM) (σ2 : StorContents) : Prop :=
  walFoldChkFrom σ1 [.save h es] = some σ2 ∧ σ2.commit ≤ σ2.last ∧ σ1.commit ≤ σ2.commit ∧
    ∀ e ∈ es, σ1.commit < uint.nat e.Index'

/-- **The raft discipline of the operations since a restart** (see the file header). -/
inductive TDisc : StorContents → WalHist → StorContents → Prop
  | nil (σ : StorContents) : TDisc σ [] σ
  | save {σ σ1 σ2 : StorContents} {B : WalHist} {h : HardStateM} {es : List EntryM} :
      TDisc σ B σ1 → tDSave σ1 h es σ2 → TDisc σ (B ++ [.save h es]) σ2
  | own {σ σ1 : StorContents} {B : WalHist} {m : SnapshotMetadataM} :
      TDisc σ B σ1 → uint.nat m.Index' ≤ σ1.commit → TDisc σ (B ++ [.snap m]) (walSaveSnap σ1 m)
  | recv {σ σ1 σ2 : StorContents} {B : WalHist} {m : SnapshotMetadataM} {h : HardStateM}
      {es : List EntryM} :
      TDisc σ B σ1 → σ1.last < uint.nat m.Index' → tDSave (walSaveSnap σ1 m) h es σ2 →
      uint.nat m.Index' ≤ σ2.commit → (∀ e ∈ es, uint.nat m.Index' < uint.nat e.Index') →
      TDisc σ (B ++ [.snap m, .save h es]) σ2

/-- The restart's read of `A`, as its re-marked guide. -/
def tRestartG (A : WalHist) : List (WalOp × Bool) :=
  remask (uint.nat (walLastHS A).Commit') (A.map (fun o => (o, true)))

/-- **The history since the last restart is disciplined**, ending at `σ` (see the file header). -/
def tSimAt (H : WalHist) (n : Nat) (σ : StorContents) : Prop :=
  ∃ A B σA, H = A ++ B ∧ A.length ≤ n ∧ gFold walFresh (tRestartG A) = some σA ∧ TDisc σA B σ

/-- **`tSimAt`, or such a history followed by a received snapshot's record** whose `Save` has not come. -/
def tSim (H : WalHist) (n : Nat) : Prop :=
  (∃ σ, tSimAt H n σ) ∨
    ∃ H0 σ m, H = H0 ++ [.snap m] ∧ tSimAt H0 n σ ∧ σ.last < uint.nat m.Index'

/-! ## Steps -/

theorem tSimAt_tSim {H : WalHist} {n : Nat} {σ : StorContents} (h : tSimAt H n σ) : tSim H n :=
  Or.inl ⟨σ, h⟩

theorem tSimAt_save {H : WalHist} {n : Nat} {σ σ2 : StorContents} {h : HardStateM} {es : List EntryM}
    (hs : tSimAt H n σ) (hd : tDSave σ h es σ2) : tSimAt (H ++ [.save h es]) n σ2 := by
  obtain ⟨A, B, σA, rfl, hA, hg, hD⟩ := hs
  exact ⟨A, B ++ [.save h es], σA, by simp, hA, hg, .save hD hd⟩

theorem tSimAt_own {H : WalHist} {n : Nat} {σ : StorContents} {m : SnapshotMetadataM}
    (hs : tSimAt H n σ) (hm : uint.nat m.Index' ≤ σ.commit) :
    tSimAt (H ++ [.snap m]) n (walSaveSnap σ m) := by
  obtain ⟨A, B, σA, rfl, hA, hg, hD⟩ := hs
  exact ⟨A, B ++ [.snap m], σA, by simp, hA, hg, .own hD hm⟩

theorem tSimAt_recv {H : WalHist} {n : Nat} {σ σ2 : StorContents} {m : SnapshotMetadataM}
    {h : HardStateM} {es : List EntryM} (hs : tSimAt H n σ) (hl : σ.last < uint.nat m.Index')
    (hd : tDSave (walSaveSnap σ m) h es σ2) (hc : uint.nat m.Index' ≤ σ2.commit)
    (hes : ∀ e ∈ es, uint.nat m.Index' < uint.nat e.Index') :
    tSimAt (H ++ [.snap m, .save h es]) n σ2 := by
  obtain ⟨A, B, σA, rfl, hA, hg, hD⟩ := hs
  exact ⟨A, B ++ [.snap m, .save h es], σA, by simp, hA, hg, .recv hD hl hd hc hes⟩

theorem tSim_snapT {H : WalHist} {n : Nat} {σ : StorContents} {m : SnapshotMetadataM}
    (hs : tSimAt H n σ) (hl : σ.last < uint.nat m.Index') : tSim (H ++ [.snap m]) n :=
  Or.inr ⟨H, σ, m, rfl, hs, hl⟩

theorem tSimAt_mark {H : WalHist} {n n' : Nat} {σ : StorContents} (hn : n ≤ n') (hs : tSimAt H n σ) :
    tSimAt H n' σ := by
  obtain ⟨A, B, σA, hH, hA, hg, hD⟩ := hs
  exact ⟨A, B, σA, hH, by omega, hg, hD⟩

theorem tSim_mark {H : WalHist} {n n' : Nat} (hn : n ≤ n') (hs : tSim H n) : tSim H n' := by
  rcases hs with ⟨σ, h⟩ | ⟨H0, σ, m, hH, h, hl⟩
  · exact Or.inl ⟨σ, tSimAt_mark hn h⟩
  · exact Or.inr ⟨H0, σ, m, hH, tSimAt_mark hn h, hl⟩

/-- The empty history (`Create`'s), at any mark. -/
theorem tSimAt_nil (n : Nat) : tSimAt [] n walFresh :=
  ⟨[], [], walFresh, rfl, Nat.zero_le _, rfl, .nil _⟩

/-! ## The discipline as a guide -/

theorem walSaveSnap_commit (σ : StorContents) (m : SnapshotMetadataM) :
    (walSaveSnap σ m).commit = σ.commit := by
  simp only [StorContents.commit, walSaveSnap_hs]

theorem gStep_save {σ1 σ2 : StorContents} {h : HardStateM} {es : List EntryM}
    (h1 : walFoldChkFrom σ1 [.save h es] = some σ2) (h2 : σ2.commit ≤ σ2.last) :
    gStep σ1 (.save h es, true) = some σ2 := by
  simp only [gStep, h1, if_pos h2]

theorem gStep_snap {σ : StorContents} {m : SnapshotMetadataM} (hok : gSnapOk m σ = true) (b : Bool) :
    gStep σ (.snap m, b) = some (if b then walSaveSnap σ m else σ) := by
  simp only [gStep, hok, ↓reduceIte]

theorem gFold_snoc (G : StorContents) (L : List (WalOp × Bool)) (x : WalOp × Bool) {G1 G2 : StorContents}
    (h1 : gFold G L = some G1) (h2 : gStep G1 x = some G2) : gFold G (L ++ [x]) = some G2 := by
  rw [gFold_append, h1, Option.bind_some]; simp only [gFold, h2, Option.bind_some]

/-- Every snapshot record the guide applies is at or below `c`. -/
def gKept (c : Nat) (L : List (WalOp × Bool)) : Prop :=
  ∀ m, (WalOpG.snap m, true) ∈ L → uint.nat m.Index' ≤ c

theorem gKept_mono {c c' : Nat} {L : List (WalOp × Bool)} (h : gKept c L) (hc : c ≤ c') : gKept c' L :=
  fun m hm => Nat.le_trans (h m hm) hc

theorem gKept_append {c : Nat} {L L' : List (WalOp × Bool)} (h : gKept c L) (h' : gKept c L') :
    gKept c (L ++ L') := by
  intro m hm
  rcases List.mem_append.1 hm with hm | hm
  · exact h m hm
  · exact h' m hm

theorem gKept_save {c : Nat} (h : HardStateM) (es : List EntryM) : gKept c [(WalOpG.save h es, true)] := by
  intro m hm; simp at hm

theorem gKept_false {c : Nat} (m : SnapshotMetadataM) : gKept c [(WalOpG.snap m, false)] := by
  intro m' hm; simp at hm

theorem gKept_snap {c : Nat} {m : SnapshotMetadataM} (h : uint.nat m.Index' ≤ c) :
    gKept c [(WalOpG.snap m, true)] := by
  intro m' hm; simp only [List.mem_singleton, Prod.mk.injEq, WalOpG.snap.injEq, and_true] at hm
  subst hm; exact h

/-- **The discipline is a guide** applying every record of `B`, all at or below the end's commit. -/
theorem TDisc.guide {σ σ' : StorContents} {B : WalHist} (hD : TDisc σ B σ') :
    ∃ LB, LB.map Prod.fst = B ∧ gFold σ LB = some σ' ∧ gKept σ'.commit LB ∧ σ.commit ≤ σ'.commit := by
  induction hD with
  | nil => exact ⟨[], rfl, rfl, fun m hm => by simp at hm, Nat.le_refl _⟩
  | @save σ1 σ2 B h es _ hd ih =>
    obtain ⟨LB, hm, hg, hk, hc⟩ := ih
    obtain ⟨h1, h2, h3, -⟩ := hd
    refine ⟨LB ++ [(.save h es, true)], by simp [hm], gFold_snoc _ _ _ hg (gStep_save h1 h2),
      gKept_append (gKept_mono hk h3) (gKept_save h es), by omega⟩
  | @own σ1 B m _ hm' ih =>
    obtain ⟨LB, hm, hg, hk, hc⟩ := ih
    have hok : gSnapOk m σ1 = true := by simp only [gSnapOk, decide_eq_true_eq]; omega
    refine ⟨LB ++ [(.snap m, true)], by simp [hm], gFold_snoc _ _ _ hg (gStep_snap hok true), ?_, ?_⟩
    · rw [walSaveSnap_commit]; exact gKept_append hk (gKept_snap hm')
    · rw [walSaveSnap_commit]; exact hc
  | @recv σ1 σ2 B m h es _ hl hd hmc _ ih =>
    obtain ⟨LB, hm, hg, hk, hc⟩ := ih
    obtain ⟨h1, h2, h3, -⟩ := hd
    rw [walSaveSnap_commit] at h3
    have hok : gSnapOk m σ1 = true := by simp only [gSnapOk, decide_eq_true_eq]; omega
    have hg1 := gFold_snoc _ _ _ hg (gStep_snap hok true)
    refine ⟨LB ++ [(.snap m, true)] ++ [(.save h es, true)], by simp [hm],
      gFold_snoc _ _ _ hg1 (by simpa using gStep_save h1 h2), ?_, by omega⟩
    exact gKept_append (gKept_append (gKept_mono hk (by omega)) (gKept_snap hmc)) (gKept_save h es)

/-! ## The images of a disciplined history -/

/-- **What an image of a disciplined `B` is**: a guide from `σ` (good), or a received snapshot's record
then its torn `Save` (bad). -/
def GoodImg (σ : StorContents) (I : WalHist) : Prop :=
  (∃ L σ'', L.map Prod.fst = I ∧ gFold σ L = some σ'' ∧ gKept σ''.commit L ∧ σ.commit ≤ σ''.commit) ∨
  (∃ L0 σ1 m es, I = L0.map Prod.fst ++ [WalOpG.snap m, WalOpG.save ⟨W64 0, W64 0, W64 0⟩ es] ∧
    gFold σ L0 = some σ1 ∧ gKept σ1.commit L0 ∧ σ.commit ≤ σ1.commit ∧ σ1.commit < uint.nat m.Index' ∧
    σ1.last < uint.nat m.Index' ∧ es ≠ [] ∧ ∀ e ∈ es, uint.nat m.Index' < uint.nat e.Index')

theorem foldlM_take {α β : Type} (f : β → α → Option β) (l : List α) (k : Nat) {x y : β}
    (h : l.foldlM f x = some y) : ∃ y', (l.take k).foldlM f x = some y' := by
  rw [← List.take_append_drop k l, List.foldlM_append] at h
  cases h' : (l.take k).foldlM f x with
  | none => rw [h'] at h; cases h
  | some y' => exact ⟨y', rfl⟩

theorem phsNext_zero (p : HardStateM) : phsNext p ⟨W64 0, W64 0, W64 0⟩ = p :=
  phsNext_empty p ⟨W64 0, W64 0, W64 0⟩ ⟨rfl, rfl, rfl⟩

/-- A torn `Save` (the first entries, no state record) after a disciplined one's start. -/
theorem tDSave_torn {σ1 σ2 : StorContents} {h : HardStateM} {es : List EntryM} (hd : tDSave σ1 h es σ2)
    (hσ1 : σ1.commit ≤ σ1.last) (k : Nat) :
    ∃ τ, walFoldChkFrom σ1 [.save ⟨W64 0, W64 0, W64 0⟩ (es.take k)] = some τ ∧ τ.commit = σ1.commit ∧
      τ.commit ≤ τ.last := by
  obtain ⟨h1, -, -, h4⟩ := hd
  rw [walFoldChkFrom_save1] at h1
  obtain ⟨x, hx, -⟩ := Option.map_eq_some_iff.1 h1
  obtain ⟨y, hy⟩ := foldlM_take _ es k hx
  have hcm : ({ σ1 with hs := phsNext σ1.hs ⟨W64 0, W64 0, W64 0⟩, ents := y } : StorContents).commit =
      σ1.commit := by
    simp only [StorContents.commit, phsNext_zero _]
  refine ⟨_, by rw [walFoldChkFrom_save1, hy]; rfl, hcm, ?_⟩
  rw [hcm]
  rcases readEnts_last hy with ⟨he, rfl⟩ | ⟨e, hle, -⟩
  · exact hσ1
  · have hge := readEnts_last_ge hy hle
    have hmem : e ∈ es := List.mem_of_mem_take (List.mem_of_getLast? hle)
    have := h4 e hmem
    simp only [StorContents.last, StorContents.b] at hge ⊢
    omega

theorem walImg_nil0 {E : Type} {I : List (WalOpG E)} (h : walImg ([] : List (WalOpG E)) 0 I) : I = [] := by
  obtain ⟨j, -, hj, h | ⟨_, _, _, hh, -⟩⟩ := h
  · simp at hj; subst hj; simpa using h
  · simp at hh

theorem phantom_step (σ : StorContents) (hσ : σ.commit ≤ σ.last) :
    gStep σ (.save ⟨W64 0, W64 0, W64 0⟩ [], true) = some σ := by
  have : walFoldChkFrom σ [.save ⟨W64 0, W64 0, W64 0⟩ []] = some σ := by
    rw [walFoldChkFrom_save1]
    simp only [List.foldlM_nil, Option.pure_def, Option.map_some, phsNext_zero]
  exact gStep_save this hσ

/-- **Every image of a disciplined history is good or bad** (`GoodImg`). -/
theorem TDisc.img {σ σ' : StorContents} {B : WalHist} (hD : TDisc σ B σ') (hσ : σ.commit ≤ σ.last)
    {I : WalHist} (hI : walImg B 0 I) : GoodImg σ I := by
  induction hD generalizing I with
  | nil =>
    rw [walImg_nil0 hI]
    exact Or.inl ⟨[], σ, rfl, rfl, fun m hm => by simp at hm, Nat.le_refl _⟩
  | @save σ1 σ2 B h es hB hd ih =>
    rcases walImg_snoc_cases hI with hI | rfl | ⟨h', es', k, ho, hk, rfl⟩
    · exact ih hI
    · obtain ⟨L, hm, hg, hk, hc⟩ := (TDisc.save hB hd).guide
      exact Or.inl ⟨L, σ2, hm, hg, hk, hc⟩
    · cases ho
      obtain ⟨LB, hm, hg, hk, hc⟩ := hB.guide
      have hσ1 := gFold_commitLe LB hσ hg
      obtain ⟨τ, hτ, hτc, hτl⟩ := tDSave_torn hd hσ1 k
      refine Or.inl ⟨LB ++ [(.save ⟨W64 0, W64 0, W64 0⟩ (es.take k), true)], τ, by simp [hm],
        gFold_snoc _ _ _ hg (gStep_save hτ hτl), ?_, by omega⟩
      rw [hτc]; exact gKept_append hk (gKept_save _ _)
  | @own σ1 B m hB hm' ih =>
    rcases walImg_snoc_cases hI with hI | rfl | ⟨h', es', k, ho, hk, rfl⟩
    · exact ih hI
    · obtain ⟨L, hm, hg, hk, hc⟩ := (TDisc.own hB hm').guide
      exact Or.inl ⟨L, _, hm, hg, hk, hc⟩
    · cases ho
  | @recv σ1 σ2 B m h es hB hl hd hmc hes ih =>
    obtain ⟨LB, hm, hg, hk, hc⟩ := hB.guide
    have hσ1 := gFold_commitLe LB hσ hg
    have hok : gSnapOk m σ1 = true := by simp only [gSnapOk, decide_eq_true_eq]; omega
    rcases walImg_append_cases hI with hI | ⟨i, hi, hI | ⟨h', es', k, ho, hk', hI⟩⟩
    · exact ih hI
    · have hi2 : i = 0 ∨ i = 1 := by simp at hi; omega
      rcases hi2 with rfl | rfl
      · simp only [Nat.zero_add, List.take_succ_cons, List.take_zero] at hI; subst hI
        refine Or.inl ⟨LB ++ [(.snap m, false)], σ1, by simp [hm],
          gFold_snoc _ _ _ hg (gStep_snap hok false), gKept_append hk (gKept_false m), hc⟩
      · simp only [Nat.reduceAdd, List.take_succ_cons, List.take_zero] at hI
        subst hI
        obtain ⟨L, hm2, hg2, hk2, hc2⟩ := (TDisc.recv hB hl hd hmc hes).guide
        exact Or.inl ⟨L, σ2, hm2, hg2, hk2, hc2⟩
    · have hi2 : i = 0 ∨ i = 1 := by simp at hi; omega
      rcases hi2 with rfl | rfl
      · simp at ho
      · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
          WalOpG.save.injEq] at ho
        obtain ⟨rfl, rfl⟩ := ho
        simp only [List.take_succ_cons, List.take_zero, List.append_assoc, List.singleton_append] at hI
        subst hI
        by_cases hne : es.take k = []
        · rw [hne]
          refine Or.inl ⟨LB ++ [(.snap m, false)] ++ [(.save ⟨W64 0, W64 0, W64 0⟩ [], true)], σ1,
            by simp [hm], gFold_snoc _ _ _ (gFold_snoc _ _ _ hg (gStep_snap hok false))
              (phantom_step σ1 hσ1), ?_, hc⟩
          exact gKept_append (gKept_append hk (gKept_false m)) (gKept_save _ _)
        · refine Or.inr ⟨LB, σ1, m, es.take k, by simp [hm], hg, hk, hc, by omega, hl, hne,
            fun e he => hes e (List.mem_of_mem_take he)⟩

/-! ## The images of `tSim` -/

theorem walImg_append_mark {E : Type} {A B I : List (WalOpG E)} {n : Nat} (hA : A.length ≤ n)
    (hI : walImg (A ++ B) n I) : ∃ I', I = A ++ I' ∧ walImg B 0 I' := by
  rcases walImg_append_cases hI with hI | ⟨i, hi, hI | ⟨h, es, k, hb, hk, hI⟩⟩
  · obtain ⟨j, h1, h2, h3 | ⟨h, es, k, hj, -, -⟩⟩ := hI
    · have : j = A.length := by omega
      subst this
      refine ⟨[], by rw [h3, List.take_length, List.append_nil], 0, Nat.le_refl _, Nat.zero_le _, Or.inl ?_⟩
      simp
    · have := getElem?_some_lt hj; omega
  · exact ⟨B.take (i + 1), hI, i + 1, Nat.zero_le _, by omega, Or.inl rfl⟩
  · refine ⟨B.take i ++ [.save ⟨0, 0, 0⟩ (es.take k)], by rw [hI, List.append_assoc], i, Nat.zero_le _,
      by omega, Or.inr ⟨h, es, k, hb, hk, rfl⟩⟩

theorem tRestartG_fst (A : WalHist) : (tRestartG A).map Prod.fst = A := by
  unfold tRestartG; rw [remask_fst]; simp [Function.comp_def]

theorem gFold_fresh_commit {L : List (WalOp × Bool)} {σ : StorContents} (h : gFold walFresh L = some σ) :
    uint.nat (walLastHS (L.map Prod.fst)).Commit' = σ.commit := by
  rw [walLastHS_eq]; show _ = uint.nat σ.hs.Commit'; rw [gFold_hs L h]; rfl

theorem remask_congr (c : Nat) {L L' : List (WalOp × Bool)} (h : L.map Prod.fst = L'.map Prod.fst) :
    remask c L = remask c L' := by
  unfold remask
  induction L generalizing L' with
  | nil => cases L' with
    | nil => rfl
    | cons _ _ => simp at h
  | cons x L ih => cases L' with
    | nil => simp at h
    | cons y L' =>
      simp only [List.map_cons, List.cons.injEq] at h ⊢
      exact ⟨by rw [h.1], ih h.2⟩

/-- **The torn `Save` after a received snapshot's record fails the restart's read too.** -/
theorem walRead_bad {L : List (WalOp × Bool)} {σ1 : StorContents} (hL : gFold walFresh L = some σ1)
    (hk : gKept σ1.commit L) {m : SnapshotMetadataM} (hc : σ1.commit < uint.nat m.Index')
    (hl : σ1.last < uint.nat m.Index') {es : List EntryM} (hne : es ≠ [])
    (hes : ∀ e ∈ es, uint.nat m.Index' < uint.nat e.Index') :
    walRead (L.map Prod.fst ++ [WalOpG.snap m, WalOpG.save ⟨W64 0, W64 0, W64 0⟩ es]) = none := by
  have hhs : walLastHS (L.map Prod.fst ++ [WalOpG.snap m, WalOpG.save ⟨W64 0, W64 0, W64 0⟩ es]) =
      σ1.hs := by
    rw [walLastHS_bad, walLastHS_eq, gFold_hs L hL]; rfl
  have hcI : uint.nat (walLastHS (L.map Prod.fst ++
      [WalOpG.snap m, WalOpG.save ⟨W64 0, W64 0, W64 0⟩ es])).Commit' = σ1.commit := by rw [hhs]; rfl
  unfold walRead
  rw [hcI, List.filter_append]
  have hnc : ¬ uint.nat m.Index' ≤ σ1.commit := by omega
  simp only [List.filter_cons, walKeep, hnc, decide_false, Bool.false_eq_true, ↓reduceIte, decide_true,
    List.filter_nil]
  obtain ⟨R1, hR1, hrel⟩ := gFold_remask σ1.commit L hL (SRel_refl _) hk
  rw [remask_congr _ (L' := (L.map Prod.fst).map (fun o => (o, true))) (by simp [Function.comp_def])] at hR1
  obtain ⟨hf, -⟩ := gFold_remask_filter σ1.commit (L.map Prod.fst)
    (by simp [walFresh, StorContents.commit, StorContents.last]) hR1
  rw [walFoldChkFrom_append, hf, Option.bind_some]
  have hb : R1.b ≤ σ1.commit := by
    refine walFoldChkFrom_b_le (fun m' hm' => ?_) (by simp [walFresh, StorContents.b]) hf
    have := (List.mem_filter.1 hm').2
    simpa [walKeep] using this
  have hRl := SRel_last hrel
  exact save_fail (by omega) _ hne hes

/-- **A good image: its restart's guide succeeds** (re-marked by its own commit). -/
theorem good_restart {L : List (WalOp × Bool)} {σ : StorContents} (hg : gFold walFresh L = some σ)
    (hk : gKept σ.commit L) :
    ∃ σR, gFold walFresh (tRestartG (L.map Prod.fst)) = some σR := by
  obtain ⟨R1, hR1, -⟩ := gFold_remask σ.commit L hg (SRel_refl _) hk
  refine ⟨R1, ?_⟩
  unfold tRestartG
  rw [gFold_fresh_commit hg, remask_congr _ (L' := L) (by simp [Function.comp_def])]
  exact hR1

/-- **Every image at the mark: `ReadAll` fails on it, or its restart's guide succeeds.** -/
theorem tSim_img {H : WalHist} {n : Nat} (hs : tSim H n) {I : WalHist} (hI : walImg H n I) :
    ((∀ cut s σ', ¬ walReadAllOk I cut s σ') ∧ walRead I = none) ∨
      ∃ σR, gFold walFresh (tRestartG I) = some σR := by
  -- the part since the restart: the image of a disciplined history, or of one with a trailing record
  have key : ∀ (A B : WalHist) σA, A.length ≤ n → gFold walFresh (tRestartG A) = some σA →
      (∀ I', walImg B 0 I' → GoodImg σA I') → walImg (A ++ B) n I →
      ((∀ cut s σ', ¬ walReadAllOk I cut s σ') ∧ walRead I = none) ∨
        ∃ σR, gFold walFresh (tRestartG I) = some σR := by
    intro A B σA hA hgA himg hI
    obtain ⟨I', rfl, hI'⟩ := walImg_append_mark hA hI
    have hcA := gFold_fresh_commit hgA
    rw [tRestartG_fst] at hcA
    have hkA : gKept σA.commit (tRestartG A) := by
      intro m hm
      unfold tRestartG remask at hm
      obtain ⟨⟨o, b⟩, -, he⟩ := List.mem_map.1 hm
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, hk⟩ := he
      simp only [walKeep, decide_eq_true_eq] at hk
      omega
    rcases himg I' hI' with ⟨L, σ'', hm, hg, hk, hc⟩ |
      ⟨L0, σ1, m, es, rfl, hg, hk0, hc0, hc, hl, hne, hes⟩
    · right
      have hg' : gFold walFresh (tRestartG A ++ L) = some σ'' := by rw [gFold_append, hgA]; exact hg
      have hk' : gKept σ''.commit (tRestartG A ++ L) := gKept_append (gKept_mono hkA hc) hk
      have := good_restart hg' hk'
      rwa [List.map_append, tRestartG_fst, hm] at this
    · left
      have hg' : gFold walFresh (tRestartG A ++ L0) = some σ1 := by rw [gFold_append, hgA]; exact hg
      have hk' : gKept σ1.commit (tRestartG A ++ L0) := gKept_append (gKept_mono hkA hc0) hk0
      have h1 := readAll_bad hg' hc hl hne hes
      have h2 := walRead_bad hg' hk' hc hl hne hes
      rw [List.map_append, tRestartG_fst, List.append_assoc] at h1 h2
      exact ⟨h1, h2⟩
  rcases hs with ⟨σ, A, B, σA, rfl, hA, hgA, hD⟩ | ⟨H0, σ, m, rfl, ⟨A, B, σA, rfl, hA, hgA, hD⟩, hl⟩
  · exact key A B σA hA hgA (fun I' h => hD.img (gFold_commitLe _ (by simp [walFresh,
      StorContents.commit, StorContents.last]) hgA) h) hI
  · refine key A (B ++ [.snap m]) σA hA hgA ?_ (by rwa [List.append_assoc] at hI)
    intro I' hI'
    have hσA := gFold_commitLe _ (by simp [walFresh, StorContents.commit, StorContents.last]) hgA
    rcases walImg_snoc_cases hI' with hI' | rfl | ⟨_, _, _, ho, _, _⟩
    · exact hD.img hσA hI'
    · obtain ⟨LB, hm, hg, hk, hc⟩ := hD.guide
      have hok : gSnapOk m σ = true := by simp only [gSnapOk, decide_eq_true_eq]; omega
      exact Or.inl ⟨LB ++ [(.snap m, false)], σ, by simp [hm], gFold_snoc _ _ _ hg (gStep_snap hok false),
        gKept_append hk (gKept_false m), hc⟩
    · cases ho

/-- **`tReadsBackOk` of every image at the mark.** -/
theorem tSim_readsBack {H : WalHist} {n : Nat} (hs : tSim H n) {I : WalHist} (hI : walImg H n I) :
    ∀ cut s σ', walReadAllOk I cut s σ' → walReadsBack I := by
  intro cut s σ' hok
  rcases tSim_img hs hI with ⟨hbad, -⟩ | ⟨σR, hR⟩
  · exact absurd hok (hbad cut s σ')
  · exact (gFold_readsBack hR).1

/-- **A restart from an image `ReadAll` succeeds on** starts the discipline again from the image's read,
at the image's length. -/
theorem tSim_restart {H : WalHist} {n : Nat} (hs : tSim H n) {I : WalHist} (hI : walImg H n I)
    {cut : Nat} {s : w64 × w64} {σ' : StorContents} (hok : walReadAllOk I cut s σ') :
    ∃ σR, walRead I = some σR ∧ walReadsBack I ∧ tSimAt I I.length σR := by
  rcases tSim_img hs hI with ⟨hbad, -⟩ | ⟨σR, hR⟩
  · exact absurd hok (hbad cut s σ')
  · obtain ⟨h1, h2⟩ := gFold_readsBack hR
    exact ⟨σR, h2, h1, I, [], σR, by simp, Nat.le_refl _, hR, .nil _⟩

/-- **A restart from an image whose restart read succeeds** starts the discipline again from that read,
at the image's length. -/
theorem tSim_restartRead {H : WalHist} {n : Nat} (hs : tSim H n) {I : WalHist} (hI : walImg H n I)
    {σ : StorContents} (hr : walRead I = some σ) : walReadsBack I ∧ tSimAt I I.length σ := by
  rcases tSim_img hs hI with ⟨-, hbad⟩ | ⟨σR, hR⟩
  · rw [hbad] at hr; cases hr
  · obtain ⟨h1, h2⟩ := gFold_readsBack hR
    rw [h2] at hr; cases hr
    exact ⟨h1, I, [], σ, by simp, Nat.le_refl _, hR, .nil _⟩

end pure

end etcd_wal
end EtcdGrove
end Perennial
