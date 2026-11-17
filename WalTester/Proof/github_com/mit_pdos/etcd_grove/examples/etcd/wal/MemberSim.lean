/-
Lean-first (no Rocq counterpart).

# The member's raft-like fields against its WAL history's discipline (W4c U5, tenth session)

`tMemSim o c bs l cm`: the candidate's history (`c.h ++ since`) is disciplined since the last restart
(`ReadsBack.tSimAt`, at `|c.h|`: the restart's image is `c.h`) up to a fold `σ` whose base, last index
and commit are the member's `base`, `last` and `commit` fields. Every operation keeps it, and gives the
`tSim` premise `save`/`saveSnap` take (`member.save.spec`), through the lemmas below, one per kind of
operation:

* `tMemSim_save`: a `Save` of consecutive entries from `lo` (above the base and the commit, at most one
  past the last index; or none), with a commit not below the old one and at most the new last index;
* `tMemSim_own`: an own snapshot at or below the commit;
* `tMemSim_recv`: a received snapshot above the last index and its `Save` (commit the snapshot's index,
  consecutive entries above it).
-/
module

public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.SnapPure
public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.SavePure

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open go_etcd_io.raft.v3 WalEnc

section pure
variable [GooseExts]

/-- **The member's fields are the disciplined history's fold** (see the file header). -/
def tMemSim (o : TOracle) (c : TCand) (bs l cm : w64) : Prop :=
  ∃ σ, tSimAt ((tCandHist o c).map absOp) c.h.length σ ∧ σ.b = uint.nat bs ∧ σ.last = uint.nat l ∧
    σ.commit = uint.nat cm

/-- The entries' indices are consecutive from `lo`. -/
def tConsec (lo : Nat) (es : List TEnt) : Prop :=
  es.map (fun e => uint.nat e.index') = List.range' lo es.length

theorem tConsec_nil (lo : Nat) : tConsec lo [] := rfl

theorem tConsec_snoc {lo : Nat} {es : List TEnt} (h : tConsec lo es) (e : TEnt)
    (he : uint.nat e.index' = lo + es.length) : tConsec lo (es ++ [e]) := by
  unfold tConsec at h ⊢
  rw [List.map_append, h, List.length_append, List.length_singleton, List.range'_concat]
  simp [he]

theorem tConsec_get {lo : Nat} {es : List TEnt} (h : tConsec lo es) {k : Nat} {x : TEnt}
    (hx : es[k]? = some x) : uint.nat x.index' = lo + k := by
  have hk : k < es.length := (List.getElem?_eq_some_iff.1 hx).1
  have h1 : (es.map (fun e => uint.nat e.index'))[k]? = some (uint.nat x.index') := by
    rw [List.getElem?_map, hx]; rfl
  rw [h, List.getElem?_range' hk] at h1
  simp at h1; omega

theorem tSimAt_commitLe {H : WalHist} {n : Nat} {σ : StorContents} (h : tSimAt H n σ) :
    σ.commit ≤ σ.last := by
  obtain ⟨A, B, σA, -, -, hg, hD⟩ := h
  have h0 := gFold_commitLe _ (by simp [walFresh, StorContents.commit, StorContents.last]) hg
  clear hg
  induction hD with
  | nil => exact h0
  | save _ hd _ => exact hd.2.1
  | own _ _ ih => exact walSaveSnap_commitLe _ ih
  | recv _ _ hd _ _ _ => exact hd.2.1

/-- `tMemSim`, at the candidate's mark. -/
theorem tMemSim_sim {o : TOracle} {c : TCand} {bs l cm : w64} (h : tMemSim o c bs l cm) :
    tSim ((tCandHist o c).map absOp) (tCandMark o c) := by
  obtain ⟨σ, hs, -⟩ := h
  exact tSimAt_tSim (tSimAt_mark (by unfold tCandMark; omega) hs)

theorem tMemSim_congr {o o' : TOracle} {c : TCand} {bs l cm : w64}
    (hh : tCandHist o' c = tCandHist o c) (h : tMemSim o c bs l cm) : tMemSim o' c bs l cm := by
  unfold tMemSim; rw [hh]; exact h

theorem tMemSim_commitLe {o : TOracle} {c : TCand} {bs l cm : w64} (h : tMemSim o c bs l cm) :
    uint.nat cm ≤ uint.nat l := by
  obtain ⟨σ, hs, -, hl, hc⟩ := h
  have := tSimAt_commitLe hs
  omega

theorem tMemSim_baseLe {o : TOracle} {c : TCand} {bs l cm : w64} (h : tMemSim o c bs l cm) :
    uint.nat bs ≤ uint.nat l := by
  obtain ⟨σ, -, hb, hl, -⟩ := h
  simp only [StorContents.last] at hl
  omega

/-! ## A `Save` of consecutive entries -/

theorem readEnts_consec (b : Nat) : ∀ (es : List EntryM) (lo : Nat) (ents : List EntryM), es ≠ [] →
    es.map (fun e => uint.nat e.Index') = List.range' lo es.length → b < lo → lo - b - 1 ≤ ents.length →
    es.foldlM (fun ents e => readEnt b ents e) ents = some (ents.take (lo - b - 1) ++ es) := by
  intro es
  induction es with
  | nil => intro _ _ h; exact absurd rfl h
  | cons e es ih =>
    intro lo ents _ hc hb hl
    simp only [List.map_cons, List.length_cons, List.range'_succ, List.cons.injEq] at hc
    obtain ⟨he, hc⟩ := hc
    have hr : readEnt b ents e = some (ents.take (lo - b - 1) ++ [e]) := by
      unfold readEnt; rw [if_neg (by omega), if_pos (by omega), he]
    simp only [List.foldlM_cons, hr, Option.bind_eq_bind, Option.bind_some]
    cases es with
    | nil => simp
    | cons e' es' =>
      have hlen : lo + 1 - b - 1 ≤ (ents.take (lo - b - 1) ++ [e]).length := by
        rw [List.length_append, List.length_take, List.length_singleton]; omega
      rw [ih (lo + 1) _ (List.cons_ne_nil _ _) hc (by omega) hlen]
      have hlen2 : (ents.take (lo - b - 1) ++ [e]).length ≤ lo + 1 - b - 1 := by
        rw [List.length_append, List.length_take, List.length_singleton]; omega
      rw [List.take_of_length_le hlen2]
      simp

theorem phsNext_commit_ge {p q : HardStateM} (h : uint.nat p.Commit' ≤ uint.nat q.Commit') :
    (phsNext p q).Commit' = q.Commit' := by
  unfold phsNext
  split
  · next he => obtain ⟨-, -, hq⟩ := he; rw [hq] at h ⊢; word
  · rfl

/-- **A disciplined `Save` of consecutive entries** (or none). -/
theorem tDSave_consec {σ : StorContents} {h : THs} {es : List TEnt} {lo : Nat}
    (hσ : σ.commit ≤ σ.last) (hc : σ.commit ≤ uint.nat h.commit')
    (hes : es = [] ∨ (tConsec lo es ∧ σ.b < lo ∧ σ.commit < lo ∧ lo ≤ σ.last + 1)) :
    let l' := if es = [] then σ.last else lo + es.length - 1
    uint.nat h.commit' ≤ l' →
    ∃ σ2, tDSave σ (absHs h) (es.map absEnt) σ2 ∧ σ2.b = σ.b ∧ σ2.last = l' ∧
      σ2.commit = uint.nat h.commit' := by
  intro l' hcl
  have hcom : (phsNext σ.hs (absHs h)).Commit' = h.commit' := phsNext_commit_ge hc
  by_cases hne : es = []
  · subst hne
    have hl0 : l' = σ.last := by simp [l']
    rw [hl0] at hcl
    refine ⟨{ σ with hs := phsNext σ.hs (absHs h) }, ⟨?_, ?_, ?_, by simp⟩, rfl, rfl, ?_⟩
    · rw [walFoldChkFrom_save1]; simp
    · simp only [StorContents.commit, StorContents.last, hcom]
      simp only [StorContents.last] at hcl; exact hcl
    · simp only [StorContents.commit, hcom]; exact hc
    · simp only [StorContents.commit, hcom]
  · obtain ⟨hcs, hb, hco, hlo⟩ := hes.resolve_left hne
    have hl'e : l' = lo + es.length - 1 := by simp [l', hne]
    have hcs' : (es.map absEnt).map (fun e => uint.nat e.Index') = List.range' lo (es.map absEnt).length := by
      rw [List.map_map, List.length_map]; exact hcs
    have hr := readEnts_consec σ.b (es.map absEnt) lo σ.ents (by simpa using hne) hcs' hb
      (by simp only [StorContents.last] at hlo; omega)
    refine ⟨{ σ with hs := phsNext σ.hs (absHs h), ents := σ.ents.take (lo - σ.b - 1) ++ es.map absEnt },
      ⟨?_, ?_, ?_, ?_⟩, rfl, ?_, ?_⟩
    · rw [walFoldChkFrom_save1, hr]; rfl
    · simp only [StorContents.commit, StorContents.last, StorContents.b, hcom, List.length_append,
        List.length_take, List.length_map]
      simp only [StorContents.last, StorContents.b] at hlo hb
      rw [hl'e] at hcl; omega
    · simp only [StorContents.commit, hcom]; exact hc
    · intro e he
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 he
      have : uint.nat x.index' ∈ List.range' lo es.length := by
        rw [← hcs]; exact List.mem_map_of_mem hx
      rw [List.mem_range'_1] at this
      show σ.commit < uint.nat x.index'
      omega
    · simp only [StorContents.last, StorContents.b, List.length_append, List.length_take, List.length_map]
      simp only [StorContents.last, StorContents.b] at hlo hb
      rw [hl'e]; omega
    · simp only [StorContents.commit, hcom]

theorem tSaveO_hist (o : TOracle) (c : TCand) (h : THs) (es : List TEnt)
    (hne : ¬ (tHsEmpty h && es.isEmpty) = true) :
    tCandHist (tSaveO o h es) c = tCandHist o c ++ [tSaveOp h es] := by
  unfold tSaveO
  rw [if_neg hne]
  split <;> simp [tCandHist, tSynced, tSaveO1]

theorem tSaveO_empty (o : TOracle) (h : THs) (es : List TEnt) (he : (tHsEmpty h && es.isEmpty) = true) :
    tSaveO o h es = o := by
  unfold tSaveO; rw [if_pos he]

/-- **A `Save` keeps the fields' relation**, and gives `save`'s `tSim` premise. -/
theorem tMemSim_save {o : TOracle} {c : TCand} {bs l cm : w64} (hm : tMemSim o c bs l cm) {h : THs}
    {es : List TEnt} {lo : Nat} (hc : uint.nat cm ≤ uint.nat h.commit')
    (hes : es = [] ∨ (tConsec lo es ∧ uint.nat bs < lo ∧ uint.nat cm < lo ∧ lo ≤ uint.nat l + 1))
    (l' : w64) (hl' : uint.nat l' = if es = [] then uint.nat l else lo + es.length - 1)
    (hcl : uint.nat h.commit' ≤ uint.nat l') :
    tSim ((tCandHist (tSaveO1 o h es) c).map absOp) (tCandMark o c) ∧
      tMemSim (tSaveO o h es) c bs l' h.commit' := by
  obtain ⟨σ, hs, hb, hl, hcm⟩ := hm
  have hσ := tSimAt_commitLe hs
  obtain ⟨σ2, hd, hb2, hl2, hc2⟩ := tDSave_consec (h := h) (es := es) (lo := lo) hσ (by omega)
    (by rcases hes with h | ⟨h1, h2, h3, h4⟩
        · exact Or.inl h
        · exact Or.inr ⟨h1, by omega, by omega, by omega⟩)
    (by split <;> simp_all <;> omega)
  have hs2 := tSimAt_save hs hd
  have hh1 : (tCandHist (tSaveO1 o h es) c).map absOp =
      (tCandHist o c).map absOp ++ [WalOpG.save (absHs h) (es.map absEnt)] := by
    rw [tSaveO1_hist, List.map_append]; rfl
  refine ⟨?_, ?_⟩
  · rw [hh1]; exact tSimAt_tSim (tSimAt_mark (by unfold tCandMark; omega) hs2)
  · by_cases he : (tHsEmpty h && es.isEmpty) = true
    · rw [tSaveO_empty o h es he]
      rw [Bool.and_eq_true] at he
      have hes0 : es = [] := List.isEmpty_iff.1 he.2
      have hh0 : h.commit' = W64 0 := by
        simp only [tHsEmpty, Bool.and_eq_true, decide_eq_true_eq] at he; exact he.1.2
      subst hes0
      refine ⟨σ, hs, hb, by rw [hl', hl]; simp, ?_⟩
      rw [hcm]; rw [hh0] at hc ⊢; simp at hc ⊢; omega
    · refine ⟨σ2, ?_, by rw [hb2, hb], by rw [hl2, hl']; split <;> simp_all, hc2⟩
      rw [tSaveO_hist o c h es he, List.map_append]
      exact hs2

/-! ## Snapshots -/

theorem tSnapO_hist (o : TOracle) (c : TCand) (idx term : w64) :
    tCandHist (tSnapO o idx term) c = tCandHist o c ++ [tSnapOp idx term] := by
  unfold tSnapO tSynced tSnapO1 tCandHist; simp

theorem tSnapO1_hist' (o : TOracle) (c : TCand) (idx term : w64) :
    tCandHist (tSnapO1 o idx term) c = tCandHist o c ++ [tSnapOp idx term] := by
  unfold tCandHist tSnapO1; simp

theorem absSnapMd_index (idx term : w64) : (absSnapMd idx term).Index' = idx := rfl

/-- **An own snapshot at or below the commit keeps the relation** (the base moved to it), and gives
`saveSnap`'s `tSim` premise. -/
theorem tMemSim_own {o : TOracle} {c : TCand} {bs l cm : w64} (hm : tMemSim o c bs l cm) {a t : w64}
    (hab : uint.nat bs < uint.nat a) (hac : uint.nat a ≤ uint.nat cm) :
    tSim ((tCandHist (tSnapO1 o a t) c).map absOp) (tCandMark o c) ∧ tMemSim (tSnapO o a t) c a l cm := by
  obtain ⟨σ, hs, hb, hl, hcm⟩ := hm
  have hσ := tSimAt_commitLe hs
  have hs2 := tSimAt_own (m := absSnapMd a t) hs (by rw [absSnapMd_index]; omega)
  have hh : ∀ o', tCandHist o' c = tCandHist o c ++ [tSnapOp a t] →
      (tCandHist o' c).map absOp = (tCandHist o c).map absOp ++ [WalOpG.snap (absSnapMd a t)] := by
    intro o' h'; rw [h', List.map_append]; rfl
  have hnl : ¬ uint.nat (absSnapMd a t).Index' < σ.b := by rw [absSnapMd_index]; omega
  refine ⟨by rw [hh _ (tSnapO1_hist' o c a t)]; exact tSimAt_tSim (tSimAt_mark (by unfold tCandMark; omega) hs2),
    _, by rw [hh _ (tSnapO_hist o c a t)]; exact hs2, ?_, ?_, ?_⟩
  · rw [walSaveSnap_b hnl, absSnapMd_index]
  · simp only [StorContents.last]
    rw [walSaveSnap_b hnl, walSaveSnap_ents hnl, absSnapMd_index, if_pos (by omega), List.length_drop]
    simp only [StorContents.last] at hl hσ; simp only [StorContents.commit] at hcm hσ
    omega
  · rw [walSaveSnap_commit]; exact hcm

/-- **A received snapshot above the last index, then its `Save`** (commit the snapshot's index, `k`
consecutive entries above it): the relation at the snapshot (base, last index and commit `s`, then the
entries), and the `tSim` premises of both calls. -/
theorem tMemSim_recv {o : TOracle} {c : TCand} {bs l cm : w64} (hm : tMemSim o c bs l cm) {s t : w64}
    (hls : uint.nat l < uint.nat s) (h : THs) (es : List TEnt) (hhc : h.commit' = s)
    (hes : tConsec (uint.nat s + 1) es) (l' : w64) (hl' : uint.nat l' = uint.nat s + es.length) :
    tSim ((tCandHist (tSnapO1 o s t) c).map absOp) (tCandMark o c) ∧
    tSim ((tCandHist (tSaveO1 (tSnapO o s t) h es) c).map absOp) (tCandMark (tSnapO o s t) c) ∧
      tMemSim (tSaveO (tSnapO o s t) h es) c s l' s := by
  obtain ⟨σ, hs, hb, hl, hcm⟩ := hm
  have hσ := tSimAt_commitLe hs
  have hh : ∀ o', tCandHist o' c = tCandHist o c ++ [tSnapOp s t] →
      (tCandHist o' c).map absOp = (tCandHist o c).map absOp ++ [WalOpG.snap (absSnapMd s t)] := by
    intro o' h'; rw [h', List.map_append]; rfl
  refine ⟨?_, ?_⟩
  · rw [hh _ (tSnapO1_hist' o c s t)]
    exact tSim_snapT (tSimAt_mark (by unfold tCandMark; omega) hs) (by rw [absSnapMd_index]; omega)
  -- the fold after the record: base and last index `s`, no entries
  have hnl : ¬ uint.nat (absSnapMd s t).Index' < σ.b := by
    rw [absSnapMd_index]; simp only [StorContents.last] at hl; omega
  obtain ⟨σ1, hσ1⟩ : ∃ σ1, σ1 = walSaveSnap σ (absSnapMd s t) := ⟨_, rfl⟩
  have hb1 : σ1.b = uint.nat s := by rw [hσ1, walSaveSnap_b hnl, absSnapMd_index]
  have hns : ¬ uint.nat (absSnapMd s t).Index' ≤ σ.commit := by rw [absSnapMd_index]; omega
  have he1 : σ1.ents = [] := by
    rw [hσ1, walSaveSnap_ents hnl, if_neg hns]
  have hc1 : σ1.commit = uint.nat cm := by rw [hσ1, walSaveSnap_commit, hcm]
  have hlast1 : σ1.last = uint.nat s := by simp only [StorContents.last, hb1, he1, List.length_nil]; omega
  obtain ⟨σ2, hd, hb2, hl2, hc2⟩ := tDSave_consec (σ := σ1) (h := h) (es := es) (lo := uint.nat s + 1)
    (by rw [hc1, hlast1]; omega) (by rw [hc1, hhc]; omega)
    (by
      by_cases hne : es = []
      · exact Or.inl hne
      · exact Or.inr ⟨hes, by omega, by omega, by omega⟩)
    (by rw [hhc]; split <;> omega)
  rw [hσ1] at hd
  have hrec := tSimAt_recv (m := absSnapMd s t) hs (by rw [absSnapMd_index]; omega) hd
    (by rw [hc2, absSnapMd_index, hhc]; exact Nat.le_refl _) (by
      intro e he
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 he
      have : uint.nat x.index' ∈ List.range' (uint.nat s + 1) es.length := by
        rw [← hes]; exact List.mem_map_of_mem hx
      rw [List.mem_range'_1] at this
      show uint.nat (absSnapMd s t).Index' < uint.nat x.index'
      rw [absSnapMd_index]; omega)
  have hh2 : ∀ o', tCandHist o' c = tCandHist (tSnapO o s t) c ++ [tSaveOp h es] →
      (tCandHist o' c).map absOp = (tCandHist o c).map absOp ++
        [WalOpG.snap (absSnapMd s t), WalOpG.save (absHs h) (es.map absEnt)] := by
    intro o' h'; rw [h', tSnapO_hist]
    simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc, List.singleton_append]; rfl
  have hhcn : ¬ (tHsEmpty h && es.isEmpty) = true := by
    intro hc
    simp only [Bool.and_eq_true, tHsEmpty, decide_eq_true_eq] at hc
    rw [hhc] at hc
    have := hc.1.2
    subst this; simp at hls
  refine ⟨?_, σ2, ?_, ?_, ?_, ?_⟩
  · rw [hh2 _ (tSaveO1_hist _ c h es)]
    exact tSimAt_tSim (tSimAt_mark (by unfold tCandMark tSnapO tSynced tSnapO1; simp) hrec)
  · rw [hh2 _ (tSaveO_hist _ c h es hhcn)]; exact hrec
  · rw [hb2, hb1]
  · rw [hl2, hl']; split
    · next he => subst he; simp at hl' ⊢; omega
    · omega
  · rw [hc2, hhc]

/-! ## The last index is below `2^63` -/

/-- Every index the history records is below `B`. -/
def walIdxLt (B : Nat) (H : WalHist) : Prop :=
  ∀ o ∈ H, match o with
    | .save _ es => ∀ e ∈ es, uint.nat e.Index' < B
    | .snap m => uint.nat m.Index' < B

theorem save_last_lt {B : Nat} {σ σ' : StorContents} {h : HardStateM} {es : List EntryM}
    (hl : σ.last < B) (hes : ∀ e ∈ es, uint.nat e.Index' < B)
    (hf : walFoldChkFrom σ [.save h es] = some σ') : σ'.last < B := by
  rw [walFoldChkFrom_save1] at hf
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 hf
  simp only [StorContents.last, StorContents.b] at hl ⊢
  rcases readEnts_last hx with ⟨-, rfl⟩ | ⟨e, hle, hbd⟩
  · exact hl
  · have := hes e (List.mem_of_getLast? hle)
    simp only [StorContents.b] at hbd
    omega

theorem snap_last_lt {B : Nat} {σ : StorContents} {m : SnapshotMetadataM} (hl : σ.last < B)
    (hm : uint.nat m.Index' < B) : (walSaveSnap σ m).last < B := by
  by_cases hg : uint.nat m.Index' < σ.b
  · rw [walSaveSnap_noop hg]; exact hl
  · simp only [StorContents.last, walSaveSnap_b hg, walSaveSnap_ents hg]
    simp only [StorContents.last] at hl
    split
    · simp only [List.length_drop]; omega
    · simp only [List.length_nil]; omega

theorem gFold_last_lt {B : Nat} : ∀ (L : List (WalOp × Bool)) {G G' : StorContents}, G.last < B →
    walIdxLt B (L.map Prod.fst) → gFold G L = some G' → G'.last < B := by
  intro L
  induction L with
  | nil => intro G G' hl _ h; cases h; exact hl
  | cons x L ih =>
    intro G G' hl hb h
    obtain ⟨o, b⟩ := x
    simp only [gFold, Option.bind_eq_some_iff] at h
    obtain ⟨G2, hst, h⟩ := h
    have hb' : walIdxLt B (L.map Prod.fst) := fun o' ho' => hb o' (by simp [ho'])
    have ho := hb o (by simp)
    refine ih ?_ hb' h
    cases o with
    | save hs es =>
      cases b with
      | false => cases hst
      | true =>
        simp only [gStep] at hst
        split at hst
        · next G3 hg3 =>
          split at hst
          · cases hst; exact save_last_lt hl ho hg3
          · cases hst
        · cases hst
    | snap m =>
      simp only [gStep] at hst
      split at hst
      · cases hst; split
        · exact snap_last_lt hl ho
        · exact hl
      · cases hst

theorem TDisc.last_lt {B : Nat} {σ σ' : StorContents} {H : WalHist} (hD : TDisc σ H σ')
    (hl : σ.last < B) (hb : walIdxLt B H) : σ'.last < B := by
  induction hD with
  | nil => exact hl
  | @save σ1 σ2 B0 h es _ hd ih =>
    exact save_last_lt (ih (fun o ho => hb o (by simp [ho]))) (hb (.save h es) (by simp)) hd.1
  | @own σ1 B0 m _ _ ih =>
    exact snap_last_lt (ih (fun o ho => hb o (by simp [ho]))) (hb (.snap m) (by simp))
  | @recv σ1 σ2 B0 m h es _ _ hd _ _ ih =>
    exact save_last_lt (snap_last_lt (ih (fun o ho => hb o (by simp [ho]))) (hb (.snap m) (by simp)))
      (hb (.save h es) (by simp)) hd.1

theorem tSimAt_last_lt {B : Nat} {H : WalHist} {n : Nat} {σ : StorContents} (hs : tSimAt H n σ)
    (hb : walIdxLt B H) (hB : 0 < B) : σ.last < B := by
  obtain ⟨A, B0, σA, rfl, -, hg, hD⟩ := hs
  have hA : σA.last < B := gFold_last_lt _ (by simp [walFresh, StorContents.last, StorContents.b]; omega)
    (by rw [tRestartG_fst]; exact fun o ho => hb o (List.mem_append_left _ ho)) hg
  exact hD.last_lt hA (fun o ho => hb o (List.mem_append_right _ ho))

theorem tHistWf_idxLt {h : List TOp} (hw : tHistWf h) : walIdxLt (2 ^ 63) (h.map absOp) := by
  intro o ho
  obtain ⟨op, hop, rfl⟩ := List.mem_map.1 ho
  have hwf := hw op hop
  unfold absOp
  cases hs : op.snap
  · simp only [Bool.false_eq_true, ↓reduceIte]
    intro e he
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 he
    exact (hwf.2.1 hs x hx).2.2.1
  · simp only [↓reduceIte]
    exact (hwf.1 hs).1

/-- **The member's last index is below `2^63`** (every index its history records is). -/
theorem tMemSim_last_lt {o : TOracle} {c : TCand} {bs l cm : w64} (h : tMemSim o c bs l cm)
    (hw : tHistWf (tCandHist o c)) : uint.nat l < 2 ^ 63 := by
  obtain ⟨σ, hs, -, hl, -⟩ := h
  rw [← hl]
  exact tSimAt_last_lt hs (tHistWf_idxLt hw) (by decide)

end pure

end etcd_wal
end EtcdGrove
end Perennial
