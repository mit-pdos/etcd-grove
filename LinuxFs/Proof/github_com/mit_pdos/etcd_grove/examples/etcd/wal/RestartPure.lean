/-
Lean-first (no Rocq counterpart).

# The restart's pure facts (W4c U5, `restartRead`/`restart`)

* **`walReadAllOk_read0`**: `ReadAll`'s success post (`walReadAllOk I cut s σ'`: the fold at the base `s`
  from some position `k` between the read position and `walOpenPos I s.1`) is the unpurged read
  `walRead I`, with the base `s`, for a history that reads back (`walReadsBack`, W4b's C2-C4 premise) and
  has no maximal index. So the tester's check may take the purged prefix 0 (`walReadCut I 0`), whatever
  `k` `ReadAll` read from: no bound of `k` by the candidate's purge bound is needed.
* **`tCandOk_open`**: the opens raise. Before an `Open` at `a` the tester stores the oracle with `a`
  appended to its pending opens (`tAddOpen`); the WAL state's `unl` raised by `Open`'s update to
  `walOpenPos … a` is still accounted for by the same candidate, through `tOpenBound` over its images
  (`walOpenPos ≤ walNameBound = tNameBound img a ≤ tOpenBound imgs a`).
-/
module

public import LinuxFs.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.Check
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.WalReadAllPost
public import LinuxFs.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.FromRaft

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI go_etcd_io.raft.v3 WalEnc

section pure
variable [GooseExts]

/-- **`ReadAll`'s read is the unpurged read** (see the file header). -/
theorem walReadAllOk_read0 {I : WalHist} {cut : Nat} {s : w64 × w64} {σ' : StorContents}
    (hpost : walReadAllOk I cut s σ') (hmax : ¬ walHasMaxIdx I) (hb : walReadsBack I) :
    ∃ σ, walRead I = some σ ∧ σ.hs = σ'.hs ∧ σ.ents = σ'.ents ∧ σ.base = entryID.mk s.2 s.1 := by
  obtain ⟨k, -, hk, hs, hat⟩ := hpost
  obtain ⟨σk, hcutk, e1, e2⟩ := walReadAt_cut hs (fun _ => hb) hat
  have hbase := walReadCut_base hcutk hs
  obtain ⟨hcl, σ0, h0⟩ := hb
  by_cases hk0 : k = 0
  · subst hk0
    rw [walReadCut_zero] at hcutk
    exact ⟨σk, hcutk, e1, e2, hbase⟩
  · have hmem := walNewestPair_mem hs.symm
    unfold walValidSnaps at hmem
    simp only [hk0, ite_false, List.nil_append, List.mem_filterMap] at hmem
    obtain ⟨o, ho, hos⟩ := hmem
    cases o with
    | save _ _ => cases hos
    | snap m =>
      simp only at hos
      split at hos
      · rename_i hmc
        cases hos
        obtain ⟨j, hj⟩ := List.getElem?_of_mem ho
        rw [List.getElem?_drop] at hj
        have ha : ∃ (i : Nat) (m' : SnapshotMetadataM), I[i]? = some (WalOpG.snap m') ∧
            m'.Index' = m.Index' := ⟨k + j, m, hj, rfl⟩
        have hknb : k ≤ walNameBound I (uint.nat m.Index') false :=
          Nat.le_trans hk (Nat.min_le_right _ _)
        have heq := walReadCut_eq hknb hmax ha hmc hcl h0 hcutk
        subst heq
        exact ⟨σk, h0, e1, e2, hbase⟩
      · cases hos

/-- The oracle with `a` appended to its pending opens (`restartRead`, before each `Open`). -/
def tAddOpen (o : TOracle) (a : w64) : TOracle := { o with opens := o.opens ++ [a] }

theorem tCandHist_addOpen (o : TOracle) (a : w64) (c : TCand) :
    tCandHist (tAddOpen o a) c = tCandHist o c := rfl

theorem tCandMark_addOpen (o : TOracle) (a : w64) (c : TCand) :
    tCandMark (tAddOpen o a) c = tCandMark o c := rfl

theorem foldl_max_mono (l : List Nat) (x y : Nat) (h : x ≤ y) : l.foldl max x ≤ l.foldl max y := by
  induction l generalizing x y with
  | nil => exact h
  | cons z l ih => exact ih _ _ (Nat.max_le.2 ⟨Nat.le_trans h (Nat.le_max_left _ _), Nat.le_max_right _ _⟩)

theorem foldl_max_ge (l : List Nat) (x : Nat) : x ≤ l.foldl max x := by
  induction l generalizing x with
  | nil => exact Nat.le_refl _
  | cons z l ih => exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

/-- The opens bound only grows with an open appended, and bounds the appended one's `openBound`. -/
theorem tOpensBound_addOpen (o : TOracle) (a : w64) (c : TCand) :
    tOpensBound o c ≤ tOpensBound (tAddOpen o a) c ∧
    uint.nat (tOpenBound (tImgs (tCandHist o c) (tCandMark o c)) a) ≤ tOpensBound (tAddOpen o a) c := by
  unfold tOpensBound
  rw [tCandHist_addOpen, tCandMark_addOpen]
  simp only [tAddOpen, List.map_append, List.map_cons, List.map_nil, List.foldl_append, List.foldl_cons,
    List.foldl_nil]
  exact ⟨Nat.le_max_left _ _, Nat.le_max_right _ _⟩

/-- **The opens raise keeps the accounting** (see the file header). -/
theorem tCandOk_open {o : TOracle} {c : TCand} {d : WalDur} (a : w64) (hc : tCandOk o c d)
    (hl : (tCandHist o c).length < 2 ^ 63) :
    tCandOk (tAddOpen o a) c { d with unl := max d.unl (walOpenPos (d.H.map WalOpG.toM) a) } := by
  obtain ⟨himg, hpur, hcut, hunl, hsz, hwf⟩ := hc
  obtain ⟨hob1, hob2⟩ := tOpensBound_addOpen o a c
  refine ⟨himg, hpur, hcut, ?_, hsz, hwf⟩
  show max d.unl (walOpenPos (d.H.map WalOpG.toM) a) ≤ max (uint.nat c.unl) (tOpensBound (tAddOpen o a) c)
  apply Nat.max_le.2
  refine ⟨Nat.le_trans hunl (Nat.max_le.2 ⟨Nat.le_max_left _ _, Nat.le_trans hob1 (Nat.le_max_right _ _)⟩), ?_⟩
  obtain ⟨img, himgm, hI⟩ := tImgs_complete himg
  have hwi : tHistWf img := tHistWf_of_mem_tImgs hwf himgm
  have hil : img.length < 2 ^ 64 := by
    have := walImg_length_le himg
    rw [hI, List.length_map, List.length_map] at this
    omega
  have h1 : walOpenPos (d.H.map WalOpG.toM) a ≤ uint.nat (tNameBound img a) := by
    rw [tNameBound_eq hwi hil, ← hI]
    exact Nat.min_le_right _ _
  have h2 := tNameBound_le_openBound a himgm
  exact Nat.le_trans h1 (Nat.le_trans h2 (Nat.le_trans hob2 (Nat.le_max_right _ _)))

/-! ## The read's entries are the history's -/

theorem tReadEnt_sub {P : TEnt → Prop} {b : w64} {ents : List TEnt} {e : TEnt} {r : List TEnt}
    (h : tReadEnt b ents e = some r) (hents : ∀ x ∈ ents, P x) (he : P e) : ∀ x ∈ r, P x := by
  unfold tReadEnt at h
  split at h
  · cases h; intro x hx; cases hx
  · split at h
    · cases h
    · cases h
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact hents x (List.mem_of_mem_take hx)
      · rw [List.mem_singleton] at hx; subst hx; exact he

theorem tReadEnts_sub {P : TEnt → Prop} (b : w64) : ∀ (es ents r : List TEnt),
    es.foldlM (fun ents e => tReadEnt b ents e) ents = some r →
    (∀ x ∈ ents, P x) → (∀ x ∈ es, P x) → ∀ x ∈ r, P x := by
  intro es
  induction es with
  | nil => intro ents r h hents _; simp at h; subst h; exact hents
  | cons e es ih =>
    intro ents r h hents hes
    simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨r1, h1, h2⟩ := h
    exact ih r1 r h2 (tReadEnt_sub h1 hents (hes e (List.mem_cons_self ..)))
      (fun x hx => hes x (List.mem_cons_of_mem _ hx))

theorem tSaveSnap_ents_sub {P : TEnt → Prop} (s : TContents) (idx term : w64) (hs : ∀ x ∈ s.ents, P x) :
    ∀ x ∈ (tSaveSnap s idx term).ents, P x := by
  unfold tSaveSnap
  split
  · exact hs
  · simp only
    split
    · intro x hx; exact hs x (List.mem_of_mem_drop hx)
    · intro x hx; cases hx

theorem tFoldChkFrom_ents_sub {P : TEnt → Prop} : ∀ (L : List TOp) (s s' : TContents),
    tFoldChkFrom s L = some s' → (∀ x ∈ s.ents, P x) →
    (∀ o ∈ L, o.snap = false → ∀ x ∈ o.ents, P x) → ∀ x ∈ s'.ents, P x := by
  intro L
  induction L with
  | nil => intro s s' h hs _; simp [tFoldChkFrom] at h; subst h; exact hs
  | cons o L ih =>
    intro s s' h hs hL
    unfold tFoldChkFrom at h
    split at h
    · exact ih _ s' h (tSaveSnap_ents_sub s o.idx o.term hs) (fun o' ho' => hL o' (List.mem_cons_of_mem _ ho'))
    · rename_i hsn
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨ents, he, h⟩ := h
      exact ih _ s' h (tReadEnts_sub s.baseIdx o.ents s.ents ents he hs
        (hL o (List.mem_cons_self ..) (by simpa using hsn)))
        (fun o' ho' => hL o' (List.mem_cons_of_mem _ ho'))

/-- **A well-formed history's read holds well-formed entries.** -/
theorem tRead_ents_wf {h : List TOp} {c : TContents} (hw : tHistWf h) (hr : tRead h = some c) :
    ∀ e ∈ c.ents, tEntWf e := by
  unfold tRead tFoldChk at hr
  refine tFoldChkFrom_ents_sub _ tC0 c hr (fun x hx => by cases hx) ?_
  intro o ho hsn x hx
  exact (hw o (List.mem_filter.1 ho).1).2.1 hsn x hx

theorem absHs_inj {a b : THs} (h : absHs a = absHs b) : a = b := by
  cases a; cases b; simp only [absHs, HardStateM.mk.injEq] at h; obtain ⟨h1, h2, h3⟩ := h; subst h1 h2 h3; rfl

/-- **The restart's read passes the check** (`restart`'s `checkRestart` premise): a candidate `cd` accounts
for the WAL state `d` (`tCandOk`); `ReadAll` read `σ'` at the base `s` (`walReadAllOk`); the history reads
back; the tester's read `c` is `σ'` through `toHS`'s getters (`absHs c.hs = σ'.hs`) and `fromRaft`, at the
base `s`. Then the image `d.H` of `cd`'s history reads `c` from the purged prefix 0. -/
theorem tCheckNext_of_read {o : TOracle} {cd : TCand} {d : WalDur} {s : w64 × w64} {σ' : StorContents}
    {c : TContents} (hcd : cd ∈ o.cands) (hc : tCandOk o cd d)
    (hpost : walReadAllOk (d.H.map WalOpG.toM) d.cut s σ') (hb : walReadsBack (d.H.map WalOpG.toM))
    (hhs : absHs c.hs = σ'.hs) (hbi : c.baseIdx = s.1) (hbt : c.baseTerm = s.2)
    (hents : c.ents = σ'.ents.map tFromRaft) : tCheckNext o c ≠ [] := by
  obtain ⟨himg, -, -, -, -, hwf⟩ := hc
  obtain ⟨img, himgm, hI⟩ := tImgs_complete himg
  have hwi : tHistWf img := tHistWf_of_mem_tImgs hwf himgm
  have hmax : ¬ walHasMaxIdx (d.H.map WalOpG.toM) := by rw [hI]; exact tHistWf_noMax hwi
  obtain ⟨σ0, h0, e1, e2, e3⟩ := walReadAllOk_read0 hpost hmax hb
  have hra := tRead_abs img
  rw [← hI, h0] at hra
  cases hr : tRead img with
  | none => rw [hr] at hra; cases hra
  | some c0 =>
    rw [hr] at hra
    simp only [Option.map_some, Option.some.injEq] at hra
    have hc0 : c0 = c := by
      simp only [absC, projC, Prod.mk.injEq] at hra
      obtain ⟨r1, r2, r3, r4⟩ := hra
      have hw0 := tRead_ents_wf hwi hr
      cases c0; cases c
      simp only at r1 r2 r3 r4 hw0 hhs hbi hbt hents ⊢
      rw [e3] at r2 r3
      rw [TContents.mk.injEq]
      refine ⟨absHs_inj (by rw [r1, e1, hhs]), ?_, ?_, ?_⟩
      · rw [r2, hbi]
      · rw [r3, hbt]
      · rw [hents, ← e2, ← r4, List.map_map]
        symm
        rw [List.map_congr_left (g := id) (fun e he => by
          simp only [Function.comp_apply, id]; exact tFromRaft_absEnt e (hw0 e he).1)]
        simp
    subst hc0
    refine tCheckNext_ne_nil hcd himgm ⟨Nat.zero_le _, Nat.zero_le _⟩ ?_
    rw [show (W64 ((0 : Nat) : Int)) = W64 0 from rfl]
    unfold tReadCut; rw [if_pos rfl]; exact hr

end pure

end etcd_wal
end EtcdGrove
end Perennial
