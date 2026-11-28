/-
Lean-first (no Rocq counterpart).

# k8s-dist K4: `FullComplete`

`notes/k8s-dist-k4.md`, "Handoff K4-4", step 6. By induction on the semantic model's run (`SRun`),
the search's configuration related to the cluster's (`CRel`): the silent steps before an operation
are `settle` (`CRel.reach`), then the operation's step from the search skipped to its target: a
watch by `HRel.watchOk`, a failed call as on the cluster, a successful one by `CRel.ok`.

`CRel.ok` (K4-6) first bounds the cluster's answers (`kstepL_target`: the target is at most the
cluster's revision), skips the search there, then gets the same answer by `mlistL_ren` (a list) or
`mstepL_ans_ren` (the rest), and keeps the relation: unchanged stores, or `HRel.write` at the same
revision on both sides (a write that changes the store answers at the next revision on both).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.dist.SharedWatch
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.dist.SharedSettle

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_dist

open k8s_etcd3
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item)

section go
variable [GooseExts]

theorem evMaxL_foldl_le (m : Nat) : ∀ (l : List WEv) (acc : Nat), acc ≤ m →
    (∀ e ∈ l, uint.nat e.o.ResourceVersion' ≤ m) →
    l.foldl (fun t e => max t (uint.nat e.o.ResourceVersion')) acc ≤ m
  | [], _, ha, _ => ha
  | e :: l, acc, ha, he => by
    rw [List.foldl_cons]
    exact evMaxL_foldl_le m l _ (by have := he e List.mem_cons_self; omega)
      (fun e' h' => he e' (List.mem_cons_of_mem _ h'))

/-- **A watch the cluster allows has its target at most the cluster's revision.** -/
theorem watchOkL_target (x : Input) (y : Output) (h : HSt) (hk : x.Kind' = W64 5) (r : Nat)
    (hok : watchOkL x y h = true) : targetL x y r ≤ uint.nat h.st.rv := by
  unfold targetL; rw [if_pos hk]
  unfold watchOkL at hok
  by_cases hf : (y.WFailed' || x.Skip') = true
  · rw [if_pos hf]; exact Nat.zero_le _
  rw [if_neg hf] at hok ⊢
  rcases hd : decWEventsL y.WEvents' with _ | all
  · exact Nat.zero_le _
  rw [hd] at hok
  dsimp only at hok ⊢
  by_cases h5 : all.any (fun e => 5 ≤ e.t) = true
  · rw [if_pos h5] at hok; cases hok
  rw [if_neg h5] at hok
  have h5' : ∀ e ∈ all, e.t < 5 := fun e he => by
    have := List.any_eq_false.mp (Bool.eq_false_iff.mpr h5) e he; simp at this; omega
  by_cases hrc : (all.filter fun e => e.t ≠ 4).any
      (fun e => uint.nat h.st.rv < uint.nat e.o.ResourceVersion') = true
  · rw [if_pos hrc] at hok; cases hok
  rw [if_neg hrc] at hok
  have hle : ∀ e ∈ all, e.t < 4 → uint.nat e.o.ResourceVersion' ≤ uint.nat h.st.rv := fun e he ht => by
    have := List.any_eq_false.mp (Bool.eq_false_iff.mpr hrc) e
      (List.mem_filter.mpr ⟨he, by simp; omega⟩)
    simp at this; omega
  have hmax : evMaxL all ≤ uint.nat h.st.rv :=
    evMaxL_foldl_le _ _ 0 (Nat.zero_le _) (fun e he => by
      have he' := List.mem_filter.mp he
      exact hle e he'.1 (by simpa using he'.2))
  by_cases hsi : x.SendInit' = W64 2 ∧ all.any (fun e => e.t < 4) = true
  · rw [if_pos hsi]
    rcases hp : parseRVD x.MinRV' with _ | req
    · exact hmax
    dsimp only
    refine Nat.max_le.mpr ⟨hmax, ?_⟩
    obtain ⟨e0, he0, ht0⟩ := List.any_eq_true.mp hsi.2
    have hne : (all.filter fun e => e.t ≠ 4) ≠ [] := by
      intro hnil
      have : e0 ∈ all.filter (fun e => e.t ≠ 4) := List.mem_filter.mpr ⟨he0, by simp at ht0 ⊢; omega⟩
      rw [hnil] at this; cases this
    generalize all.filter (fun e => e.t ≠ 4) = evs at hok hne
    by_cases hbm : (!bookmarksOkL evs) = true
    · rw [if_pos hbm] at hok; cases hok
    rw [if_neg hbm, hp] at hok
    dsimp only at hok
    rw [if_pos hsi.1] at hok
    rcases hb : evs.findIdx? (fun e => e.t = 3) with _ | b
    · rw [hb] at hok
      unfold initialPrefixOkL at hok
      have he : evs.isEmpty = false := by cases evs; exact absurd rfl hne; rfl
      rw [he, Bool.false_or] at hok
      obtain ⟨r', hr', _⟩ := List.any_eq_true.mp hok
      have := List.mem_range'_1.mp hr'
      omega
    · rw [hb] at hok
      dsimp only at hok
      generalize evs.getD b ⟨0, ⟨[], [], [], [], [], [], 0, false⟩⟩ = bm at hok
      by_cases ha : (!bm.o.Annotated') = true
      · rw [if_pos ha] at hok; cases hok
      rw [if_neg ha] at hok
      by_cases hc1 : (uint.nat req ≠ 0 ∧ uint.nat bm.o.ResourceVersion' < uint.nat req) ∨
          uint.nat bm.o.ResourceVersion' < 1 ∨ uint.nat h.st.rv < uint.nat bm.o.ResourceVersion'
      · rw [if_pos hc1] at hok; cases hok
      omega
  · rw [if_neg hsi]; exact hmax

/-! ## The cluster's answers are bounded -/

/-- A "not found" names the store's revision. -/
theorem mstepL_nf (x : Input) (st : GSt) (h : (mstepL x st).2.Err' = W64 1) :
    (mstepL x st).2.ErrRV' = st.rv := by
  revert h
  rcases hq : parseRVD x.MinRV' with _ | req <;>
    simp only [mstepL, mcreateL, mdeleteL, mupdateL, mgetL, hq] <;>
    repeat' split
  all_goals
    simp only [notFoundL, errOutL, existsL, invalidObjL, invalidOutL, rejectedL, otherL, tooLargeL,
      zeroOutL, objOutL]
    first | (intro; trivial) | (intro; rfl) | (intro h; exact absurd h (by decide))

/-- A successful write answers at most the next revision, when the store's items are at most its
revision. -/
theorem mstepL_wr (x : Input) (st : GSt)
    (hit : ∀ it ∈ st.items, uint.nat it.obj'.ResourceVersion' ≤ uint.nat st.rv)
    (hb : uint.nat st.rv + 1 < 2 ^ 64) (h : (mstepL x st).2.Err' = W64 0) :
    uint.nat (mstepL x st).2.RV' ≤ uint.nat st.rv + 1 := by
  have hs : uint.nat (st.rv + W64 1) = uint.nat st.rv + 1 := by word
  revert h
  rcases hq : parseRVD x.MinRV' with _ | req <;>
    simp only [mstepL, mcreateL, mdeleteL, mupdateL, mgetL, hq] <;>
    repeat' split
  all_goals
    simp only [notFoundL, errOutL, existsL, invalidObjL, invalidOutL, rejectedL, otherL, tooLargeL,
      zeroOutL, objOutL]
    first
    | (intro h; exact absurd h (by decide))
    | (intro; omega)
    | (intro; rename_i hh; have := hit _ (lookupL_mem _ _ hh.1); omega)
    | (intro; simp; done)
    | (intro; have hl : (lookupL st.items x.Key').snd = true := (by simp_all)
       have := hit _ (lookupL_mem _ _ hl); omega)

/-- A successful read's minimum revision is at most the store's. -/
theorem mstepL_rd (x : Input) (st : GSt) (hw : isWriteL x = false) (h : (mstepL x st).2.Err' = W64 0)
    (req : w64) (hq : parseRVD x.MinRV' = some req) : uint.nat req ≤ uint.nat st.rv := by
  have h0 : x.Kind' ≠ W64 0 := by intro e; simp [isWriteL, e] at hw
  have h1 : x.Kind' ≠ W64 1 := by intro e; simp [isWriteL, e] at hw
  have h2 : x.Kind' ≠ W64 2 := by intro e; simp [isWriteL, e] at hw
  simp only [mstepL, h0, h1, h2, if_false, mgetL, hq] at h
  by_cases hl : uint.nat st.rv < uint.nat req
  · rw [if_pos hl] at h; exact absurd h (by simp [tooLargeL, errOutL])
  · omega

/-- The cluster's current items carry revisions at most its own. -/
theorem HRel.items_le {A : List Nat} {n0 : Nat} {ρ : Nat → Nat} {W : List Nat} {s c : HSt}
    (h : HRel A n0 ρ W s c) (it : item) (hi : it ∈ c.st.items) :
    uint.nat it.obj'.ResourceVersion' ≤ uint.nat c.st.rv := by
  rw [h.cur] at hi
  obtain ⟨it0, hi0, rfl⟩ := List.mem_map.mp hi
  have hs := h.stored_cur it0 hi0
  have hf := h.fits _ hs
  have h1 := (h.stored_cut _ hs).2
  have h2 := h.stored_le _ hs
  have h3 := h.le
  simp only [renItem, renObj]
  generalize ρ (uint.nat it0.obj'.ResourceVersion') = n at hf h1 ⊢
  have : uint.nat (W64 (n : Int)) = n := by word
  omega

/-- **A successful list's revisions are at most the store's**: a past read's, and the answer's. -/
theorem mlistL_bound (x : Input) (c : HSt) (h : (mlistL x c).Err' = W64 0) (req : w64)
    (hq : parseRVD x.MinRV' = some req) :
    uint.nat req ≤ uint.nat c.st.rv ∧ (pastReadL x req = false → (mlistL x c).ListRV' = c.st.rv) := by
  unfold mlistL at h ⊢
  rw [hq] at h ⊢
  dsimp only at h ⊢
  by_cases hl : uint.nat c.st.rv < uint.nat req
  · rw [if_pos hl] at h; exact absurd h (by simp [tooLargeL, errOutL])
  rw [if_neg hl] at h ⊢
  refine ⟨by omega, fun hp => ?_⟩
  cases hpk : k8s.prepareKeyM go!"/objs" x.ListKey' x.Recursive' with
  | none => rw [hpk] at h; exact absurd h (by simp [otherL, errOutL])
  | some pre =>
    rw [hpk] at h
    dsimp only at h ⊢
    rw [(listOutL_ok _ _ _ _ (by rw [h]; decide)).2.2]
    unfold listStL; rw [hp]; rfl

/-- A list's answer has no "not found". -/
theorem mlistL_nf (x : Input) (c : HSt) : (mlistL x c).Err' ≠ W64 1 := by
  unfold mlistL
  rcases parseRVD x.MinRV' with _ | req
  · simp [otherL, errOutL]
  dsimp only
  split
  · simp [tooLargeL, errOutL]
  rcases k8s.prepareKeyM go!"/objs" x.ListKey' x.Recursive' with _ | pre
  · simp [otherL, errOutL]
  dsimp only
  intro e
  have := (listOutL_ok _ _ _ _ (by rw [e]; decide)).2.1
  rw [this] at e; exact absurd e (by decide)

/-- **The cluster's answer's target is at most its revision.** -/
theorem kstepL_target (x : Input) (y : Output) (c : HSt)
    (hit : ∀ it ∈ c.st.items, uint.nat it.obj'.ResourceVersion' ≤ uint.nat c.st.rv)
    (hb : uint.nat c.st.rv + 1 < 2 ^ 64) (hk : x.Kind' ≠ W64 5) (hy : y = (kstepL x c).2) (r : Nat) :
    targetL x y r ≤ uint.nat c.st.rv := by
  unfold targetL
  rw [if_neg hk]
  by_cases h4 : x.Kind' = W64 4
  · have hy' : y = mlistL x c := by rw [hy]; unfold kstepL; rw [if_pos h4]
    rw [if_neg (by rw [hy']; exact mlistL_nf x c)]
    by_cases h0 : y.Err' = W64 0
    · rw [if_neg (by rw [h0]; simp), if_pos h4]
      rcases hq : parseRVD x.MinRV' with _ | req
      · exact Nat.zero_le _
      dsimp only
      have hbd := mlistL_bound x c (by rw [← hy']; exact h0) req hq
      split
      · exact hbd.1
      · next hp => rw [hy', hbd.2 (by simpa using hp)]; exact Nat.le_refl _
    · rw [if_pos h0]; exact Nat.zero_le _
  have hy' : y = (mstepL x c.st).2 := by rw [hy]; unfold kstepL; rw [if_neg h4]
  by_cases h1 : y.Err' = W64 1
  · rw [if_pos h1, hy', mstepL_nf x c.st (by rw [← hy']; exact h1)]; exact Nat.le_refl _
  rw [if_neg h1]
  by_cases h0 : y.Err' = W64 0
  · rw [if_neg (by rw [h0]; simp), if_neg h4]
    split
    · have := mstepL_wr x c.st hit hb (by rw [← hy']; exact h0)
      rw [← hy'] at this
      split <;> omega
    · next hw =>
      rcases hq : parseRVD x.MinRV' with _ | req
      · exact Nat.zero_le _
      dsimp only
      exact mstepL_rd x c.st (by simp only [isWriteL]; simpa using hw) (by rw [← hy']; exact h0) req hq
  · rw [if_pos h0]; exact Nat.zero_le _

/-- A failed list (not `EOther`) fails alike on a store at most as new: its revision is too large. -/
theorem mlistL_err (x : Input) (s c : HSt) (hle : uint.nat s.st.rv ≤ uint.nat c.st.rv)
    (h0 : (mlistL x c).Err' ≠ W64 0) (h4 : (mlistL x c).Err' ≠ W64 4) : mlistL x s = mlistL x c := by
  unfold mlistL at h0 h4 ⊢
  rcases hq : parseRVD x.MinRV' with _ | req
  · rfl
  rw [hq] at h0 h4
  dsimp only at h0 h4 ⊢
  by_cases hl : uint.nat c.st.rv < uint.nat req
  · rw [if_pos hl, if_pos (by omega)]
  · rw [if_neg hl] at h0 h4
    exfalso
    cases hpk : k8s.prepareKeyM go!"/objs" x.ListKey' x.Recursive' with
    | none => rw [hpk] at h4; exact h4 (by simp [otherL, errOutL])
    | some pre =>
      rw [hpk] at h0 h4
      dsimp only at h0 h4
      exact h0 (listOutL_ok _ _ _ _ h4).2.1

section rel
variable {A : List Nat} {n0 : Nat}

/-- **A successful operation other than a watch**, from the search's configuration `d` skipped to its
target, answers as the cluster's and keeps the relation (`notes/k8s-dist-k4.md`, "Handoff K4-5"). -/
theorem CRel.ok (hn0 : 1 ≤ n0) {d g : GCfg} (hc : CRel A n0 d g) (hnw : NoWrap g) (x : Input) (y : Output)
    (hk : x.Kind' ≠ W64 5) (hy : y = (kstepL x g.st).2) (h4 : y.Err' ≠ W64 4) (hanc : OpAnchors A x y) :
    ∃ e', e' ∈ stepL ⟨skipToL d.st (targetL x y (uint.nat d.st.st.rv)), d.pend⟩ x y ∧
      CRel A n0 e' ⟨(kstepL x g.st).1, g.pend⟩ := by
  obtain ⟨⟨ρ, W, h⟩, hp, hpw, hpa⟩ := hc
  have hT := kstepL_target x y g.st h.items_le hnw hk hy (uint.nat d.st.st.rv)
  have hlt : uint.nat g.st.st.rv < 2 ^ 64 := by word
  have hsrv := skipToL_rv d.st (targetL x y (uint.nat d.st.st.rv)) (by omega)
  have h' := h.skipTo _ hT
  generalize hTd : targetL x y (uint.nat d.st.st.rv) = T at hT hsrv h' ⊢
  generalize skipToL d.st T = s at hsrv h' ⊢
  have hTs : T ≤ uint.nat s.st.rv := by rw [hsrv]; exact Nat.le_max_right _ _
  have hds : uint.nat d.st.st.rv ≤ uint.nat s.st.rv := by rw [hsrv]; exact Nat.le_max_left _ _
  have hk5 := hanc.2.2.2 hk
  have hpre : x.HasPreRV' = true → ∀ r, parseRVD x.PreRV' = some r → uint.nat r ∈ A :=
    fun hp r hr => hanc.2.1 r hp hr
  unfold targetL at hTd
  rw [if_neg hk] at hTd
  suffices ∃ ρ' W', (kstepL x s).2 = (kstepL x g.st).2 ∧
      HRel A n0 ρ' W' (kstepL x s).1 (kstepL x g.st).1 by
    obtain ⟨ρ', W', he, hr⟩ := this
    refine ⟨⟨(kstepL x s).1, d.pend⟩, ?_, ⟨⟨ρ', W', hr⟩, hp, hpw, hpa⟩⟩
    unfold stepL
    rw [if_neg hk, if_neg h4, if_pos (by rw [hy]; exact he.symm)]
    exact List.mem_singleton_self _
  by_cases h4k : x.Kind' = W64 4
  · -- a list: both stores unchanged
    have hks : ∀ c, kstepL x c = (c, mlistL x c) := fun c => by unfold kstepL; rw [if_pos h4k]
    have hyl : y = mlistL x g.st := by rw [hy, hks]
    rw [hks, hks]
    refine ⟨ρ, W, ?_, h'⟩
    dsimp only
    by_cases h0 : y.Err' = W64 0
    · refine mlistL_ren h' x (by rw [← hyl]; exact h4) hanc.1
        (fun os ho => hk5.2.2.2.1 h4k h0 os (by rw [hyl]; exact ho)) ?_
      intro _ req hq
      have e : T = (if pastReadL x req then uint.nat req else uint.nat y.ListRV') := by
        rw [← hTd, if_neg (by rw [h0]; decide), if_neg (by rw [h0]; simp), if_pos h4k]
        simp only [hq]
      rw [← hyl, ← e]; exact hTs
    · exact mlistL_err x s g.st h'.le (by rw [← hyl]; exact h0) (by rw [← hyl]; exact h4)
  -- a write or a read
  have hks : ∀ c, kstepL x c = (advanceL c (mstepL x c.st).1, (mstepL x c.st).2) := fun c => by
    unfold kstepL; rw [if_neg h4k]
  have hy' : y = (mstepL x g.st.st).2 := by rw [hy, hks]
  have hcur := h'.cur
  have hgst : g.st.st = ⟨s.st.items.map (renItem ρ), g.st.st.rv⟩ := by rw [← hcur]
  have hans : (mstepL x s.st).2 = (mstepL x g.st.st).2 := by
    have := mstepL_ans_ren (A := A) (ρ := ρ) (x := x) (its := s.st.items) (a := s.st.rv)
      (b := g.st.st.rv) ?_
    · rw [hgst]; exact this
    rw [← hgst, ← hy']
    exact {
      zero := h'.ρ_id 0 (Nat.zero_le _)
      cut := fun it hi => (h'.stored_cut _ (h'.stored_cur it hi)).1
      fits := fun it hi => h'.fits _ (h'.stored_cur it hi)
      pre := hpre
      le := h'.le
      b_lt := hnw
      rvA := hk5.2.2.1
      msgA := hk5.2.2.2.2
      nf := fun h1 => by
        have e : T = uint.nat y.ErrRV' := by rw [← hTd, if_pos h1]
        omega
      wr := fun h0 hw => by
        have hk012 : x.Kind' = W64 0 ∨ x.Kind' = W64 1 ∨ x.Kind' = W64 2 := by
          simpa [isWriteL] using hw
        have e : T = (if uint.nat d.st.st.rv < uint.nat y.RV' then uint.nat y.RV' - 1 else 0) := by
          rw [← hTd, if_neg (by rw [h0]; decide), if_neg (by rw [h0]; simp), if_neg h4k, if_pos hk012]
        split at e <;> omega
      rd := fun h0 hw req hq => by
        have hk012 : ¬(x.Kind' = W64 0 ∨ x.Kind' = W64 1 ∨ x.Kind' = W64 2) := by
          simpa [isWriteL] using hw
        have e : T = uint.nat req := by
          rw [← hTd, if_neg (by rw [h0]; decide), if_neg (by rw [h0]; simp), if_neg h4k, if_neg hk012]
          simp only [hq]
        omega }
  rw [hks, hks]
  dsimp only
  by_cases hw : isWriteL x = true
  · obtain ⟨-, hrv⟩ := h'.stepRen x hpre hnw
    by_cases hch : (mstepL x s.st).1.rv = s.st.rv
    · -- a write with no effect: both stores unchanged
      have hcc : (mstepL x g.st.st).1.rv = g.st.st.rv := by
        rcases hrv with ⟨_, e⟩ | ⟨e, _⟩
        · exact e
        · exact absurd (e.symm.trans hch) (rv_succ_ne _)
      have hs1 : (mstepL x s.st).1 = s.st :=
        (mstepL_shape x s.st).resolve_right (fun e => rv_succ_ne _ (e.1.symm.trans hch))
      have hc1 : (mstepL x g.st.st).1 = g.st.st :=
        (mstepL_shape x g.st.st).resolve_right (fun e => rv_succ_ne _ (e.1.symm.trans hcc))
      refine ⟨ρ, W, hans, ?_⟩
      rw [advanceL_same _ _ hs1, advanceL_same _ _ hc1]; exact h'
    · -- a write that changes the store: at the cluster's revision on both sides
      have hcc : (mstepL x g.st.st).1.rv ≠ g.st.st.rv := by
        rcases hrv with ⟨e, _⟩ | ⟨_, e⟩
        · exact absurd e hch
        · rw [e]; exact rv_succ_ne _
      have hS := mstepL_changed x s.st hch
      have hC := mstepL_changed x g.st.st hcc
      have heq : uint.nat s.st.rv = uint.nat g.st.st.rv := by
        have e := congrArg Output.RV' hans
        rw [hS.2.2, hC.2.2] at e
        have := h'.le
        have : uint.nat (s.st.rv + W64 1) = uint.nat (g.st.st.rv + W64 1) := by rw [e]
        word
      refine ⟨_, _, hans, h'.write x hpre hnw hch fun v _ => ?_⟩
      dsimp only
      rw [heq]
      exact ⟨Iff.rfl, Iff.rfl⟩
  · -- a read: both stores unchanged
    have hw' : isWriteL x = false := by simpa using hw
    have e1 := kstepL_nonwrite x s hw'
    have e2 := kstepL_nonwrite x g.st hw'
    rw [hks] at e1 e2
    dsimp only at e1 e2
    exact ⟨ρ, W, hans, by rw [e1, e2]; exact h'⟩

/-- A failed call's target is 0. -/
theorem targetL_err (x : Input) (y : Output) (r : Nat) (hk : x.Kind' ≠ W64 5) (h4 : y.Err' = W64 4) :
    targetL x y r = 0 := by
  unfold targetL
  rw [if_neg hk, if_neg (by rw [h4]; decide), if_pos (by rw [h4]; decide)]

/-- **One operation**: the cluster's silent steps, then its step, are a step of the search. -/
theorem CRel.op (hn0 : 1 ≤ n0) {h0 : HSt} {e g g₁ g₂ : GCfg} {x : Input} {y : Output}
    (hc : CRel A n0 e g) (hr : SReach h0 g g₁) (hnw : NoWrap g₁)
    (hps : linkv.PStep (kSpec h0) g₁ x (ansOf y) g₂) (hanc : OpAnchors A x y) :
    ∃ e', SearchStep A e x y e' ∧ CRel A n0 e' g₂ := by
  obtain ⟨d, hsd, hcd⟩ := CRel.reach hr hc
  suffices ∃ e', e' ∈ stepL ⟨skipToL d.st (targetL x y (uint.nat d.st.st.rv)), d.pend⟩ x y ∧
      CRel A n0 e' g₂ by
    obtain ⟨e', he', hc'⟩ := this; exact ⟨e', ⟨d, hsd, he'⟩, hc'⟩
  generalize ha : ansOf y = a at hps
  unfold ansOf at ha
  cases hps with
  | ok ho =>
    have hk : x.Kind' ≠ W64 5 := by simpa using ho
    split at ha
    · cases ha
    · next h4 =>
      cases ha
      exact hcd.ok hn0 hnw x _ hk rfl h4 hanc
  | errW hw ho =>
    have hk : x.Kind' ≠ W64 5 := by simpa using ho
    split at ha
    · next h4 =>
      obtain ⟨⟨ρ, W, h⟩, hp, hpw, hpa⟩ := hcd
      refine ⟨⟨d.st, x :: d.pend⟩, ?_, ⟨⟨ρ, W, h⟩, hp.cons x, ?_, ?_⟩⟩
      · rw [targetL_err x y _ hk h4, skipToL_le _ _ (Nat.zero_le _)]
        unfold stepL; rw [if_neg hk, if_pos h4, if_pos hw]; exact List.mem_singleton_self _
      · intro i hi; rcases List.mem_cons.mp hi with rfl | hi
        · exact hw
        · exact hpw i hi
      · intro i hi; rcases List.mem_cons.mp hi with rfl | hi
        · exact fun hp r => hanc.2.1 r hp
        · exact hpa i hi
    · cases ha
  | errR hw ho =>
    have hk : x.Kind' ≠ W64 5 := by simpa using ho
    split at ha
    · next h4 =>
      refine ⟨d, ?_, hcd⟩
      rw [targetL_err x y _ hk h4, skipToL_le _ _ (Nat.zero_le _)]
      unfold stepL; rw [if_neg hk, if_pos h4, if_neg (by simpa using hw)]; exact List.mem_singleton_self _
    · cases ha
  | obs o hob hoo =>
    have hk : x.Kind' = W64 5 := by simpa using hob
    have hoy : o = y := by
      split at ha
      · cases ha
      · cases ha; rfl
    subst hoy
    have hw : watchOkL x o g₁.st = true := hoo
    obtain ⟨⟨ρ, W, h⟩, hp, hpw, hpa⟩ := hcd
    have ht := watchOkL_target x o g₁.st hk (uint.nat d.st.st.rv) hw
    have h' := h.skipTo _ ht
    have hlt : uint.nat g₁.st.st.rv < 2 ^ 64 := by word
    have hsrv := skipToL_rv d.st (targetL x o (uint.nat d.st.st.rv)) (by omega)
    have ht0 : targetL x o 0 = targetL x o (uint.nat d.st.st.rv) := by unfold targetL; rw [if_pos hk, if_pos hk]
    have hws := h'.watchOk hn0 x o hanc hk (by rw [ht0, hsrv]; exact Nat.le_max_right _ _) hw
    refine ⟨⟨skipToL d.st (targetL x o (uint.nat d.st.st.rv)), d.pend⟩, ?_, ⟨⟨ρ, W, h'⟩, hp, hpw, hpa⟩⟩
    unfold stepL; rw [if_pos hk, if_pos hws]; exact List.mem_singleton_self _

end rel

/-- **K4's theorem**: the full mode's search is complete for the shared model. -/
theorem fullComplete : FullComplete := by
  intro h0 A ops c' hlen hlast hseed _ hA hrun
  have hn0 : 1 ≤ uint.nat h0.st.rv := by
    rw [← hlen]
    cases hh : h0.hist with
    | nil => rw [hh] at hlast; cases hlast
    | cons _ _ => simp
  have hinit : CRel A (uint.nat h0.st.rv) ⟨h0, []⟩ ⟨h0, []⟩ :=
    ⟨⟨id, [], HRel.init h0 hlen hlast hseed⟩, List.Perm.refl _, by simp, by simp⟩
  have main : ∀ c ops c', SRun h0 c ops c' → ∀ e, CRel A (uint.nat h0.st.rv) e c →
      (∀ p ∈ ops, OpAnchors A p.1 p.2) → SearchRun A e ops := by
    intro c ops c' hr
    induction hr with
    | nil => intro e _ _; exact .nil _
    | cons hre hnw hps _ ih =>
      intro e hc hops
      obtain ⟨e', hst, hc'⟩ := hc.op hn0 hre hnw hps (hops _ List.mem_cons_self)
      exact .cons hst (ih e' hc' (fun p hp => hops p (List.mem_cons_of_mem _ hp)))
  exact main _ _ _ hrun _ hinit hA.2

end go

end k8s_dist
end EtcdGrove
end Perennial
