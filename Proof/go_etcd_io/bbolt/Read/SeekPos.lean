/-
The public reader `Seek`'s (U6i, `notes/bbolt-proof-plan.md`) position: the stack `seek` leaves
(`rRoute`, routing `kb` from the bucket's root) is at the entry `seekIdx` names (`rRoute_seekPos`):
the entries before it have keys below `kb` (children before the routed one are below its key,
which is at most `kb`; the leaf's first `pageSeekIdx` keys), those from it on do not (`entSplit`).
-/
module

public import Proof.go_etcd_io.bbolt.Read.Route
public import Proof.go_etcd_io.bbolt.Read.GetFacts

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt


open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section seekPos
variable [GooseExts]
variable {v : View} {bv : List w8} {pp : Loc}

/-- An entry (leaf, index) whose key is below `kb`. -/
def entLt (kb : List w8) (x : List w8 × Nat) : Bool :=
  decide (go.GoStringLt (leafKey x.1 x.2) kb)

/-- The entries `E` split at `i`: the first `i` have keys below `kb`, the others do not. -/
def entSplit (kb : List w8) (E : List (List w8 × Nat)) (i : Nat) : Prop :=
  ∃ A B, E = A ++ B ∧ A.length = i ∧ (∀ x ∈ A, entLt kb x = true) ∧
    (∀ x ∈ B, entLt kb x = false)

theorem takeWhile_entSplit (kb : List w8) (E : List (List w8 × Nat)) (i : Nat)
    (h : entSplit kb E i) : (E.takeWhile (entLt kb)).length = i := by
  obtain ⟨A, B, rfl, rfl, hA, hB⟩ := h
  induction A with
  | nil =>
    cases B with
    | nil => rfl
    | cons b B => simp [List.takeWhile_cons, hB b (by simp)]
  | cons a A ih =>
    have := ih (fun x hx => hA x (by simp [hx]))
    simp [List.takeWhile_cons, hA a (by simp), this]

/-- `takeWhile` stops at an element failing the test. -/
theorem takeWhile_stop {α : Type} (p : α → Bool) : ∀ (l : List α)
    (h : (l.takeWhile p).length < l.length), p (l[(l.takeWhile p).length]) = false
  | [], h => absurd h (by simp)
  | a :: l, h => by
    cases hp : p a with
    | false =>
      have h0 : ((a :: l).takeWhile p).length = 0 := by simp [List.takeWhile_cons, hp]
      simp only [h0, List.getElem_cons_zero]; exact hp
    | true =>
      have h1 : ((a :: l).takeWhile p).length = (l.takeWhile p).length + 1 := by
        simp [List.takeWhile_cons, hp]
      have h' : (l.takeWhile p).length < l.length := by rw [h1] at h; simp at h; omega
      simp only [h1, List.getElem_cons_succ]
      exact takeWhile_stop p l h'

/-- **A leaf's entries split at the search index** (its keys increase). -/
theorem lEnts_split (pg : List w8) (kb : List w8)
    (hs : ∀ i j, i < j → j < pageCount pg → go.GoStringLt (leafKey pg i) (leafKey pg j)) :
    entSplit kb (lEnts pg) (pageSeekIdx pg kb) := by
  let f : Nat → Bool := fun i => decide (go.GoStringLt (leafKey pg i) kb)
  let R := List.range (pageCount pg)
  have ht : pageSeekIdx pg kb = (R.takeWhile f).length := rfl
  have htl : (R.takeWhile f).length ≤ R.length := (List.takeWhile_sublist _).length_le
  have htake : R.take (R.takeWhile f).length = R.takeWhile f :=
    (List.prefix_iff_eq_take.mp (List.takeWhile_prefix f)).symm
  refine ⟨(R.take (pageSeekIdx pg kb)).map (pg, ·), (R.drop (pageSeekIdx pg kb)).map (pg, ·),
    ?_, ?_, ?_, ?_⟩
  · unfold lEnts; rw [← List.map_append, List.take_append_drop]
  · rw [List.length_map, List.length_take, ht]; omega
  · intro x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
    rw [ht, htake] at hj
    exact List.all_eq_true.mp List.all_takeWhile j hj
  · intro x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
    obtain ⟨k, hk, hkj⟩ := List.getElem_of_mem hj
    rw [List.getElem_drop] at hkj
    simp only [R, List.getElem_range] at hkj
    subst hkj
    simp only [List.length_drop, R, List.length_range] at hk
    have hlt : (R.takeWhile f).length < R.length := by simp [R]; rw [← ht]; omega
    have hstop := takeWhile_stop f R hlt
    simp only [R, List.getElem_range] at hstop
    rw [← ht] at hstop
    show decide (go.GoStringLt (leafKey pg (pageSeekIdx pg kb + k)) kb) = false
    apply decide_eq_false
    intro hlt'
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0; simp only [Nat.add_zero] at hlt'
      have : f (pageSeekIdx pg kb) = true := decide_eq_true hlt'
      rw [this] at hstop; cases hstop
    · have h1 := go.goStringLt_trans (hs (pageSeekIdx pg kb) (pageSeekIdx pg kb + k) (by omega)
        (by omega)) hlt'
      have : f (pageSeekIdx pg kb) = true := decide_eq_true h1
      rw [this] at hstop; cases hstop

/-- `flatMap_range_split_bind` with the rest's members: from the children after `j`. -/
theorem flatMap_range_split' {α β : Type} (g : Nat → List α) (f : α → List β) (c j : Nat)
    (hj : j < c) : ∃ D, ((List.range c).flatMap g).flatMap f =
      ((List.range j).flatMap g).flatMap f ++ ((g j).flatMap f ++ D) ∧
      ∀ y ∈ D, ∃ k, j < k ∧ k < c ∧ y ∈ (g k).flatMap f := by
  obtain ⟨d, rfl⟩ : ∃ d, c = (j + 1) + d := ⟨c - (j + 1), by omega⟩
  refine ⟨(((List.range d).map fun x => j + 1 + x).flatMap g).flatMap f, ?_, ?_⟩
  · rw [List.range_add, List.flatMap_append, List.range_succ, List.flatMap_append]
    simp [List.flatMap_append, List.append_assoc]
  · intro y hy
    obtain ⟨a, ha, hya⟩ := List.mem_flatMap.mp hy
    obtain ⟨x, hx, hxa⟩ := List.mem_flatMap.mp ha
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
    rw [List.mem_range] at hz
    exact ⟨j + 1 + z, by omega, by omega, List.mem_flatMap.mpr ⟨a, hxa, hya⟩⟩

/-- **A route in a bucket stored in pages is a stack at the entry splitting the keys below
`kb`** (from a well-formed position with B+tree keys). -/
theorem rRoute_split (kb : List w8) (hi : inBucketRoot bv ≠ 0) (pht : Nat → Nat)
    (hht : pageHts v.pages pht) :
    ∀ (n pid : Nat) (path : List elemRef) (lo hi' : Option (List w8)), pht pid < n →
      (∃ hwm, treeWF v.pages hwm pid) → treeKeys v.pages pid lo hi' →
      rRoute v bv pp kb pid path →
      ∃ i s, rPosF v bv pp n pid path i s ∧ entSplit kb ((leavesF n v.pages pid).flatMap lEnts) i
  | 0, _, _, _, _, hn, _, _, _ => absurd hn (Nat.not_lt_zero _)
  | n + 1, pid, path, lo, hi', hn, ⟨hwm, hw⟩, hk, hr => by
    match path, hr with
    | [e], ⟨pg, hpa, hnode, hfl, hidx⟩ =>
      have hpa0 := hpa
      unfold rPageAt at hpa
      rw [if_neg hi] at hpa
      obtain ⟨pg', hpg, he⟩ := Option.map_eq_some_iff.mp hpa
      simp only [Prod.mk.injEq] at he
      obtain ⟨-, rfl⟩ := he
      have hL : leavesF (n + 1) v.pages pid = [pg'] := by
        simp only [leavesF, hpg, hfl, if_true]
      rw [hL]
      cases hw with
      | page _ pg2 _ _ hpg2 _ _ hpt =>
        rw [hpg] at hpg2; cases hpg2
        cases hpt with
        | leaf _ _ _ hlwf _ =>
          refine ⟨pageSeekIdx pg' kb, _, ⟨pg', ⟨hpa0, hnode, hfl, (pageSeekIdx_le pg' kb).1, hidx⟩,
            rfl⟩, ?_⟩
          simpa using lEnts_split pg' kb hlwf.2.2.2
        | branch _ _ hf _ _ => rw [hfl] at hf; simp [branchPageFlag, leafPageFlag] at hf
    | e :: e' :: es, ⟨pg, hpa, hnode, hfl, hbr, hrt⟩ =>
      have hpa0 := hpa
      unfold rPageAt at hpa
      rw [if_neg hi] at hpa
      obtain ⟨pg', hpg, he⟩ := Option.map_eq_some_iff.mp hpa
      simp only [Prod.mk.injEq] at he
      obtain ⟨-, rfl⟩ := he
      have hnl : ¬ pageFlags pg' = leafPageFlag := by
        rw [hfl]; simp [branchPageFlag, leafPageFlag]
      have hL : leavesF (n + 1) v.pages pid = (List.range (pageCount pg')).flatMap
          fun i => leavesF n v.pages (branchPgid pg' i) := by
        simp only [leavesF, hpg, hnl, if_false]
      rw [hL]
      obtain ⟨r, hr_def⟩ : ∃ r, r = e.index'.toNat := ⟨_, rfl⟩
      rw [← hr_def] at hbr hrt
      have hrc := hbr.1
      cases hw with
      | page _ pg2 _ _ hpg2 _ _ hpt =>
        rw [hpg] at hpg2; cases hpg2
        cases hpt with
        | leaf _ _ hf _ _ => exact absurd hf hnl
        | branch _ _ _ hbwf hch =>
          cases hk with
          | leaf _ pg3 _ _ hpg3 hf3 _ _ =>
            rw [hpg] at hpg3; cases hpg3; exact absurd hf3 hnl
          | branch _ pg3 _ _ kind hpg3 _ _ _ _ hkch =>
            rw [hpg] at hpg3; cases hpg3
            have hht' := (hht pid pg' hpg).2 hfl _ hrc
            obtain ⟨ic, sc, hpc, hsc⟩ := rRoute_split kb hi pht hht n _ (e' :: es) _ _ (by omega)
              ⟨hwm, hch _ hrc⟩ (hkch _ hrc) hrt
            have hs := hbwf.2.2.2.2
            have hix : e.index' = W64 (r : Int) := by
              have := pageCount_lt pg'
              subst hr_def
              apply BitVec.eq_of_toNat_eq
              simp only [BitVec.toNat_ofInt, Int.natCast_pow]
              have h2 : e.index'.toNat < 2 ^ 64 := e.index'.isLt
              rw [Int.toNat_emod (by omega) (by omega)]
              simp; omega
            refine ⟨entsBefore v.pages n pg' r + ic, entsBefore v.pages n pg' r + sc,
              ⟨pg', r, ic, sc, ⟨hi, hpa0, hnode, hfl, hrc, hix⟩, hpc, rfl, rfl⟩, ?_⟩
            obtain ⟨D, hD, hDm⟩ := flatMap_range_split'
              (fun c => leavesF n v.pages (branchPgid pg' c)) lEnts _ r hrc
            rw [hD]
            obtain ⟨A, B, hAB, hAl, hA, hB⟩ := hsc
            refine ⟨((List.range r).flatMap fun c => leavesF n v.pages (branchPgid pg' c)).flatMap
              lEnts ++ A, B ++ D, ?_, ?_, ?_, ?_⟩
            · rw [hAB]; simp [List.append_assoc]
            · rw [List.length_append, hAl]; rfl
            · intro x hx
              rcases List.mem_append.mp hx with hx | hx
              · obtain ⟨pgc, hpgc, hxm⟩ := List.mem_flatMap.mp hx
                obtain ⟨c, hc, hpgc'⟩ := List.mem_flatMap.mp hpgc
                rw [List.mem_range] at hc
                unfold lEnts at hxm
                obtain ⟨idx, hidx, rfl⟩ := List.mem_map.mp hxm
                rw [List.mem_range] at hidx
                have hkin := leavesF_keyIn v.pages n _ _ _ (hkch c (by omega)) pgc hpgc' idx hidx
                have hlt := hkin.2 (branchKey pg' (c + 1)) (by unfold childHi; rw [if_pos (by omega)])
                have hr0 : ¬ go.GoStringLt kb (branchKey pg' r) := by
                  rcases hbr.2.1 with h | h
                  · omega
                  · exact h
                have hle : go.GoStringLt (leafKey pgc idx) (branchKey pg' r) := by
                  rcases Nat.lt_or_ge (c + 1) r with h | h
                  · exact go.goStringLt_trans hlt (hs _ _ h hrc)
                  · rw [show c + 1 = r by omega] at hlt; exact hlt
                show decide (go.GoStringLt (leafKey pgc idx) kb) = true
                exact decide_eq_true (TreeEnts.gs_lt_of_lt_nlt hle hr0)
              · exact hA x hx
            · intro x hx
              rcases List.mem_append.mp hx with hx | hx
              · exact hB x hx
              · obtain ⟨c, hrc', hcc, hxm⟩ := hDm x hx
                obtain ⟨pgc, hpgc, hxm'⟩ := List.mem_flatMap.mp hxm
                unfold lEnts at hxm'
                obtain ⟨idx, hidx, rfl⟩ := List.mem_map.mp hxm'
                rw [List.mem_range] at hidx
                have hkin := leavesF_keyIn v.pages n _ _ _ (hkch c hcc) pgc hpgc idx hidx
                have hge := hkin.1 (branchKey pg' c) (by unfold childLo; rw [if_neg (by omega)])
                have hk1 := hbr.2.2 (by omega)
                show decide (go.GoStringLt (leafKey pgc idx) kb) = false
                apply decide_eq_false
                intro hlt
                apply hge
                have h1 := go.goStringLt_trans hlt hk1
                rcases Nat.lt_or_ge (r + 1) c with h | h
                · exact go.goStringLt_trans h1 (hs _ _ h hcc)
                · rw [show r + 1 = c by omega] at h1; exact h1

/-- **`seek`'s stack is at the entry `seekIdx` names**, in a well-formed reader bucket. -/
theorem rRoute_seekPos (kb : List w8) (hok : rBktOK v bv) (pht : Nat → Nat)
    (hht : pageHts v.pages pht) (els : List elemRef)
    (hr : rRoute v bv pp kb (inBucketRoot bv) els) :
    ∃ s, rPosAt v bv pp els ((rEnts v bv).takeWhile (entLt kb)).length s := by
  have key : ∃ i s, rPosAt v bv pp els i s ∧ entSplit kb (rEnts v bv) i := by
    by_cases hi : inBucketRoot bv = 0
    · rcases hok.2.1 with ⟨_, _, hfl, hwf⟩ | ⟨hi', _⟩
      · rw [hi] at hr
        match els, hr with
        | [e], ⟨pg, hpa, hnode, hfl', hidx⟩ =>
          have hpa0 := hpa
          unfold rPageAt at hpa
          simp only [if_pos hi, if_true, Option.some.injEq, Prod.mk.injEq] at hpa
          obtain ⟨-, rfl⟩ := hpa
          refine ⟨pageSeekIdx (inlinePage bv) kb, if pageSeekIdx (inlinePage bv) kb <
            pageCount (inlinePage bv) then pageSeekIdx (inlinePage bv) kb + 1 else
            pageSeekIdx (inlinePage bv) kb, ?_, ?_⟩
          · unfold rPosAt rFuel
            rw [if_pos hi, hi]
            exact ⟨inlinePage bv, ⟨hpa0, hnode, hfl', (pageSeekIdx_le _ kb).1, hidx⟩, rfl⟩
          · have : rEnts v bv = lEnts (inlinePage bv) := by
              unfold rEnts
              rw [← rLeaves_root]
              unfold rLeaves
              rw [if_pos hi]
              simp
            rw [this]
            exact lEnts_split _ kb hwf.2.2.2
        | e :: e' :: es, ⟨pg, hpa, _, hfl', _, _⟩ =>
          unfold rPageAt at hpa
          simp only [if_pos hi, if_true, Option.some.injEq, Prod.mk.injEq] at hpa
          obtain ⟨_, rfl⟩ := hpa
          rw [hfl] at hfl'; simp [branchPageFlag, leafPageFlag] at hfl'
      · exact absurd hi hi'
    · obtain ⟨hrt, hrh⟩ := rRoot_ok pht hht hok
      rcases hrt with ⟨h, -⟩ | ⟨-, hwm, hw⟩
      · exact absurd h hi
      rcases hrh with h | h
      · exact absurd h hi
      obtain ⟨i, s, hp, hsp⟩ :=
        rRoute_split kb hi pht hht _ _ els none none h ⟨hwm, hw⟩ (hok.2.2 hi) hr
      refine ⟨i, s, hp, ?_⟩
      have : rEnts v bv = (leavesF (rFuel v bv) v.pages (inBucketRoot bv)).flatMap lEnts := by
        unfold rEnts
        rw [← rLeaves_root]
        unfold rLeaves
        rw [if_neg hi]
      rw [this]; exact hsp
  obtain ⟨i, s, hp, hsp⟩ := key
  rw [takeWhile_entSplit kb _ i hsp]
  exact ⟨s, hp⟩

/-- `seekIdx` of a reader bucket's entries, over its positions. -/
theorem seekIdx_rEnts (v : View) (bv : List w8) (kb : List w8) :
    seekIdx (bktEntries v.pages bv) kb = ((rEnts v bv).takeWhile (entLt kb)).length := by
  rw [← rEnts_bktEntries]
  unfold seekIdx
  rw [List.takeWhile_map, List.length_map]
  rfl

end seekPos

end bbolt
end EtcdGrove
end Perennial
