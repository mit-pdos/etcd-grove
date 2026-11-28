/-
Lean-first (no Rocq counterpart).

# k8s-dist K4: a list on related histories

`notes/k8s-dist-k4.md`, "Handoff K4-3", step 3. On the search's history `s` and the cluster's `c`,
related by `HRel`, a list answers the same (`mlistL_ren`), given the operation's anchors (its minimum
revision, the items it shows) and the search's target (a past read's revision, or the current
revision the answer shows, at most the search's). A past read at the anchor `req`: the stores at `req`
on both sides are a pair (`CutW`), so renamed; the current read: the target puts the search at the
cluster's revision. The list loop reads keys and selectors only (`listLoopL_ren`), and the objects it
shows are anchored, so not renamed (`renObj_fix`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.dist.SharedHist

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

/-! ## The loop on renamed items -/

/-- A loop state with its objects mapped. -/
def mapLS (f : Obj → Obj) (s : ListModel.LState w8 Obj) : ListModel.LState w8 Obj :=
  { s with items := s.items.map f }

theorem foldl_lstep_map (sel : Obj → Bool) (limit : Nat) (f : Obj → Obj) (hf : ∀ o, sel (f o) = sel o) :
    ∀ (sc : List (List w8 × Obj)) (s : ListModel.LState w8 Obj),
      (sc.map fun ko => (ko.1, f ko.2)).foldl (ListModel.lstep sel limit) (mapLS f s) =
        mapLS f (sc.foldl (ListModel.lstep sel limit) s)
  | [], _ => rfl
  | ko :: sc, s => by
    simp only [List.map_cons, List.foldl_cons]
    rw [← foldl_lstep_map sel limit f hf sc]
    congr 1
    simp only [ListModel.lstep, mapLS, List.length_map, hf]
    split
    · rfl
    · split <;> rfl

/-- **The list loop on renamed items** is the loop with its objects renamed. -/
theorem listLoopL_ren (ρ : Nat → Nat) (x : Input) (its : List item) :
    listLoopL x (its.map (renItem ρ)) = mapLS (renObj ρ) (listLoopL x its) := by
  unfold listLoopL ListModel.loop
  have : scopeL x (its.map (renItem ρ)) = (scopeL x its).map fun ko => (ko.1, renObj ρ ko.2) := by
    unfold scopeL
    simp only [List.filter_map, List.map_map]
    rfl
  rw [this]
  exact foldl_lstep_map _ _ _ (fun o => selOkL_ren ρ x o) _ ⟨[], none, false, 0⟩

theorem foldl_lstep_items (sel : Obj → Bool) (limit : Nat) :
    ∀ (sc : List (List w8 × Obj)) (s : ListModel.LState w8 Obj) (o : Obj),
      o ∈ (sc.foldl (ListModel.lstep sel limit) s).items → o ∈ s.items ∨ ∃ ko ∈ sc, ko.2 = o
  | [], _, _, h => Or.inl h
  | ko :: sc, s, o, h => by
    rw [List.foldl_cons] at h
    rcases foldl_lstep_items sel limit sc _ o h with h | ⟨k, hk, e⟩
    · simp only [ListModel.lstep] at h
      split at h
      · exact Or.inl h
      · split at h
        · rcases List.mem_cons.mp h with e | h
          · exact Or.inr ⟨ko, List.mem_cons_self, e.symm⟩
          · exact Or.inl h
        · exact Or.inl h
    · exact Or.inr ⟨k, List.mem_cons_of_mem _ hk, e⟩

/-- The loop's objects are the store's. -/
theorem listLoopL_items (x : Input) (its : List item) (o : Obj) (h : o ∈ (listLoopL x its).items) :
    ∃ it ∈ its, it.obj' = o := by
  unfold listLoopL ListModel.loop at h
  rcases foldl_lstep_items _ _ _ _ o h with h | ⟨ko, hk, e⟩
  · cases h
  · unfold scopeL at hk
    obtain ⟨hk, -⟩ := List.mem_filter.mp hk
    obtain ⟨it, hi, rfl⟩ := List.mem_map.mp hk
    exact ⟨it, hi, e⟩

/-- A list's answer that is not `EOther` is a success showing the loop's objects at the store's
revision. -/
theorem listOutL_ok (x : Input) (st : GSt) (l : ListModel.LState w8 Obj) (p : GoString)
    (h : (listOutL x st l p).Err' ≠ W64 4) :
    (listOutL x st l p).Items' = encItemsL l.items.reverse ∧ (listOutL x st l p).Err' = W64 0 ∧
      (listOutL x st l p).ListRV' = st.rv := by
  unfold listOutL at h ⊢
  dsimp only at h ⊢
  split <;> (try split) <;> simp_all [otherL, errOutL]

/-- **A list's answer on renamed stores** at the same revision: the same, when the objects it shows
are anchors. -/
theorem listOutL_ren (A : List Nat) (ρ : Nat → Nat) (x : Input) (S C : GSt) (p : GoString)
    (hC : C.items = S.items.map (renItem ρ)) (hrv : S.rv = C.rv)
    (hcut : ∀ it ∈ S.items, CutW A ρ (uint.nat it.obj'.ResourceVersion') ∧
      ρ (uint.nat it.obj'.ResourceVersion') < 2 ^ 64)
    (hne : (listOutL x C (listLoopL x C.items) p).Err' ≠ W64 4)
    (hA : ∀ os : List Obj, (listOutL x C (listLoopL x C.items) p).Items' = encItemsL os →
      ∀ o ∈ os, uint.nat o.ResourceVersion' ∈ A) :
    listOutL x S (listLoopL x S.items) p = listOutL x C (listLoopL x C.items) p := by
  rw [hC, listLoopL_ren] at hne hA ⊢
  have hfix : (listLoopL x S.items).items.map (renObj ρ) = (listLoopL x S.items).items := by
    have hA' := hA ((listLoopL x S.items).items.map (renObj ρ)).reverse
    refine (List.map_congr_left (g := id) fun o ho => ?_).trans (List.map_id _)
    obtain ⟨it, hi, rfl⟩ := listLoopL_items x S.items o ho
    refine renObj_fix _ (hcut it hi).1 (hcut it hi).2 ?_
    have := (listOutL_ok _ _ _ _ hne).1
    simp only [mapLS] at this
    exact hA' this _ (List.mem_reverse.mpr (List.mem_map_of_mem ho))
  unfold listOutL
  simp only [mapLS, hfix, hrv]

/-- **A list on related histories** (`notes/k8s-dist-k4.md`, "Handoff K4-3", step 3): the search's
answers what the cluster's does, given the list's anchors (its minimum revision, the objects it
shows) and its target (a past read's revision, or the current one, at most the search's). -/
theorem mlistL_ren {A : List Nat} {n0 : Nat} {ρ : Nat → Nat} {W : List Nat} {s c : HSt}
    (h : HRel A n0 ρ W s c) (x : Input)
    (hne : (mlistL x c).Err' ≠ W64 4)
    (hmin : ∀ r, parseRVD x.MinRV' = some r → uint.nat r ∈ A)
    (hA : ∀ os : List Obj, (mlistL x c).Items' = encItemsL os → ∀ o ∈ os, uint.nat o.ResourceVersion' ∈ A)
    (htgt : (mlistL x c).Err' = W64 0 → ∀ req, parseRVD x.MinRV' = some req →
      (if pastReadL x req then uint.nat req else uint.nat (mlistL x c).ListRV') ≤ uint.nat s.st.rv) :
    mlistL x s = mlistL x c := by
  have hle := h.le
  unfold mlistL at hne hA htgt ⊢
  cases hq : parseRVD x.MinRV' with
  | none => rfl
  | some req =>
    simp only [hq] at hne hA htgt ⊢
    by_cases hb : uint.nat c.st.rv < uint.nat req
    · simp only [hb, if_true, show uint.nat s.st.rv < uint.nat req by omega]
    · simp only [hb, if_false] at hne hA htgt ⊢
      cases hp : k8s.prepareKeyM go!"/objs" x.ListKey' x.Recursive' with
      | none => simp only [hp] at hne; exact absurd rfl hne
      | some pre =>
        simp only [hp] at hne hA htgt ⊢
        -- the answer is a success (its error is 0 or 4)
        have hok := (listOutL_ok _ _ _ _ hne).2.1
        have ht := htgt hok req rfl
        have hra := hmin req hq
        unfold listStL at hne hA ht ⊢
        by_cases hpast : pastReadL x req = true
        · simp only [hpast, if_true] at hne hA ht ⊢
          rw [if_neg (by omega)]
          have hrs : uint.nat s.st.rv < 2 ^ 64 := by word
          by_cases hn : uint.nat req ≤ n0
          · have := h.seed _ hn
            unfold histN at this; unfold histAtL; rw [this]
          · have hcs := h.hist _ ht _ (by omega)
              ⟨fun _ => rfl, fun w hw => by
                obtain ⟨-, h2⟩ := h.cut w hw _ hra
                constructor
                · intro h1
                  rcases Nat.lt_or_ge (uint.nat req) (ρ w) with hc | hc
                  · have := h2.mpr hc; omega
                  · exact hc
                · intro h1
                  rcases Nat.lt_or_ge (uint.nat req) w with hc | hc
                  · have := h2.mp hc; omega
                  · exact hc⟩
            refine listOutL_ren A ρ x _ _ pre hcs ?_ (fun it hi => ?_) hne hA
            · show (histN s.hist (uint.nat req)).rv = (histN c.hist (uint.nat req)).rv
              rw [h.shrv _ (by omega) ht, h.chrv _ (by omega) (by omega)]
            · have hs := h.stored _ ht it hi
              have hcu := h.stored_cut _ hs
              have : uint.nat it.obj'.ResourceVersion' < 2 ^ 64 := by word
              have : uint.nat c.st.rv < 2 ^ 64 := by word
              exact ⟨hcu.1, by omega⟩
        · simp only [hpast, Bool.false_eq_true, if_false] at hne hA ht ⊢
          have hrv : s.st.rv = c.st.rv := by
            rw [(listOutL_ok _ _ _ _ hne).2.2] at ht
            word
          rw [if_neg (by rw [hrv]; omega)]
          refine listOutL_ren A ρ x _ _ pre h.cur hrv (fun it hi => ?_) hne hA
          have hcu := h.stored_cut _ (h.stored_cur it hi)
          have : uint.nat it.obj'.ResourceVersion' < 2 ^ 64 := by word
          have : uint.nat c.st.rv < 2 ^ 64 := by word
          exact ⟨hcu.1, by omega⟩

end go

end k8s_dist
end EtcdGrove
end Perennial
