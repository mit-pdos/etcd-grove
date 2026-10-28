/-
Lean-first (no Rocq counterpart).

# The driver's model: its item lists as maps (stage 6b of `notes/k8s-etcd3-plan.md`)

On a list sorted by key (`SortedI`), `setItemL` is a map update: `setItemL its it = setRI it its`
(the recursive form), `lookupL` of it is `it` at its key and `lookupL its` elsewhere
(`lookupL_setItemL`), and it stays sorted; `delItemL` is a map deletion (`lookupL_delItemL`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8setcd3.KModel

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8setcd3

open github_com.mit_pdos.etcd_grove.examples.k8setcd3 (item)

section go
variable [GooseExts]

/-- The items are sorted by key, strictly (so the keys are distinct). -/
def SortedI (its : List item) : Prop := (its.map item.key').Pairwise go.GoStringLt

/-- `setItem`, recursively, on a sorted list. -/
def setRI (it : item) : List item → List item
  | [] => [it]
  | e :: es =>
    if go.GoStringLt it.key' e.key' then it :: e :: es
    else if e.key' = it.key' then it :: es
    else e :: setRI it es

theorem lookupL_cons (e : item) (l : List item) (k : GoString) :
    lookupL (e :: l) k = if e.key' = k then (e, true) else lookupL l k := by
  unfold lookupL
  by_cases h : e.key' = k <;> simp [h, List.find?_cons]

theorem lookupL_nil (k : GoString) : lookupL [] k = (zItem, false) := rfl

theorem sortedI_cons {e : item} {l : List item} :
    SortedI (e :: l) ↔ (∀ x ∈ l, go.GoStringLt e.key' x.key') ∧ SortedI l := by
  unfold SortedI
  simp [List.pairwise_cons]

/-- With `done` set and no later key `it`'s, the loop copies the rest. -/
theorem setStepI_done (it : item) (o l : List item) (h : ∀ x ∈ l, x.key' ≠ it.key') :
    l.foldl (setStepI it) (o, true) = (o ++ l, true) := by
  induction l generalizing o with
  | nil => simp
  | cons e l ih =>
    simp only [List.foldl_cons]
    have he : e.key' ≠ it.key' := h e (by simp)
    have : setStepI it (o, true) e = (o ++ [e], true) := by simp [setStepI, he]
    rw [this, ih (o ++ [e]) (fun x hx => h x (by simp [hx]))]
    simp

/-- The end of `setItem`: `it` appended if not yet written. -/
def setFinI (it : item) (st : List item × Bool) : List item := if st.2 then st.1 else st.1 ++ [it]

theorem setItemL_fin (it : item) (l : List item) :
    setItemL l it = setFinI it (l.foldl (setStepI it) ([], false)) := rfl

theorem setItemL_eq (it : item) (l : List item) (hs : SortedI l) : setItemL l it = setRI it l := by
  suffices H : ∀ o, setFinI it (l.foldl (setStepI it) (o, false)) = o ++ setRI it l by
    rw [setItemL_fin]; simpa using H []
  induction l with
  | nil => intro o; simp [setRI, setFinI]
  | cons e l ih =>
    intro o
    obtain ⟨hlt, hs'⟩ := sortedI_cons.1 hs
    simp only [List.foldl_cons]
    by_cases h1 : go.GoStringLt it.key' e.key'
    · have h2 : e.key' ≠ it.key' := fun h => go.goStringLt_irrefl _ (h ▸ h1)
      have hst : setStepI it (o, false) e = (o ++ [it] ++ [e], true) := by
        simp [setStepI, h1, h2]
      rw [hst, setStepI_done it _ l (fun x hx he => go.goStringLt_irrefl _
        (he ▸ go.goStringLt_trans h1 (hlt x hx)))]
      simp [setRI, setFinI, h1]
    · by_cases h2 : e.key' = it.key'
      · have hst : setStepI it (o, false) e = (o ++ [it], true) := by
          simp [setStepI, h2, go.goStringLt_irrefl]
        rw [hst, setStepI_done it _ l (fun x hx he => go.goStringLt_irrefl _
          (he ▸ h2 ▸ hlt x hx))]
        simp [setRI, setFinI, h2, go.goStringLt_irrefl]
      · have hst : setStepI it (o, false) e = (o ++ [e], false) := by
          simp [setStepI, h1, h2]
        rw [hst, ih hs' (o ++ [e])]
        simp [setRI, h1, h2]

theorem lookupL_setRI (it : item) (l : List item) (k : GoString) :
    lookupL (setRI it l) k = if it.key' = k then (it, true) else lookupL l k := by
  induction l with
  | nil => simp [setRI, lookupL_cons, lookupL_nil]
  | cons e l ih =>
    unfold setRI
    by_cases h1 : go.GoStringLt it.key' e.key'
    · simp only [h1, ↓reduceIte, lookupL_cons]
    · by_cases h2 : e.key' = it.key'
      · rw [if_neg h1, if_pos h2]
        rw [lookupL_cons]
        by_cases hk : it.key' = k
        · simp [hk]
        · rw [if_neg hk, if_neg hk, lookupL_cons, if_neg (fun h => hk (h2.symm.trans h))]
      · simp only [h1, h2, ↓reduceIte, lookupL_cons, ih]
        by_cases hk : e.key' = k
        · have : it.key' ≠ k := fun h => h2 (hk.trans h.symm)
          simp [hk, this]
        · simp [hk]

theorem mem_setRI (it : item) (l : List item) (x : item) (h : x ∈ setRI it l) :
    x = it ∨ x ∈ l := by
  induction l with
  | nil => simpa [setRI] using h
  | cons e l ih =>
    unfold setRI at h
    split at h
    · simpa using h
    · split at h
      · simp at h; rcases h with rfl | h
        · exact .inl rfl
        · exact .inr (List.mem_cons_of_mem _ h)
      · simp at h; rcases h with rfl | h
        · exact .inr (by simp)
        · rcases ih h with h | h
          · exact .inl h
          · exact .inr (List.mem_cons_of_mem _ h)

theorem sortedI_setRI (it : item) (l : List item) (hs : SortedI l) : SortedI (setRI it l) := by
  induction l with
  | nil => simp [setRI, SortedI]
  | cons e l ih =>
    obtain ⟨hlt, hs'⟩ := sortedI_cons.1 hs
    unfold setRI
    by_cases h1 : go.GoStringLt it.key' e.key'
    · simp only [h1, ↓reduceIte]
      refine sortedI_cons.2 ⟨?_, hs⟩
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact h1
      · exact go.goStringLt_trans h1 (hlt x hx)
    · by_cases h2 : e.key' = it.key'
      · rw [if_neg h1, if_pos h2]
        exact sortedI_cons.2 ⟨fun x hx => h2 ▸ hlt x hx, hs'⟩
      · simp only [h1, h2, ↓reduceIte]
        have hlt' : go.GoStringLt e.key' it.key' :=
          Classical.byContradiction fun h3 => h2 (go.goStringLt_eq_of_not_lt h3 h1)
        refine sortedI_cons.2 ⟨?_, ih hs'⟩
        intro x hx
        rcases mem_setRI it l x hx with rfl | hx
        · exact hlt'
        · exact hlt x hx

/-- **`setItem` on a sorted list is a map update.** -/
theorem lookupL_setItemL (its : List item) (it : item) (hs : SortedI its) (k : GoString) :
    lookupL (setItemL its it) k = if it.key' = k then (it, true) else lookupL its k := by
  rw [setItemL_eq it its hs, lookupL_setRI]

theorem sortedI_setItemL (its : List item) (it : item) (hs : SortedI its) :
    SortedI (setItemL its it) := by
  rw [setItemL_eq it its hs]; exact sortedI_setRI it its hs

/-- **`delItem` is a map deletion.** -/
theorem lookupL_delItemL (its : List item) (k k' : GoString) :
    lookupL (delItemL its k) k' = if k = k' then (zItem, false) else lookupL its k' := by
  induction its with
  | nil => simp [delItemL, lookupL_nil]
  | cons e l ih =>
    unfold delItemL at ih ⊢
    by_cases he : e.key' = k
    · simp only [List.filter_cons, he, decide_true, Bool.not_true, Bool.false_eq_true,
        ↓reduceIte, ih, lookupL_cons]
      by_cases hk : k = k' <;> simp [hk]
    · simp only [List.filter_cons, he, decide_false, Bool.not_false, ↓reduceIte, lookupL_cons, ih]
      by_cases hk : k = k'
      · subst hk; simp [he]
      · simp [hk]

theorem sortedI_delItemL (its : List item) (k : GoString) (hs : SortedI its) :
    SortedI (delItemL its k) := by
  unfold SortedI delItemL at *
  exact (hs.sublist (List.Sublist.map _ (List.filter_sublist)))

end go

end k8setcd3
end EtcdGrove
end Perennial
