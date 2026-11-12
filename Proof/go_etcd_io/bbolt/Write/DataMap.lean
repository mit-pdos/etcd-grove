/-
U7k (`notes/bbolt-proof-plan.md`): the list and map facts of `wtxData_put`/`wtxData_del`. A
bucket's walk is a list of leaf blocks; replacing the blocks of one leaf (`sel`) by `wsPut`/`wsDel`
of its entries changes the bucket's `GMap.ofList` of plain entries by `insert`/`delete` when no
other block holds the key, and keeps its bucket entries (`rootEnts`) when the key is no bucket's.
-/
module

public import Proof.go_etcd_io.bbolt.Model.LTree

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

namespace Write

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section datamap
variable [GooseExts]

/-- A leaf entry's plain entry (`lbktEnts`). -/
def plainOf (w : WEntry) : Option BoltEnt :=
  if decide (isBktFlag w.flags) then none else some (w.key, w.value)

/-- A leaf entry's bucket entry (`rootEnts`). -/
def bktOf (w : WEntry) : Option (GoString × List w8) :=
  if decide (isBktFlag w.flags) then some (w.key, w.value) else none

/-! ## Maps of lists -/

theorem ofList_append {K V : Type} [DecidableEq K] (A B : List (K × V)) :
    GMap.ofList (A ++ B) = GMap.ofList A ∪ GMap.ofList B := by
  induction A with
  | nil => apply GMap.ext; intro k; show _ = (none : Option V).or _; simp; rfl
  | cons a A ih =>
    obtain ⟨a1, a2⟩ := a
    apply GMap.ext; intro k
    show (GMap.ofList ((a1, a2) :: (A ++ B))) !! k = (GMap.ofList ((a1, a2) :: A) ∪ _) !! k
    simp only [GMap.ofList, GMap.lookup_union, GMap.lookup_insert_eq_iff, ih]
    split <;> simp

theorem ofList_none {K V : Type} [DecidableEq K] (L : List (K × V)) (k : K)
    (h : ∀ e ∈ L, e.1 ≠ k) : (GMap.ofList L) !! k = none := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    obtain ⟨a1, a2⟩ := a
    simp only [GMap.ofList, GMap.lookup_insert_eq_iff]
    rw [if_neg (h _ List.mem_cons_self)]
    exact ih fun e he => h e (List.mem_cons_of_mem _ he)

theorem ofList_filter_ne {K V : Type} [DecidableEq K] (L : List (K × V)) (k : K) :
    GMap.ofList (L.filter fun e => decide (e.1 ≠ k)) = (GMap.ofList L).delete k := by
  induction L with
  | nil => apply GMap.ext; intro k'; show (none : Option V) = if k = k' then none else none; simp
  | cons a L ih =>
    obtain ⟨a1, a2⟩ := a
    apply GMap.ext; intro k'
    by_cases h : a1 = k
    · subst h
      rw [List.filter_cons_of_neg (by simp), ih]
      simp only [GMap.ofList, GMap.lookup_delete_iff, GMap.lookup_insert_eq_iff]
      split <;> simp_all
    · rw [List.filter_cons_of_pos (by simp [h])]
      simp only [GMap.ofList, GMap.lookup_delete_iff, GMap.lookup_insert_eq_iff, ih]
      by_cases h1 : a1 = k' <;> by_cases h2 : k = k' <;> simp_all

theorem ofList_mid {K V : Type} [DecidableEq K] (A B : List (K × V)) (x : K × V)
    (h : ∀ e ∈ A, e.1 ≠ x.1) :
    GMap.ofList (A ++ x :: B) = (GMap.ofList (A ++ B)).insert x.1 x.2 := by
  rw [ofList_append, ofList_append]
  apply GMap.ext; intro k
  show (GMap.ofList A ∪ GMap.insert x.1 x.2 (GMap.ofList B)) !! k =
    (GMap.insert x.1 x.2 (GMap.ofList A ∪ GMap.ofList B)) !! k
  simp only [GMap.lookup_union, GMap.lookup_insert_eq_iff]
  by_cases hk : x.1 = k
  · subst hk; rw [ofList_none A x.1 h]; simp
  · simp [hk]

/-! ## Sorted entries -/

/-- The entries' keys increase strictly, as a list relation. -/
def wsPw (ws : List WEntry) : Prop := ws.Pairwise fun a b => go.GoStringLt a.key b.key

theorem wsSorted_pw (ws : List WEntry) (h : wsSorted ws) : wsPw ws := by
  unfold wsPw
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  have := h i j hij hj
  unfold wKey at this
  simpa [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj] using this

theorem filter_lt_gt (ws : List WEntry) (k : List w8) (h : wsPw ws) :
    ws.filter (fun w => decide (go.GoStringLt w.key k)) ++
      ws.filter (fun w => decide (go.GoStringLt k w.key)) =
    ws.filter fun w => decide (w.key ≠ k) := by
  induction ws with
  | nil => rfl
  | cons a ws ih =>
    unfold wsPw at h
    rw [List.pairwise_cons] at h
    obtain ⟨hlt, hp⟩ := h
    have ih := ih hp
    by_cases h1 : go.GoStringLt a.key k
    · have h2 : ¬ go.GoStringLt k a.key := go.goStringLt_asymm h1
      have h3 : a.key ≠ k := fun he => by subst he; exact go.goStringLt_irrefl _ h1
      rw [List.filter_cons_of_pos (by simpa using h1), List.filter_cons_of_neg (by simpa using h2),
        List.filter_cons_of_pos (by simpa using h3), List.cons_append, ih]
    · -- every later key is above `a.key ≥ k`
      have hge : ∀ w ∈ ws, go.GoStringLt k w.key := by
        intro w hw
        have := hlt w hw
        by_cases he : a.key = k
        · rw [← he]; exact this
        · have : go.GoStringLt k a.key :=
            Classical.byContradiction fun hc => he (go.goStringLt_eq_of_not_lt h1 hc)
          exact go.goStringLt_trans this (hlt w hw)
      have hlt0 : ws.filter (fun w => decide (go.GoStringLt w.key k)) = [] := by
        rw [List.filter_eq_nil_iff]; intro w hw
        simpa using go.goStringLt_asymm (hge w hw)
      have hgt0 : ws.filter (fun w => decide (go.GoStringLt k w.key)) = ws := by
        rw [List.filter_eq_self]; intro w hw; simpa using hge w hw
      have hne0 : ws.filter (fun w => decide (w.key ≠ k)) = ws := by
        rw [List.filter_eq_self]; intro w hw
        have := hge w hw
        simp only [ne_eq, decide_eq_true_eq]
        intro he; rw [he] at this; exact go.goStringLt_irrefl _ this
      rw [List.filter_cons_of_neg (by simpa using h1), hlt0, List.nil_append]
      by_cases he : a.key = k
      · rw [List.filter_cons_of_neg (by simp [he]; exact go.goStringLt_irrefl _),
          List.filter_cons_of_neg (by simp [he]), hgt0, hne0]
      · have : go.GoStringLt k a.key :=
          Classical.byContradiction fun hc => he (go.goStringLt_eq_of_not_lt h1 hc)
        rw [List.filter_cons_of_pos (by simpa using this), List.filter_cons_of_pos (by simp [he]),
          hgt0, hne0]

theorem wsPut_split (ws : List WEntry) (e : WEntry) :
    wsPut ws e = ws.filter (fun w => decide (go.GoStringLt w.key e.key)) ++ e ::
      ws.filter (fun w => decide (go.GoStringLt e.key w.key)) := by
  unfold wsPut; simp

theorem filterMap_filter_ne {α : Type} (g : WEntry → Option (List w8 × α))
    (hg : ∀ w x, g w = some x → x.1 = w.key) (ws : List WEntry) (k : List w8) :
    (ws.filter fun w => decide (w.key ≠ k)).filterMap g =
      (ws.filterMap g).filter fun x => decide (x.1 ≠ k) := by
  induction ws with
  | nil => rfl
  | cons a ws ih =>
    by_cases ha : a.key = k
    · rw [List.filter_cons_of_neg (by simp [ha]), ih, List.filterMap_cons]
      cases hga : g a with
      | none => rfl
      | some x => rw [List.filter_cons_of_neg (by simp [hg a x hga, ha])]
    · rw [List.filter_cons_of_pos (by simp [ha]), List.filterMap_cons, List.filterMap_cons, ih]
      cases hga : g a with
      | none => rfl
      | some x => rw [List.filter_cons_of_pos (by simp [hg a x hga, ha])]

theorem plainOf_key (w : WEntry) (x : BoltEnt) (h : plainOf w = some x) : x.1 = w.key := by
  unfold plainOf at h; split at h
  · cases h
  · cases h; rfl

theorem bktOf_key (w : WEntry) (x : GoString × List w8) (h : bktOf w = some x) : x.1 = w.key := by
  unfold bktOf at h; split at h
  · cases h; rfl
  · cases h

theorem filterMap_filter_ne_keep {α : Type} (g : WEntry → Option α) (ws : List WEntry)
    (k : List w8) (h : ∀ w ∈ ws, w.key = k → g w = none) :
    (ws.filter fun w => decide (w.key ≠ k)).filterMap g = ws.filterMap g := by
  induction ws with
  | nil => rfl
  | cons a ws ih =>
    have ih := ih fun w hw => h w (List.mem_cons_of_mem _ hw)
    by_cases ha : a.key = k
    · rw [List.filter_cons_of_neg (by simp [ha]), ih, List.filterMap_cons,
        h a List.mem_cons_self ha]
    · rw [List.filter_cons_of_pos (by simp [ha]), List.filterMap_cons, List.filterMap_cons, ih]

/-- **A leaf's plain entries after `Put`**. -/
theorem ofList_plain_wsPut (ws : List WEntry) (e : WEntry) (hs : wsPw ws)
    (hflag : ¬ isBktFlag e.flags) :
    GMap.ofList ((wsPut ws e).filterMap plainOf) =
      (GMap.ofList (ws.filterMap plainOf)).insert e.key e.value := by
  rw [wsPut_split, List.filterMap_append, List.filterMap_cons]
  have he : plainOf e = some (e.key, e.value) := by unfold plainOf; simp [hflag]
  rw [he]
  rw [ofList_mid _ _ (e.key, e.value)]
  · rw [← List.filterMap_append, filter_lt_gt ws e.key hs,
      filterMap_filter_ne plainOf plainOf_key, ofList_filter_ne]
    apply GMap.ext; intro k
    show (GMap.insert e.key e.value _) !! k = (GMap.insert e.key e.value _) !! k
    simp only [GMap.lookup_insert_eq_iff, GMap.lookup_delete_iff]
    split <;> simp_all
  · intro x hx
    rw [List.mem_filterMap] at hx
    obtain ⟨w, hw, hwx⟩ := hx
    rw [plainOf_key w x hwx]
    rw [List.mem_filter] at hw
    have := of_decide_eq_true hw.2
    intro heq; rw [heq] at this; exact go.goStringLt_irrefl _ this

theorem ofList_plain_wsDel (ws : List WEntry) (k : List w8) :
    GMap.ofList ((wsDel ws k).filterMap plainOf) =
      (GMap.ofList (ws.filterMap plainOf)).delete k := by
  unfold wsDel
  rw [filterMap_filter_ne plainOf plainOf_key, ofList_filter_ne]

theorem bkt_wsPut (ws : List WEntry) (e : WEntry) (hs : wsPw ws) (hflag : ¬ isBktFlag e.flags)
    (hnb : ∀ w ∈ ws, w.key = e.key → ¬ isBktFlag w.flags) :
    (wsPut ws e).filterMap bktOf = ws.filterMap bktOf := by
  rw [wsPut_split, List.filterMap_append, List.filterMap_cons]
  have he : bktOf e = none := by unfold bktOf; simp [hflag]
  rw [he, ← List.filterMap_append, filter_lt_gt ws e.key hs]
  apply filterMap_filter_ne_keep
  intro w hw hk; unfold bktOf; simp [hnb w hw hk]

theorem bkt_wsDel (ws : List WEntry) (k : List w8)
    (hnb : ∀ w ∈ ws, w.key = k → ¬ isBktFlag w.flags) :
    (wsDel ws k).filterMap bktOf = ws.filterMap bktOf := by
  unfold wsDel
  apply filterMap_filter_ne_keep
  intro w hw hk; unfold bktOf; simp [hnb w hw hk]

/-! ## Blocks -/

theorem fm_congr {α β : Type} {f g : α → List β} {l : List α} (h : ∀ x ∈ l, f x = g x) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons, h a List.mem_cons_self,
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem blocks_del {β : Type} (bs : List β) (sel : β → Bool) (get : β → List WEntry)
    (k : List w8) (h2 : ∀ b ∈ bs, sel b = false → ∀ w ∈ get b, w.key ≠ k) :
    GMap.ofList (bs.flatMap fun b => (if sel b then wsDel (get b) k else get b).filterMap plainOf) =
      (GMap.ofList (bs.flatMap fun b => (get b).filterMap plainOf)).delete k := by
  induction bs with
  | nil => apply GMap.ext; intro k'; show (none : Option _) = if k = k' then none else none; simp
  | cons b bs ih =>
    have ih := ih fun b' hb' => h2 b' (List.mem_cons_of_mem _ hb')
    simp only [List.flatMap_cons]
    rw [ofList_append, ofList_append, ih]
    apply GMap.ext; intro k'
    show (_ ∪ _) !! k' = (GMap.delete k (_ ∪ _)) !! k'
    simp only [GMap.lookup_union, GMap.lookup_delete_iff]
    cases hs : sel b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      by_cases hk : k = k'
      · subst hk
        rw [ofList_none _ k]; · simp
        intro x hx; rw [List.mem_filterMap] at hx
        obtain ⟨w, hw, hwx⟩ := hx
        rw [plainOf_key w x hwx]; exact h2 b List.mem_cons_self hs w hw
      · simp [hk]
    · simp only [↓reduceIte, ofList_plain_wsDel, GMap.lookup_delete_iff]
      split <;> simp

theorem blocks_put {β : Type} (bs : List β) (sel : β → Bool) (get : β → List WEntry)
    (e : WEntry) (hflag : ¬ isBktFlag e.flags) (hs : ∀ b ∈ bs, sel b = true → wsPw (get b))
    (h2 : ∀ b ∈ bs, sel b = false → ∀ w ∈ get b, w.key ≠ e.key) (h3 : ∃ b ∈ bs, sel b = true) :
    GMap.ofList (bs.flatMap fun b =>
        (if sel b then wsPut (get b) e else get b).filterMap plainOf) =
      (GMap.ofList (bs.flatMap fun b => (get b).filterMap plainOf)).insert e.key e.value := by
  -- the blocks with no selected one are unchanged
  have hsame : ∀ bs : List β, (∀ b ∈ bs, sel b = false) →
      (bs.flatMap fun b => (if sel b then wsPut (get b) e else get b).filterMap plainOf) =
        bs.flatMap fun b => (get b).filterMap plainOf := by
    intro bs h
    apply fm_congr; intro b hb; rw [h b hb]; rfl
  induction bs with
  | nil => obtain ⟨b, hb, -⟩ := h3; cases hb
  | cons b bs ih =>
    simp only [List.flatMap_cons]
    rw [ofList_append, ofList_append]
    cases hsb : sel b
    · obtain ⟨b', hb', hs'⟩ := h3
      have hb'' : b' ∈ bs := by
        rcases List.mem_cons.1 hb' with rfl | h
        · rw [hsb] at hs'; cases hs'
        · exact h
      rw [ih (fun b hb => hs b (List.mem_cons_of_mem _ hb))
        (fun b hb => h2 b (List.mem_cons_of_mem _ hb)) ⟨b', hb'', hs'⟩]
      apply GMap.ext; intro k'
      show (_ ∪ GMap.insert _ _ _) !! k' = (GMap.insert _ _ (_ ∪ _)) !! k'
      simp only [Bool.false_eq_true, ↓reduceIte, GMap.lookup_union, GMap.lookup_insert_eq_iff]
      by_cases hk : e.key = k'
      · subst hk
        rw [ofList_none _ e.key]; · simp
        intro x hx; rw [List.mem_filterMap] at hx
        obtain ⟨w, hw, hwx⟩ := hx
        rw [plainOf_key w x hwx]; exact h2 b List.mem_cons_self hsb w hw
      · simp [hk]
    · simp only [↓reduceIte]
      rw [ofList_plain_wsPut _ _ (hs b List.mem_cons_self hsb) hflag]
      have hrest : GMap.ofList (bs.flatMap fun b =>
            (if sel b then wsPut (get b) e else get b).filterMap plainOf) =
          (GMap.ofList (bs.flatMap fun b => (get b).filterMap plainOf)).insert e.key e.value ∨
          GMap.ofList (bs.flatMap fun b =>
            (if sel b then wsPut (get b) e else get b).filterMap plainOf) =
          GMap.ofList (bs.flatMap fun b => (get b).filterMap plainOf) := by
        by_cases hex : ∃ b ∈ bs, sel b = true
        · exact Or.inl (ih (fun b hb => hs b (List.mem_cons_of_mem _ hb))
            (fun b hb => h2 b (List.mem_cons_of_mem _ hb)) hex)
        · have hno : ∀ b ∈ bs, sel b = false := by
            intro b hb
            cases h : sel b
            · rfl
            · exact absurd ⟨b, hb, h⟩ hex
          exact Or.inr (by rw [hsame bs hno])
      rcases hrest with hr | hr <;> rw [hr] <;> (apply GMap.ext; intro k') <;>
        simp only [GMap.lookup_union, GMap.lookup_insert_eq_iff] <;>
        split <;> simp

theorem blocks_bkt {β : Type} (bs : List β) (sel : β → Bool) (get : β → List WEntry)
    (f : List WEntry → List WEntry)
    (hf : ∀ b ∈ bs, sel b = true → (f (get b)).filterMap bktOf = (get b).filterMap bktOf) :
    (bs.flatMap fun b => (if sel b then f (get b) else get b).filterMap bktOf) =
      bs.flatMap fun b => (get b).filterMap bktOf := by
  apply fm_congr; intro b hb
  cases h : sel b
  · rfl
  · simp only [↓reduceIte]; exact hf b hb h

end datamap

end Write

end bbolt
end EtcdGrove
end Perennial
