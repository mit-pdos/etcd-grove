/-
`node.spill` after its children's loop (U9w, `notes/bbolt-proof-plan.md`; pure): **a per-entry
family cut at the pieces' lengths** (`cutF`), for `pcInv_init`'s `Es`/`Ds`: piece `k`'s part is
the family from its first entry's global index `o` on (`cutF_get`), and the global bound of entry
`o + m` is the piece's bound of its entry `m` (`childHi_cut`).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.NodeSpillTailInv

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section cut

/-- **A family `f` over the global indices, cut at the lengths `ls`**: each part the
concatenation of its indices' lists. -/
def cutF {β : Type} : List Nat → (Nat → List β) → List (List β)
  | [], _ => []
  | a :: ls, f => (List.range a).flatMap f :: cutF ls (fun g => f (a + g))

theorem cutF_length {β : Type} (ls : List Nat) (f : Nat → List β) :
    (cutF ls f).length = ls.length := by
  induction ls generalizing f with
  | nil => rfl
  | cons a ls ih => simp [cutF, ih]

theorem cutF_flatten {β : Type} (ls : List Nat) (f : Nat → List β) :
    (cutF ls f).flatten = (List.range ls.sum).flatMap f := by
  induction ls generalizing f with
  | nil => rfl
  | cons a ls ih =>
    simp only [cutF, List.flatten_cons, ih, List.sum_cons, List.range_add, List.flatMap_append,
      List.flatMap_map]

/-- **Piece `k`'s part** (see the module doc). -/
theorem cutF_get {α β : Type} (wss : List (List α)) (f : Nat → List β) (k : Nat) (ws : List α)
    (h : wss[k]? = some ws) :
    ∃ o, (cutF (wss.map List.length) f)[k]? =
        some ((List.range ws.length).flatMap (fun m => f (o + m))) ∧
      (∀ m, m < ws.length → wss.flatten[o + m]? = ws[m]?) ∧
      wss.flatten.drop (o + ws.length) = (wss.drop (k + 1)).flatten := by
  induction wss generalizing k f with
  | nil => simp at h
  | cons a rest ih =>
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      refine ⟨0, ?_, ?_, ?_⟩
      · simp [cutF]
      · intro m hm
        simp only [Nat.zero_add, List.flatten_cons]
        rw [List.getElem?_append_left hm]
      · simp
    | succ k =>
      simp only [List.getElem?_cons_succ] at h
      obtain ⟨o, h1, h2, h3⟩ := ih (fun g => f (a.length + g)) k h
      refine ⟨a.length + o, ?_, ?_, ?_⟩
      · simp only [List.map_cons, cutF, List.getElem?_cons_succ, h1, Nat.add_assoc]
      · intro m hm
        rw [List.flatten_cons, show a.length + o + m = a.length + (o + m) by omega,
          List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
        exact h2 m hm
      · rw [List.flatten_cons, show a.length + o + ws.length = a.length + (o + ws.length) by omega,
          List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append,
          Nat.add_sub_cancel_left, h3, List.drop_succ_cons]

end cut

section bound
variable [GooseExts] [GoGlobalContext]

/-- **The global bound of entry `o + m` is piece `k`'s bound of its entry `m`** (the pieces not
empty when there are two or more). -/
theorem childHi_cut {hi : Option (List w8)} {wss : List (List WEntry)} {k o : Nat}
    {ws : List WEntry} (hk : wss[k]? = some ws)
    (h2 : wss.flatten.drop (o + ws.length) = (wss.drop (k + 1)).flatten)
    (hg : ∀ m, m < ws.length → wss.flatten[o + m]? = ws[m]?)
    (hne : ∀ (k' : Nat) (ws' : List WEntry), wss[k']? = some ws' → 2 ≤ wss.length → 0 < ws'.length)
    {m : Nat} (hm : m < ws.length) :
    childHi hi (wKey wss.flatten) wss.flatten.length (o + m) =
      childHi (pcHi hi wss k) (wKey ws) ws.length m := by
  have hkl : k < wss.length := (List.getElem?_eq_some_iff.1 hk).1
  unfold childHi
  by_cases hm1 : m + 1 < ws.length
  · have e := hg (m + 1) hm1
    have hlt : o + m + 1 < wss.flatten.length := by
      rw [Nat.add_assoc] at *
      have : (wss.flatten[o + (m + 1)]?).isSome := by rw [e]; simp [hm1]
      simpa using this
    rw [if_pos hlt, if_pos hm1]
    unfold wKey; rw [Nat.add_assoc, e]
  · have hme : m + 1 = ws.length := by omega
    rw [if_neg hm1]
    unfold pcHi childHi
    by_cases hk1 : k + 1 < wss.length
    · rw [if_pos hk1]
      obtain ⟨ws', hws'⟩ : ∃ ws', wss[k + 1]? = some ws' :=
        ⟨_, List.getElem?_eq_getElem hk1⟩
      have hpos := hne (k + 1) ws' hws' (by omega)
      have hd : (wss.drop (k + 1)).flatten = ws' ++ (wss.drop (k + 2)).flatten := by
        rw [List.drop_eq_getElem_cons hk1, List.flatten_cons]
        rw [List.getElem?_eq_some_iff] at hws'
        obtain ⟨_, e⟩ := hws'
        rw [e]
      have e0 : wss.flatten[o + m + 1]? = ws'[0]? := by
        rw [show o + m + 1 = o + ws.length + 0 by omega, ← List.getElem?_drop, h2, hd,
          List.getElem?_append_left hpos]
      have hlt : o + m + 1 < wss.flatten.length := by
        have : (wss.flatten[o + m + 1]?).isSome := by rw [e0]; simp [hpos]
        simpa using this
      rw [if_pos hlt]
      unfold wssKey wKey
      rw [e0, hws']
      rfl
    · rw [if_neg hk1]
      have hd : (wss.drop (k + 1)).flatten = [] := by
        rw [List.drop_eq_nil_of_le (by omega)]; rfl
      have hle : wss.flatten.length ≤ o + m + 1 := by
        have := congrArg List.length h2
        rw [hd, List.length_drop] at this
        simp only [List.length_nil] at this
        omega
      rw [if_neg (by omega)]

end bound

end Spill

end bbolt
end EtcdGrove
end Perennial
