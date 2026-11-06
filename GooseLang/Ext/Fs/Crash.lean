/-
What a machine crash keeps of the log (`Impl.lean`, `MachineCrash`), for a log whose calls did not
overlap: every entry's call began after the previous one took effect (`Sequential`). Then a set
closed under `Follows` is a prefix, so a crash keeps the durable tree with a prefix of the log
replayed, as with a journal of one thread. Untrusted.
-/
module

public import GooseLang.Ext.Fs.Tree

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs

/-- Every entry's call began when the log held exactly the entries before it: no two calls
overlapped. -/
def Sequential (log : List LogEntry) : Prop := ∀ x (e : LogEntry), log[x]? = some e → e.start = x

theorem sequential_snoc {log : List LogEntry} {o : MetaOp} (h : Sequential log) :
    Sequential (log ++ [⟨o, log.length⟩]) := by
  intro x e he
  by_cases hx : x < log.length
  · rw [List.getElem?_append_left hx] at he; exact h x e he
  · have : x = log.length := by
      have := List.getElem?_eq_some_iff.1 he |>.1; simp at this; omega
    subst this
    rw [List.getElem?_append_right (Nat.le_refl _)] at he
    simp at he; rw [← he]

/-- In a sequential log, an entry follows every earlier one. -/
theorem follows_seq {log : List LogEntry} (h : Sequential log) {x y : Nat} (hx : x < log.length)
    (hy : y < x) : Follows log x y := by
  obtain ⟨ex, hex⟩ : ∃ e, log[x]? = some e := ⟨_, List.getElem?_eq_getElem hx⟩
  obtain ⟨ey, hey⟩ : ∃ e, log[y]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  exact ⟨hy, ex, ey, hex, hey, .inl (by rw [h x ex hex]; exact hy)⟩

open Classical in
/-- A set of naturals below `L`, closed downwards, is an initial segment. -/
theorem init_seg (S : Nat → Prop) : ∀ L, (∀ x, S x → x < L) → (∀ x y, S x → y < x → S y) →
    ∃ n, n ≤ L ∧ ∀ x, S x ↔ x < n
  | 0, hb, _ => ⟨0, Nat.le_refl _, fun x => ⟨fun hx => hb x hx, fun hx => absurd hx (Nat.not_lt_zero _)⟩⟩
  | L + 1, hb, hd => by
    by_cases hL : S L
    · refine ⟨L + 1, Nat.le_refl _, fun x => ⟨hb x, fun hx => ?_⟩⟩
      rcases Nat.lt_or_ge x L with h | h
      · exact hd L x hL h
      · have : x = L := by omega
        subst this; exact hL
    · obtain ⟨n, hn, hiff⟩ := init_seg S L (fun x hx => by
        have := hb x hx
        rcases Nat.lt_or_ge x L with h | h
        · exact h
        · have : x = L := by omega
          subst this; exact absurd hx hL) hd
      exact ⟨n, by omega, hiff⟩

/-- **A closed set of a sequential log is a prefix.** -/
theorem closed_prefix {log : List LogEntry} (h : Sequential log) {S : Nat → Prop}
    (hS : ∀ x, S x → x < log.length) (hc : Closed log S) :
    ∃ n, n ≤ log.length ∧ ∀ x, S x ↔ x < n :=
  init_seg S log.length hS (fun x y hx hy => hc x y hx (follows_seq h (hS x hx) hy))

open Classical in
/-- The operations of a prefix of the log. -/
theorem keptOps_prefix (log : List LogEntry) (S : Nat → Prop) (n : Nat) (hn : n ≤ log.length)
    (hS : ∀ x, S x ↔ x < n) : keptOps log S = (log.take n).map (·.op) := by
  unfold keptOps
  have : ∀ m, m ≤ n → (List.range m).filterMap
      (fun k => if S k then (log[k]?).map (·.op) else none) = (log.take m).map (·.op) := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      have hm' : S m := (hS m).2 (by omega)
      rw [List.range_succ, List.filterMap_append, ih (by omega), List.take_succ, List.map_append,
        List.getElem?_eq_getElem (by omega : m < log.length)]
      congr 1
      simp only [List.filterMap_cons, List.filterMap_nil]
      rw [if_pos hm', List.getElem?_eq_getElem (by omega : m < log.length)]
      rfl
  have hrest : (List.range log.length).filterMap
      (fun k => if S k then (log[k]?).map (·.op) else none) =
      (List.range n).filterMap (fun k => if S k then (log[k]?).map (·.op) else none) := by
    have hsplit : List.range log.length = List.range n ++
        (List.range (log.length - n)).map (n + ·) := by
      rw [← List.range_add]; congr 1; omega
    rw [hsplit, List.filterMap_append]
    suffices h0 : ((List.range (log.length - n)).map (n + ·)).filterMap
        (fun k => if S k then (log[k]?).map (·.op) else none) = [] by rw [h0, List.append_nil]
    rw [List.filterMap_eq_nil_iff]
    intro k hk
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hk
    rw [if_neg (fun h' => by have := (hS _).1 h'; omega)]
  rw [hrest, this n (Nat.le_refl _)]

/-- **What a crash keeps of a sequential log**: the operations of a prefix, as with one journal. -/
theorem crash_seq {log : List LogEntry} (h : Sequential log) {S : Nat → Prop}
    (hS : ∀ x, S x → x < log.length) (hc : Closed log S) :
    ∃ n, n ≤ log.length ∧ keptOps log S = (log.take n).map (·.op) := by
  obtain ⟨n, hn, hiff⟩ := closed_prefix h hS hc
  exact ⟨n, hn, keptOps_prefix log S n hn hiff⟩

end Fs
end Perennial

end
