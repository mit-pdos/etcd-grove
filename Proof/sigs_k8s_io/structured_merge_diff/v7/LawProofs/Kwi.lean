/-
**`keysWithItemsB_iff`, proved** (`v7/Laws.lean`): `keysWithItemsB` decides `keysWithItems`.
`kwiAt` checks every position of a path (`kwiAt_iff`), and a set passes when each of its paths does
(`FSet.all_iff`).

Prove phase (2026-11-19, notes/smd-plan.md).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.Laws

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

namespace LawProofs

theorem FSet.all_iff {α : Type} [DecidableEq α] (f : α → Bool) (s : FSet α) :
    s.all f = true ↔ ∀ x, x ∈ s → f x = true := by
  induction s using Quotient.inductionOn with
  | h l =>
    change (!(l.any (fun x => !f x))) = true ↔ ∀ x, FSet.mem (Quotient.mk _ l) x = true → f x = true
    simp [FSet.mem]

/-- One position's check of `kwiAt` (its `match`, verbatim). -/
def kwiChk (S : Schema) (t : TypeRef) (s : PathSet) (acc : Path) (pe : PE) (rest : Path) : Bool :=
  match pe with
  | .key fl =>
    let it := acc ++ [pe]
    match rest with
    | [] =>
      match (typeAlong S (some t) it).bind (fun t => S.find t.name) with
      | some (.map _ _ rel) =>
        decide (rel = .atomic) || fl.all (fun nv => decide ((it ++ [.field nv.1]) ∈ s))
      | _ => true
    | .field n :: r =>
      if fl.any (fun nv => decide (nv.1 = n)) then decide (it ∈ s) && r.isEmpty else true
    | _ => true
  | _ => true

theorem kwiAt_cons (S : Schema) (t : TypeRef) (s : PathSet) (acc : Path) (pe : PE) (rest : Path) :
    kwiAt S t s acc (pe :: rest) = (kwiChk S t s acc pe rest && kwiAt S t s (acc ++ [pe]) rest) := by
  rfl

theorem kwiAt_iff (S : Schema) (t : TypeRef) (s : PathSet) : ∀ (q acc : Path),
    kwiAt S t s acc q = true ↔
      ∀ q1 pe rest, q = q1 ++ pe :: rest → kwiChk S t s (acc ++ q1) pe rest = true
  | [], acc => by
      simp only [kwiAt, true_iff]
      intro q1 pe rest h
      simp at h
  | pe :: rest, acc => by
      rw [kwiAt_cons, Bool.and_eq_true, kwiAt_iff S t s rest (acc ++ [pe])]
      constructor
      · rintro ⟨h1, h2⟩ q1 pe' rest' hq
        cases q1 with
        | nil =>
          simp only [List.nil_append, List.cons.injEq] at hq
          obtain ⟨rfl, rfl⟩ := hq
          simpa using h1
        | cons x q1' =>
          simp only [List.cons_append, List.cons.injEq] at hq
          obtain ⟨rfl, hq⟩ := hq
          have := h2 q1' pe' rest' hq
          simpa using this
      · intro h
        refine ⟨by simpa using h [] pe rest rfl, fun q1 pe' rest' hq => ?_⟩
        have := h (pe :: q1) pe' rest' (by simp [hq])
        simpa using this

end LawProofs

open LawProofs

theorem keysWithItemsB_iff_law_holds : keysWithItemsB_iff.law := by
  intro S t s
  unfold keysWithItemsB
  rw [LawProofs.FSet.all_iff]
  simp only [LawProofs.kwiAt_iff, List.nil_append]
  constructor
  · intro h
    intro p fl
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨n, v, hnv, hq⟩
      have := h _ hq p (.key fl) [.field n] (by simp)
      simp only [kwiChk] at this
      have hany : fl.any (fun nv => decide (nv.1 = n)) = true :=
        List.any_eq_true.2 ⟨(n, v), hnv, by simp⟩
      simp only [hany, ite_true, List.isEmpty_nil, Bool.and_true, decide_eq_true_eq] at this
      exact this
    · rintro hq ⟨fs, e, rel, htype, hrel⟩ n v hnv
      have := h _ hq p (.key fl) [] (by simp)
      simp only [kwiChk, htype, Bool.or_eq_true, decide_eq_true_eq, hrel, false_or,
        List.all_eq_true] at this
      have := this (n, v) hnv
      simpa using this
    · intro n v r hnv hr hq
      have := h _ hq p (.key fl) (.field n :: r) (by simp)
      simp only [kwiChk] at this
      have hany : fl.any (fun nv => decide (nv.1 = n)) = true :=
        List.any_eq_true.2 ⟨(n, v), hnv, by simp⟩
      simp only [hany, ite_true, Bool.and_eq_true, List.isEmpty_iff] at this
      exact hr this.2
  · intro h q hq q1 pe rest hqe
    subst hqe
    cases pe with
    | field _ => rfl
    | value _ => rfl
    | index _ => rfl
    | key fl =>
      cases rest with
      | nil =>
        simp only [kwiChk]
        split
        · rename_i fs e rel htype
          cases hrel : decide (rel = .atomic) with
          | true => rfl
          | false =>
            simp only [Bool.false_or, List.all_eq_true, decide_eq_true_eq]
            intro nv hnv
            have := (h q1 fl).2.1 hq ⟨fs, e, rel, htype, by simpa using hrel⟩ nv.1 nv.2 hnv
            simpa using this
        · rfl
      | cons x r =>
        cases x with
        | field n =>
          simp only [kwiChk]
          split
          · rename_i hany
            obtain ⟨⟨n', v⟩, hnv, hn⟩ := List.any_eq_true.1 hany
            simp only [decide_eq_true_eq] at hn
            subst hn
            have hr : r = [] := by
              cases r with
              | nil => rfl
              | cons x r' =>
                exact absurd (by simpa using hq)
                  ((h q1 fl).2.2 n' v (x :: r') hnv (List.cons_ne_nil _ _))
            subst hr
            have := (h q1 fl).1 ⟨n', v, hnv, by simpa using hq⟩
            simp [this]
          · rfl
        | key _ => rfl
        | value _ => rfl
        | index _ => rfl

end smd
end EtcdGrove
end Perennial
