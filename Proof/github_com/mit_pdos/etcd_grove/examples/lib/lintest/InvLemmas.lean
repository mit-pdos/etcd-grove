/-
Lean-first (no Rocq counterpart).

# lintest: the ghost log's steps, in pure terms (2026-10-14)

`InvOk` (`Defs.lean`) is preserved by the two events of a client's loop: a clock reading
(`InvOk.read`: the clock moves forward, the client records the value it read) and an
operation's linearization point (`InvOk.commit`: the operation is appended to the log with
the clock's current value, and to the client's records). What a client learns from it
(`InvOk.lr_le'`, `InvOk.recs_le`): its last reading and the `τ`s of its records are at most
the clock's current value. The library may return an output other than the one it committed,
when the model cannot tell them apart (`InvOk.swap`: the client's last record and its log entry
take the returned output; `applySpec`, `Defs.lean`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.lintest.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace lintest

open github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

section pure
variable {σ α : Type}

theorem run_append_one (M : SeqModel σ α) (s0 : σ) (l : List α) (a : α) :
    run M s0 (l ++ [a]) = (run M s0 l).bind (M.step · a) := by
  induction l generalizing s0 with
  | nil =>
    simp only [List.nil_append, run, Option.bind_some]
    cases M.step s0 a <;> rfl
  | cons b l ih =>
    simp only [List.cons_append, run]
    cases M.step s0 b with
    | none => rfl
    | some s1 => exact ih s1

theorem clientRecs_append (c : Nat) (Lc : List (α × Int)) (p : α × Int) :
    clientRecs c (Lc ++ [p]) = clientRecs c Lc ++ [⟨c, Lc.length, p.1, p.2⟩] := by
  simp [clientRecs, List.mapIdx_append]

/-- Running the model over two lists of steps it cannot tell apart, pointwise. -/
theorem run_map_congr {β : Type} (M : SeqModel σ α) (f g : β → α) (l : List β)
    (h : ∀ x ∈ l, ∀ s, M.step s (f x) = M.step s (g x)) (s0 : σ) :
    run M s0 (l.map f) = run M s0 (l.map g) := by
  induction l generalizing s0 with
  | nil => rfl
  | cons b l ih =>
    simp only [List.map_cons, run]
    rw [h b (List.mem_cons_self ..) s0]
    cases M.step s0 (g b) with
    | none => rfl
    | some s1 => exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx)) s1

end pure

section ghost
variable [GooseExts] {σ : Type} {M : SeqModel σ OpV} {n : Nat} {s : σ} {t : w64}
  {L : List (LinRec OpV)} {Ls : GMap Nat ClientV}

theorem toRecs_append (c : Nat) (Lc : List (OpV × w64)) (p : OpV × w64) :
    toRecs c (Lc ++ [p]) = toRecs c Lc ++ [⟨c, Lc.length, p.1, sint.Z p.2⟩] := by
  simp only [toRecs, List.map_append, List.map_cons, List.map_nil, clientRecs_append,
    List.length_map]

theorem recsOf_insert (c c' : Nat) (v : ClientV) :
    recsOf (Ls.insert c v) c' = if c = c' then v.1 else recsOf Ls c' := by
  unfold recsOf
  rw [GMap.lookup_insert_eq_iff]
  split <;> rfl

/-- A client's last clock reading is at most the clock's value. -/
theorem InvOk.lr_le' (H : InvOk M n s t L Ls) {c : Nat} {v : ClientV}
    (hc : Ls.lookup c = some v) : sint.Z v.2 ≤ sint.Z t := H.lr_le c v hc

/-- A client's records are in the log, so their `τ`s are at most the clock's value. -/
theorem InvOk.recs_le (H : InvOk M n s t L Ls) {c : Nat} {v : ClientV}
    (hc : Ls.lookup c = some v) {p : OpV × w64} (hp : p ∈ v.1) : sint.Z p.2 ≤ sint.Z t := by
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hp
  have hm : (⟨c, j, p.1, sint.Z p.2⟩ : LinRec OpV) ∈ L.filter (fun e => e.c == c) := by
    rw [H.filt c]
    apply List.mem_of_getElem? (i := j)
    simp only [toRecs, recsOf, hc, Option.map_some, Option.getD_some, clientRecs_getElem?,
      List.getElem?_map, hj]
  exact H.le_t _ (List.mem_filter.1 hm).1

/-- A clock reading: the clock moves from `t` to `t' ≥ t`, and client `c` records `t'`. -/
theorem InvOk.read (H : InvOk M n s t L Ls) {c : Nat} {v : ClientV}
    (hc : Ls.lookup c = some v) {t' : w64} (ht : sint.Z t ≤ sint.Z t') :
    InvOk M n s t' L (Ls.insert c (v.1, t')) where
  runs := H.runs
  sorted := H.sorted
  le_t e he := Int.le_trans (H.le_t e he) ht
  lr_le c' v' hc' := by
    rw [GMap.lookup_insert_eq_iff] at hc'
    split at hc'
    · cases hc'; exact Int.le_refl _
    · exact Int.le_trans (H.lr_le c' v' hc') ht
  dom c' v' hc' := by
    rw [GMap.lookup_insert_eq_iff] at hc'
    split at hc'
    · next h => subst h; exact H.dom c v hc
    · exact H.dom c' v' hc'
  filt c' := by
    rw [recsOf_insert, H.filt c']
    split
    · next h => subst h; simp only [recsOf, hc, Option.map_some, Option.getD_some]
    · rfl

/-- A linearization point: client `c`'s operation `io` takes the model from `s` to `s'`; it is
appended to the log and to the client's records, with the clock's value `t`. -/
theorem InvOk.commit (H : InvOk M n s t L Ls) {c : Nat} {v : ClientV}
    (hc : Ls.lookup c = some v) {io : OpV} {s' : σ} (hstep : M.step s io = some s') :
    InvOk M n s' t (L ++ [⟨c, v.1.length, io, sint.Z t⟩]) (Ls.insert c (v.1 ++ [(io, t)], v.2))
    where
  runs := by
    rw [List.map_append, List.map_singleton, run_append_one, H.runs]
    exact hstep
  sorted := by
    rw [List.pairwise_append]
    refine ⟨H.sorted, List.pairwise_singleton _ _, ?_⟩
    intro a ha b hb
    rw [List.mem_singleton] at hb
    subst hb
    exact H.le_t a ha
  le_t e he := by
    rw [List.mem_append, List.mem_singleton] at he
    rcases he with he | he
    · exact H.le_t e he
    · subst he; exact Int.le_refl _
  lr_le c' v' hc' := by
    rw [GMap.lookup_insert_eq_iff] at hc'
    split at hc'
    · cases hc'; exact H.lr_le c v hc
    · exact H.lr_le c' v' hc'
  dom c' v' hc' := by
    rw [GMap.lookup_insert_eq_iff] at hc'
    split at hc'
    · next h => subst h; exact H.dom c v hc
    · exact H.dom c' v' hc'
  filt c' := by
    rw [List.filter_append, recsOf_insert, H.filt c']
    split
    · next h =>
      subst h
      rw [toRecs_append]
      simp only [recsOf, hc, Option.map_some, Option.getD_some, List.filter_cons,
        beq_self_eq_true, ↓reduceIte, List.filter_nil]
    · next h =>
      simp only [List.filter_cons, List.filter_nil]
      have : (c == c') = false := by simp [h]
      rw [this]
      simp

/-- The log entry of client `c`'s `j`-th record, with the output swapped to `io'`. -/
def swapRec (c j : Nat) (io' : OpV) (e : LinRec OpV) : LinRec OpV :=
  if e.c = c ∧ e.j = j then { e with io := io' } else e

theorem map_swapRec_toRecs (c : Nat) (Lc : List (OpV × w64)) (io io' : OpV) (τ : w64) :
    (toRecs c (Lc ++ [(io, τ)])).map (swapRec c Lc.length io') = toRecs c (Lc ++ [(io', τ)]) := by
  apply List.ext_getElem?
  intro k
  simp only [List.getElem?_map, toRecs, clientRecs_getElem?, List.map_append, List.map_cons,
    List.map_nil]
  rcases Nat.lt_trichotomy k Lc.length with hk | hk | hk
  · rw [List.getElem?_append_left (by simpa using hk), List.getElem?_append_left (by simpa using hk)]
    cases (Lc.map fun p => (p.1, sint.Z p.2))[k]? with
    | none => rfl
    | some p => simp [swapRec, Nat.ne_of_lt hk]
  · subst hk
    rw [List.getElem?_append_right (by simp), List.getElem?_append_right (by simp)]
    simp [swapRec]
  · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
    rfl

theorem map_swapRec_toRecs_ne {c c' : Nat} (h : c ≠ c') (j : Nat) (io' : OpV)
    (Lc : List (OpV × w64)) : (toRecs c' Lc).map (swapRec c j io') = toRecs c' Lc := by
  refine (List.map_congr_left ?_).trans (List.map_id _)
  intro e he
  obtain ⟨p, -, hp⟩ := mem_clientRecs he
  have hc : e.c = c' := by rw [hp]
  simp [swapRec, hc, Ne.symm h]

/-- The library returned `io'` in place of the output `io` it committed, which the model cannot
tell apart: client `c`'s last record, and its entry in the log, take `io'`. -/
theorem InvOk.swap (H : InvOk M n s t L Ls) {c : Nat} {Lc : List (OpV × w64)} {lr : w64}
    {io io' : OpV} {τ : w64} (hc : Ls.lookup c = some (Lc ++ [(io, τ)], lr))
    (heq : ∀ s, M.step s io' = M.step s io) :
    InvOk M n s t (L.map (swapRec c Lc.length io')) (Ls.insert c (Lc ++ [(io', τ)], lr)) where
  runs := by
    rw [List.map_map, ← H.runs]
    refine run_map_congr M _ _ L ?_ M.init
    intro e he s0
    simp only [Function.comp_apply, swapRec]
    split
    · next hj =>
      have hm : e ∈ L.filter (fun e => e.c == c) := List.mem_filter.2 ⟨he, by simp [hj.1]⟩
      rw [H.filt c, recsOf, hc, Option.map_some, Option.getD_some] at hm
      obtain ⟨p, hp, he'⟩ := mem_clientRecs hm
      rw [List.getElem?_map, hj.2, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
        List.getElem?_cons_zero, Option.map_some, Option.some.injEq] at hp
      subst hp
      rw [he']
      exact heq s0
    · rfl
  sorted := by
    rw [List.pairwise_map]
    refine H.sorted.imp ?_
    intro a b hab
    simp only [swapRec]
    split <;> split <;> exact hab
  le_t e he := by
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
    have := H.le_t e0 he0
    simp only [swapRec]
    split <;> exact this
  lr_le c' v' hc' := by
    rw [GMap.lookup_insert_eq_iff] at hc'
    split at hc'
    · cases hc'; exact H.lr_le c (Lc ++ [(io, τ)], lr) hc
    · exact H.lr_le c' v' hc'
  dom c' v' hc' := by
    rw [GMap.lookup_insert_eq_iff] at hc'
    split at hc'
    · next h => subst h; exact H.dom c _ hc
    · exact H.dom c' v' hc'
  filt c' := by
    have hf : (L.map (swapRec c Lc.length io')).filter (fun e => e.c == c') =
        (L.filter (fun e => e.c == c')).map (swapRec c Lc.length io') := by
      rw [List.filter_map]
      congr 1
      apply List.filter_congr
      intro e _
      simp only [Function.comp_apply, swapRec]
      split <;> rfl
    rw [hf, H.filt c', recsOf_insert]
    split
    · next h =>
      subst h
      simp only [recsOf, hc, Option.map_some, Option.getD_some]
      exact map_swapRec_toRecs c Lc io io' τ
    · next h => exact map_swapRec_toRecs_ne h _ _ _

/-- A client's trace and records, one operation further. -/
theorem ClientOk.snoc {id : w64} {hc : List Operation} {Lc : List (OpV × w64)}
    (H : ClientOk id hc Lc) (input output : GoInterface) (call τ ret : w64)
    (h1 : sint.Z call ≤ sint.Z τ) (h2 : sint.Z τ ≤ sint.Z ret) :
    ClientOk id (hc ++ [Operation.mk id input call output ret GoInterface.nil ()])
      (Lc ++ [((input, output), τ)]) := by
  obtain ⟨hlen, hj⟩ := H
  refine ⟨by simp [hlen], ?_⟩
  intro j o p ho hp
  rcases Nat.lt_or_ge j hc.length with hlt | hge
  · rw [List.getElem?_append_left hlt] at ho
    rw [List.getElem?_append_left (by omega)] at hp
    exact hj j o p ho hp
  · rw [List.getElem?_append_right hge] at ho
    rw [List.getElem?_append_right (by omega)] at hp
    rcases Nat.lt_or_ge (j - hc.length) 1 with h1' | h1'
    · have h0 : j - hc.length = 0 := by omega
      have h0' : j - Lc.length = 0 := by omega
      rw [h0] at ho
      rw [h0'] at hp
      simp only [List.getElem?_cons_zero, Option.some.injEq] at ho hp
      subst ho hp
      exact ⟨rfl, rfl, h1, h2⟩
    · rw [List.getElem?_eq_none (by simp; omega)] at ho
      cases ho

end ghost

end lintest
end EtcdGrove
end Perennial
