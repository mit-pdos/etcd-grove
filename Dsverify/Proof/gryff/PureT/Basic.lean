/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureT/Basic.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit A2 (totality): basic tools. A forward "the step is `.ok` with a postcondition" calculus
for the model's `Except Fail` and `Option` computations, and lemmas about the model's maps, words,
replica ids and sends.
-/
module

public import Dsverify.Proof.gryff.Pure.Agree

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pure.tot

open model kahn

/-! ## The `Ok` calculus -/

/-- `x` is `.ok a` with `Q a`. -/
def Ok {α : Type} (x : Except Fail α) (Q : α → Prop) : Prop := ∃ a, x = .ok a ∧ Q a

/-- `x` is `some a` with `Q a`. -/
def OkO {α : Type} (x : Option α) (Q : α → Prop) : Prop := ∃ a, x = some a ∧ Q a

theorem Ok.ret {α : Type} {a : α} {Q : α → Prop} (h : Q a) : Ok (pure a : Except Fail α) Q :=
  ⟨a, rfl, h⟩

theorem Ok.ok {α : Type} {a : α} {Q : α → Prop} (h : Q a) : Ok (Except.ok a : Except Fail α) Q :=
  ⟨a, rfl, h⟩

theorem Ok.bind {α β : Type} {x : Except Fail α} {f : α → Except Fail β} {Q : β → Prop}
    (h : Ok x (fun a => Ok (f a) Q)) : Ok (x >>= f) Q := by
  obtain ⟨a, rfl, b, hb, hq⟩ := h
  exact ⟨b, hb, hq⟩

theorem Ok.mono {α : Type} {x : Except Fail α} {Q Q' : α → Prop} (h : Ok x Q)
    (hQ : ∀ a, Q a → Q' a) : Ok x Q' := by
  obtain ⟨a, h1, h2⟩ := h; exact ⟨a, h1, hQ a h2⟩

theorem Ok.isOk {α : Type} {x : Except Fail α} {Q : α → Prop} (h : Ok x Q) : ∃ a, x = .ok a := by
  obtain ⟨a, h1, _⟩ := h; exact ⟨a, h1⟩

theorem Ok.post {α : Type} {x : Except Fail α} {Q : α → Prop} (h : Ok x Q) {a : α}
    (hx : x = .ok a) : Q a := by
  obtain ⟨b, h1, h2⟩ := h; rw [hx] at h1; cases h1; exact h2

theorem OkO.some {α : Type} {a : α} {Q : α → Prop} (h : Q a) : OkO (some a) Q := ⟨a, rfl, h⟩

theorem OkO.mono {α : Type} {x : Option α} {Q Q' : α → Prop} (h : OkO x Q)
    (hQ : ∀ a, Q a → Q' a) : OkO x Q' := by
  obtain ⟨a, h1, h2⟩ := h; exact ⟨a, h1, hQ a h2⟩

theorem OkO.bind {α β : Type} {x : Option α} {f : α → Option β} {Q : β → Prop}
    (h : OkO x (fun a => OkO (f a) Q)) : OkO (x >>= f) Q := by
  obtain ⟨a, rfl, b, hb, hq⟩ := h
  exact ⟨b, hb, hq⟩

/-- `forIn` over a list in `Except Fail`, with a loop invariant. -/
theorem Ok.loop {α β : Type} (l : List α) (init : β) (f : α → β → Except Fail (ForInStep β))
    (I : List α → β → Prop) (h0 : I [] init)
    (hstep : ∀ pre a post b, l = pre ++ a :: post → I pre b →
      Ok (f a b) (fun r => match r with
        | .yield b' => I (pre ++ [a]) b'
        | .done b' => ∀ post', I (pre ++ a :: post') b')) :
    Ok (forIn l init f) (fun b => ∃ pre, I pre b ∧ ∃ post, l = pre ++ post) := by
  suffices H : ∀ (pre post : List α) (b : β), l = pre ++ post → I pre b →
      Ok (forIn post b f) (fun b => ∃ pre, I pre b ∧ ∃ post, l = pre ++ post) by
    exact H [] l init rfl h0
  intro pre post
  induction post generalizing pre with
  | nil => intro b hl hb; exact Ok.ret ⟨pre, hb, [], by simpa using hl⟩
  | cons a post ih =>
    intro b hl hb
    rw [List.forIn_cons]
    apply Ok.bind
    refine (hstep pre a post b hl hb).mono ?_
    intro r hr
    match r with
    | .done b' => exact Ok.ret ⟨pre ++ [a], hr [], post, by simp [hl]⟩
    | .yield b' => exact ih (pre ++ [a]) b' (by simp [hl]) hr

/-- `forIn` over a list in `Option`, with a loop invariant. -/
theorem OkO.loop {α β : Type} (l : List α) (init : β) (f : α → β → Option (ForInStep β))
    (I : List α → β → Prop) (h0 : I [] init)
    (hstep : ∀ pre a post b, l = pre ++ a :: post → I pre b →
      OkO (f a b) (fun r => match r with
        | .yield b' => I (pre ++ [a]) b'
        | .done b' => ∀ post', I (pre ++ a :: post') b')) :
    OkO (forIn l init f) (fun b => ∃ pre, I pre b ∧ ∃ post, l = pre ++ post) := by
  suffices H : ∀ (pre post : List α) (b : β), l = pre ++ post → I pre b →
      OkO (forIn post b f) (fun b => ∃ pre, I pre b ∧ ∃ post, l = pre ++ post) by
    exact H [] l init rfl h0
  intro pre post
  induction post generalizing pre with
  | nil => intro b hl hb; exact OkO.some ⟨pre, hb, [], by simpa using hl⟩
  | cons a post ih =>
    intro b hl hb
    rw [List.forIn_cons]
    apply OkO.bind
    refine (hstep pre a post b hl hb).mono ?_
    intro r hr
    match r with
    | .done b' => exact OkO.some ⟨pre ++ [a], hr [], post, by simp [hl]⟩
    | .yield b' => exact ih (pre ++ [a]) b' (by simp [hl]) hr

/-- `forIn` over a list in `Id`, with a loop invariant (all iterations `yield`). -/
theorem Id.forIn_inv {α β : Type} (l : List α) (init : β) (f : α → β → Id (ForInStep β))
    (I : β → Prop) (h0 : I init)
    (hstep : ∀ a b, a ∈ l → I b → ∃ b', f a b = ForInStep.yield b' ∧ I b') :
    I (Id.run (forIn l init f)) := by
  induction l generalizing init with
  | nil => simpa using h0
  | cons a l ih =>
    obtain ⟨b', hb, hI⟩ := hstep a init (by simp) h0
    simp only [List.forIn_cons, Id.run]
    rw [hb]
    exact ih b' hI (fun a b ha hb => hstep a b (by simp [ha]) hb)

/-! ## Maps -/

namespace AMap
variable {n : Nat} {V : Type}

theorem get?_put (m : AMap n V) (k k' : BitVec n) (v : V) :
    (m.put k v).get? k' = if k' = k then some v else m.get? k' := by
  induction m with
  | nil => simp [model.AMap.put, model.AMap.get?, List.lookup]; split <;> simp_all
  | cons e t ih =>
    obtain ⟨a, b⟩ := e
    simp only [model.AMap.put]
    by_cases h1 : k = a
    · subst h1; by_cases h2 : k' = k <;> simp [model.AMap.get?, List.lookup, h2]; try (split <;> simp_all)
    · by_cases h3 : k.toNat < a.toNat
      · simp only [h1, h3, if_true, if_false]
        by_cases h2 : k' = k <;> simp [model.AMap.get?, List.lookup, h2]; try (split <;> simp_all)
      · simp only [h1, h3, if_false]
        simp only [model.AMap.get?] at ih ⊢
        by_cases h2 : k' = a
        · subst h2; simp [List.lookup, Ne.symm h1]
        · have e2 : (k' == a) = false := by simpa using h2
          simp only [List.lookup, e2, ih]

theorem get?_del (m : AMap n V) (k k' : BitVec n) :
    (m.del k).get? k' = if k' = k then none else m.get? k' := by
  induction m with
  | nil => simp [model.AMap.del, model.AMap.get?, List.lookup]
  | cons e t ih =>
    obtain ⟨a, b⟩ := e
    simp only [model.AMap.del, model.AMap.get?] at ih ⊢
    by_cases h1 : a = k
    · subst h1
      simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ite_false, ih]
      by_cases h2 : k' = a
      · simp [h2]
      · have e2 : (k' == a) = false := by simpa using h2
        simp only [h2, ite_false, List.lookup, e2]
    · have : (a != k) = true := by simpa using h1
      simp only [List.filter_cons, this, if_true]
      by_cases h2 : k' = a
      · subst h2; simp [List.lookup, h1]
      · have e2 : (k' == a) = false := by simpa using h2
        simp only [List.lookup, e2, ih]

theorem mem_of_get? {m : AMap n V} {k : BitVec n} {v : V} (h : m.get? k = some v) : (k, v) ∈ m := by
  induction m with
  | nil => simp [model.AMap.get?, List.lookup] at h
  | cons e t ih =>
    obtain ⟨a, b⟩ := e
    simp only [model.AMap.get?, List.lookup] at h
    by_cases h1 : k = a
    · subst h1; simp at h; subst h; simp
    · have : (k == a) = false := by simpa using h1
      rw [this] at h; exact List.mem_cons_of_mem _ (ih h)

theorem mem_put {m : AMap n V} {k : BitVec n} {v : V} {e : BitVec n × V} (h : e ∈ m.put k v) :
    e = (k, v) ∨ e ∈ m := by
  induction m with
  | nil => simp [model.AMap.put] at h; exact Or.inl h
  | cons x t ih =>
    obtain ⟨a, b⟩ := x
    simp only [model.AMap.put] at h
    split at h
    · simp at h; rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ h)
    · split at h
      · simp at h; rcases h with h | h | h
        · exact Or.inl h
        · subst h; simp
        · exact Or.inr (List.mem_cons_of_mem _ h)
      · simp at h; rcases h with h | h
        · subst h; simp
        · rcases ih h with h | h
          · exact Or.inl h
          · exact Or.inr (List.mem_cons_of_mem _ h)

theorem mem_del {m : AMap n V} {k : BitVec n} {e : BitVec n × V} (h : e ∈ m.del k) :
    e ∈ m ∧ e.1 ≠ k := by
  simp only [model.AMap.del, List.mem_filter] at h
  exact ⟨h.1, by simpa using h.2⟩

end AMap

/-! ## Words -/

theorem rid32_toNat (r : Fin 3) : (rid32 r).toNat = r.val := by
  have := r.isLt
  simp [rid32]; omega

theorem rid32_toInt (r : Fin 3) : (rid32 r).toInt = r.val := by
  revert r; decide

theorem rid32_inj {r r' : Fin 3} (h : rid32 r = rid32 r') : r = r' := by
  have := congrArg BitVec.toNat h
  rw [rid32_toNat, rid32_toNat] at this
  exact Fin.ext this

theorem dstOf_rid (r : Fin 3) : dstOf (rid32 r) = some r := by
  revert r; decide

theorem sendTo_rid (r : Fin 3) (m : Msg) : sendTo (rid32 r) m = some (.send r m) := by
  simp [sendTo, dstOf_rid]

theorem sendPeer_rid {s : RState} {r r' : Fin 3} (hs : s.id = rid32 r) (hne : r' ≠ r) (m : Msg) :
    sendPeer s (rid32 r') m = some (.send r' m) := by
  have : rid32 r' ≠ s.id := by rw [hs]; exact fun h => hne (rid32_inj h)
  simp [sendPeer, this, sendTo_rid]

/-- The two peers of replica `r`, in `PreferredPeerOrder`. -/
def peers (r : Fin 3) : List (Fin 3) := [r + 1, r + 2]

theorem peerOrder_eq {s : RState} {r : Fin 3} (hs : s.id = rid32 r) :
    peerOrder s = (peers r).map rid32 := by
  simp only [peerOrder, hs, peers]
  clear hs; revert r; decide

theorem peers_ne {r q : Fin 3} (h : q ∈ peers r) : q ≠ r := by
  revert q; revert r; decide

theorem bcast_eq {s : RState} {r : Fin 3} (hs : s.id = rid32 r) (m : Msg) :
    bcast s m = some ((peers r).map (fun q => .send q m)) := by
  rw [bcast, peerOrder_eq hs]
  have h1 := sendPeer_rid (m := m) hs (peers_ne (r := r) (q := r + 1) (by simp [peers]))
  have h2 := sendPeer_rid (m := m) hs (peers_ne (r := r) (q := r + 2) (by simp [peers]))
  simp [peers, List.mapM_cons, h1, h2]

/-- `slt` and `sle` on words whose values are small and nonnegative are the order of `toNat`. -/
theorem toInt_small {x : w32} (h : x.toNat < 2 ^ 31) : x.toInt = x.toNat := by
  rw [BitVec.toInt_eq_toNat_cond]; simp; omega

end Perennial.gryff.pure.tot

namespace Perennial.gryff.pure.tot
open model

theorem never_bind {α β : Type} (f : α → Except Fail β) :
    ((never : Except Fail α) >>= f) = never := rfl
theorem dead_bind {α β : Type} (f : α → Except Fail β) :
    ((dead : Except Fail α) >>= f) = dead := rfl
theorem disabled_bind {α β : Type} (f : α → Except Fail β) :
    ((disabled : Except Fail α) >>= f) = disabled := rfl
theorem pure_bind' {α β : Type} (a : α) (f : α → Except Fail β) :
    ((pure a : Except Fail α) >>= f) = f a := rfl
theorem map_never {α β : Type} (f : α → β) : (f <$> (never : Except Fail α)) = never := rfl
theorem map_dead {α β : Type} (f : α → β) : (f <$> (dead : Except Fail α)) = dead := rfl

/-- The step simp set: the model's control flow with the given facts. -/
syntax "tsimp" (" [" Lean.Parser.Tactic.simpLemma,* "]")? (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| tsimp $[[$xs,*]]? $[$loc]?) => do
    let xs := xs.map (·.getElems) |>.getD #[]
    `(tactic| simp (config := {maxSteps := 4000000}) only [ne_eq, not_true_eq_false,
      not_false_eq_true, ite_true, ite_false, Bool.false_eq_true, Bool.true_eq_false, Bool.not_true,
      Bool.not_false, never_bind, dead_bind, disabled_bind, pure_bind', map_never, map_dead,
      Bool.and_true, Bool.true_and, Bool.and_false, Bool.false_and, Bool.or_false, Bool.false_or,
      Bool.or_true, Bool.true_or, if_true, if_false, $xs,*] $[$loc]?)

end Perennial.gryff.pure.tot
