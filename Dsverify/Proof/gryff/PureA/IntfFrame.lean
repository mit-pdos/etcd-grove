/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureA/IntfFrame.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit AI, internal: the interference invariant's frame. A step at replica `a` at clock `κ` adds at
most one record (`addRec`: `a` records instance `ox` at time `κ`, if it had not), maybe a creation
deps entry, and moves the clock to `κ + 1`; old facts survive (`*_mono`); `intf_post`: the invariant
after a step from its local obligations (`LocalI`: new copies of `a` satisfy `CopyI`, sent messages
`MsgI`) and the table / ghost facts of the step.
-/
module

public import Dsverify.Proof.gryff.PureA.IntfFun

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pureA.AI

open Perennial Perennial.gryff.model Perennial.gryff.pure Perennial.gryff.kahn Perennial.gryff.pureA
open Perennial.gryff.pureA.AW

/-! ## The ghost's growth -/

/-- Replica `a` records instance `ox` at time `κ` (if it had not). -/
def addRec (rc : RecG) (a : Fin 3) (κ : Nat) : Option (w32 × w32) → RecG
  | none => rc
  | some (q, j) => fun w q' j' =>
    if w = a ∧ q' = q ∧ j' = j ∧ rc a q j = none then some κ else rc w q' j'

/-- `rc'` extends `rc` by records at times `≥ κ`. -/
structure RExt (rc rc' : RecG) (κ : Nat) : Prop where
  keep : ∀ w q j t, rc w q j = some t → rc' w q j = some t
  new : ∀ w q j t, rc' w q j = some t → t < κ → rc w q j = some t

def DgLe (dg dg' : DepG) : Prop := ∀ q j D, dg q j = some D → dg' q j = some D

theorem DgLe.refl (dg : DepG) : DgLe dg dg := fun _ _ _ h => h

theorem addRec_ext (rc : RecG) (a : Fin 3) (κ : Nat) (ox : Option (w32 × w32)) :
    RExt rc (addRec rc a κ ox) κ := by
  rcases ox with _ | ⟨q, j⟩
  · exact ⟨fun _ _ _ _ h => h, fun _ _ _ _ h _ => h⟩
  · refine ⟨fun w q' j' t h => ?_, fun w q' j' t h ht => ?_⟩
    · simp only [addRec]
      rw [if_neg]; · exact h
      rintro ⟨rfl, rfl, rfl, e⟩; rw [e] at h; cases h
    · simp only [addRec] at h
      split at h
      · cases h; exact absurd ht (Nat.lt_irrefl _)
      · exact h

theorem addRec_self {rc : RecG} {a : Fin 3} {κ : Nat} {q j : w32}
    (hcl : ∀ t, rc a q j = some t → t < κ) : ∃ t, addRec rc a κ (some (q, j)) a q j = some t ∧ t ≤ κ ∧
      (rc a q j = none → t = κ) := by
  simp only [addRec]
  cases h : rc a q j with
  | none => exact ⟨κ, by simp [h], Nat.le_refl _, fun _ => rfl⟩
  | some t =>
    refine ⟨t, ?_, ?_, fun e => by cases e⟩
    · simp [h]
    · exact Nat.le_of_lt (hcl t h)

/-! ## Monotonicity -/

section mono
variable {rc rc' : RecG} {κ κ' : Nat} (E : RExt rc rc' κ) (hk : κ ≤ κ')
include E hk

theorem cov_mono {q i : w32} {D : Deps} {w : Fin 3} {e : Option (Fin 3)} (h : Cov rc κ q i D w e) :
    Cov rc' κ' q i D w e := by
  obtain ⟨τ, hτ, ⟨t, ht, htτ⟩, hc⟩ := h
  exact ⟨τ, Nat.le_trans hτ hk, ⟨t, E.keep _ _ _ _ ht, htτ⟩,
    fun r j t' h1 h2 h3 h4 => hc r j t' (E.new _ _ _ _ h1 (Nat.lt_of_lt_of_le h2 hτ)) h2 h3 h4⟩

theorem wp2_mono {q i : w32} {D : Deps} (h : Wp2 rc κ q i D) : Wp2 rc' κ' q i D := by
  obtain ⟨w1, w2, e, h12, c1, c2, he⟩ := h
  exact ⟨w1, w2, e, h12, cov_mono E hk c1, cov_mono E hk c2, he⟩

theorem valI_mono {q i : w32} {D : Deps} {st : w8} (h : ValI rc κ q i D st) :
    ValI rc' κ' q i D st :=
  ⟨h.1, let ⟨w, hw⟩ := h.2.1; ⟨w, cov_mono E hk hw⟩, fun hs => wp2_mono E hk (h.2.2 hs)⟩

theorem candI_mono {q i : w32} {ri : Option RecoveryInstance} (h : CandI rc κ q i ri) :
    CandI rc' κ' q i ri := fun r hr hc => valI_mono E hk (h r hr hc)

theorem copyI_mono {dg dg' : DepG} (hd : DgLe dg dg') {q i : w32} {a : Fin 3} {cp : Copy}
    (h : CopyI rc κ dg q i a cp) : CopyI rc' κ' dg' q i a cp where
  val h1 h2 := let k := h.val h1 h2
    ⟨valI_mono E hk k.1, fun hs => let k2 := k.2 hs; ⟨cov_mono E hk k2.1, k2.2⟩⟩
  own0 h1 h2 h3 h4 := let ⟨D, hD, hl⟩ := h.own0 h1 h2 h3 h4; ⟨D, hd _ _ _ hD, hl⟩
  cand lb hl hn := candI_mono E hk (h.cand lb hl hn)

theorem msgI_mono {dg dg' : DepG} (hd : DgLe dg dg') {d : Fin 3} {m : Msg}
    (h : MsgI rc κ dg d m) : MsgI rc' κ' dg' d m := by
  cases m <;> simp only [MsgI] at h ⊢
  case preAccept m =>
    intro hc
    obtain ⟨k0, k1, ⟨w, hw, k2⟩, k3⟩ := h hc
    exact ⟨k0, k1, ⟨w, hw, cov_mono E hk k2⟩, fun h0 => hd _ _ _ (k3 h0)⟩
  case preAcceptReply m =>
    intro hc
    obtain ⟨k1, w, hw, k2⟩ := h hc
    exact ⟨k1, w, hw, cov_mono E hk k2⟩
  case preAcceptOK m =>
    obtain ⟨D, hD, X, hX, k⟩ := h
    exact ⟨D, hd _ _ _ hD, X, hX, cov_mono E hk k⟩
  case accept m =>
    intro hc; exact ⟨(h hc).1, wp2_mono E hk (h hc).2⟩
  case commit m =>
    intro hc; exact ⟨(h hc).1, wp2_mono E hk (h hc).2⟩
  case prepareReply m =>
    intro h1 h2; exact valI_mono E hk (h h1 h2)
  all_goals trivial

end mono

/-! ## Deps -/

theorem cov_weaken {rc : RecG} {κ : Nat} {q i : w32} {D D' : Deps} {w : Fin 3}
    {e e' : Option (Fin 3)} (he : ∀ r, e' ≠ some r → e ≠ some r)
    (hD : ∀ r : Fin 3, e' ≠ some r → sint.Z (D.at r.val) ≤ sint.Z (D'.at r.val))
    (h : Cov rc κ q i D w e) : Cov rc κ q i D' w e' := by
  obtain ⟨τ, hτ, k1, hc⟩ := h
  exact ⟨τ, hτ, k1, fun r j t h1 h2 h3 h4 => Int.le_trans (hc r j t h1 h2 h3 (he r h4)) (hD r h4)⟩

theorem cov_dle {rc : RecG} {κ : Nat} {q i : w32} {D D' : Deps} {w : Fin 3} {e : Option (Fin 3)}
    (hD : DLe D D') (h : Cov rc κ q i D w e) : Cov rc κ q i D' w e :=
  cov_weaken (fun _ h => h) (fun r _ => hD r.val) h

theorem sameRow_dle {q i : w32} {D D' : Deps} (hD : DLe D D') (h : SameRow q i D) :
    SameRow q i D' := Int.le_trans h (hD _)

theorem wp2_dle {rc : RecG} {κ : Nat} {q i : w32} {D D' : Deps} (hD : DLe D D')
    (h : Wp2 rc κ q i D) : Wp2 rc κ q i D' := by
  obtain ⟨w1, w2, e, h12, c1, c2, he⟩ := h
  exact ⟨w1, w2, e, h12, cov_dle hD c1, cov_dle hD c2, he⟩

/-! ## New coverage -/

/-- Replica `a`, whose table (in the state before the step) is below `D` on the rows other than
`q` and `e`, and which recorded `(q, i)` by now, covers `D` at the step's time `κ`. -/
theorem cov_new {rc : RecG} {κ : Nat} {s : RState} {a : Fin 3} {q i : w32} {D : Deps}
    {e : Option (Fin 3)} {ox : Option (w32 × w32)}
    (tab : ∀ (r : Fin 3) j t, rc a (rid32 r) j = some t →
      ∃ hi, s.confAt r.val = some hi ∧ sint.Z j ≤ sint.Z hi)
    (hD : ∀ r : Fin 3, rid32 r ≠ q → e ≠ some r → ∀ hi, s.confAt r.val = some hi →
      sint.Z hi ≤ sint.Z (D.at r.val))
    (hrec : ∃ t, addRec rc a κ ox a q i = some t ∧ t ≤ κ) :
    Cov (addRec rc a κ ox) (κ + 1) q i D a e := by
  refine ⟨κ, Nat.le_succ _, hrec, fun r j t h1 h2 h3 h4 => ?_⟩
  have h1' := (addRec_ext rc a κ ox).new _ _ _ _ h1 h2
  obtain ⟨hi, e1, l1⟩ := tab r j t h1'
  exact Int.le_trans l1 (hD r h3 h4 hi e1)

/-! ## The frame -/

/-- The local obligations of a step of `a` from `s` to `s'` sending `o`, w.r.t. the new ghosts. -/
def LocalI (rc : RecG) (κ : Nat) (dg : DepG) (s s' : RState) (a : Fin 3) (o : List Out) : Prop :=
  (∀ q i cp, s'.inst q i = some cp → s.inst q i = some cp ∨ CopyI rc κ dg q i a cp) ∧
  (∀ d m, m ∈ A1b.sentR d o → MsgI rc κ dg d m)

/-- **The frame**: the invariant after a step. -/
theorem intf_post {c c1 : Cfg gNet} {κ : Nat} {rc : RecG} {dg dg' : DepG} {a : Fin 3} {e : Ev}
    {s' : RState} {o : List Out} {ox : Option (w32 × w32)}
    (J : IInv c κ rc dg) (hp : Post c a e s' o c1) (hloc : Loc s') (hd : DgLe dg dg')
    (hdg : ∀ q j D, dg' q j = some D → dg q j = some D ∨
      ∃ r : Fin 3, ∃ t, q = rid32 r ∧ addRec rc a κ ox r q j = some t)
    (hconf : ConfLe (c.st a) s')
    (hox : ∀ q j, ox = some (q, j) →
      (∃ hi, s'.confAt q.toNat = some hi ∧ sint.Z j ≤ sint.Z hi) ∧
      (∃ r : Fin 3, q = rid32 r ∧ sint.Z j < sint.Z ((c1.st r).crt (rid32 r))) ∧
      (q = rid32 a ∨ ∃ w t, rc w q j = some t))
    (hcrt : ∀ r, sint.Z ((c.st r).crt (rid32 r)) ≤ sint.Z ((c1.st r).crt (rid32 r)))
    (hownRow : ∀ j, 0 ≤ sint.Z j → sint.Z j < sint.Z (s'.crt (rid32 a)) →
      ∃ t, addRec rc a κ ox a (rid32 a) j = some t)
    (hL : LocalI (addRec rc a κ ox) (κ + 1) dg' (c.st a) s' a o) :
    IInv c1 (κ + 1) (addRec rc a κ ox) dg' := by
  have E := addRec_ext rc a κ ox
  have hk : κ ≤ κ + 1 := Nat.le_succ _
  -- the new entry
  have newE : ∀ w q j t, addRec rc a κ ox w q j = some t → rc w q j = some t ∨
      (w = a ∧ ox = some (q, j) ∧ t = κ ∧ rc a q j = none) := by
    intro w q j t h
    rcases ox with _ | ⟨q0, j0⟩
    · exact Or.inl h
    · simp only [addRec] at h
      split at h
      · rename_i hc; obtain ⟨rfl, rfl, rfl, hn⟩ := hc; cases h
        exact Or.inr ⟨rfl, rfl, rfl, hn⟩
      · exact Or.inl h
  refine ⟨?loc, ?clock, ?inj, ?own, ?born, ?dgRec, ?confLen, ?tab, ?ownRow, ?copies, ?msgs⟩
  · intro j
    by_cases h : j = a
    · subst h; rw [st_postA hp]; exact hloc
    · rw [st_postN hp h]; exact J.loc j
  · intro w q j t h
    rcases newE w q j t h with h | ⟨-, -, rfl, -⟩
    · exact Nat.lt_succ_of_lt (J.clock _ _ _ _ h)
    · exact Nat.lt_succ_self _
  · intro w q j q' j' t h1 h2
    rcases newE w q j t h1 with h1 | ⟨ew, e1, et, -⟩ <;>
      rcases newE w q' j' t h2 with h2 | ⟨-, e2, et', -⟩
    · exact J.inj _ _ _ _ _ _ h1 h2
    · have := J.clock _ _ _ _ h1; omega
    · have := J.clock _ _ _ _ h2; omega
    · rw [e1] at e2; cases e2; exact ⟨rfl, rfl⟩
  · intro w r j t h
    rcases newE w _ j t h with h | ⟨rfl, e1, rfl, hn⟩
    · obtain ⟨t0, h0, l0⟩ := J.own w r j t h
      exact ⟨t0, E.keep _ _ _ _ h0, l0⟩
    · rcases (hox _ _ e1).2.2 with eq | ⟨w', t', h'⟩
      · obtain rfl := rid32_inj eq
        exact ⟨_, h, Nat.le_refl _⟩
      · obtain ⟨t0, h0, -⟩ := J.own w' r j t' h'
        exact ⟨t0, E.keep _ _ _ _ h0, Nat.le_of_lt (J.clock _ _ _ _ h0)⟩
  · intro w q j t h
    rcases newE w q j t h with h | ⟨rfl, e1, -, -⟩
    · obtain ⟨r, hr, hlt⟩ := J.born w q j t h
      exact ⟨r, hr, Int.lt_of_lt_of_le hlt (hcrt r)⟩
    · exact (hox _ _ e1).2.1
  · intro q j D h
    rcases hdg q j D h with h | h
    · obtain ⟨r, t, hr, ht⟩ := J.dgRec q j D h
      exact ⟨r, t, hr, E.keep _ _ _ _ ht⟩
    · exact h
  · intro w
    by_cases hw : w = a
    · subst hw; rw [st_postA hp, hconf.1]; exact J.confLen w
    · rw [st_postN hp hw]; exact J.confLen w
  · intro w r j t h
    rcases newE w _ j t h with h | ⟨rfl, e1, -, -⟩
    · obtain ⟨hi, e2, l2⟩ := J.tab w r j t h
      by_cases hw : w = a
      · subst hw; rw [st_postA hp]
        obtain ⟨hi', e3, l3⟩ := hconf.2 _ _ e2
        exact ⟨hi', e3, Int.le_trans l2 l3⟩
      · rw [st_postN hp hw]; exact ⟨hi, e2, l2⟩
    · rw [st_postA hp]
      have := (hox _ _ e1).1
      rw [rid32_toNat] at this; exact this
  · intro w j h0 hlt
    by_cases hw : w = a
    · subst hw; rw [st_postA hp] at hlt; exact hownRow j h0 hlt
    · rw [st_postN hp hw] at hlt
      obtain ⟨t, ht⟩ := J.ownRow w j h0 hlt
      exact ⟨t, E.keep _ _ _ _ ht⟩
  · intro j q i cp hc
    unfold cpOf at hc
    by_cases h : j = a
    · subst h; rw [st_postA hp] at hc
      rcases hL.1 q i cp hc with h | h
      · exact copyI_mono E hk hd (J.copies j q i cp h)
      · exact h
    · rw [st_postN hp h] at hc; exact copyI_mono E hk hd (J.copies j q i cp hc)
  · intro d m hm
    rcases mem_post hp hm with h | h
    · exact msgI_mono E hk hd (J.msgs d m h)
    · exact hL.2 d m h

end Perennial.gryff.pureA.AI
