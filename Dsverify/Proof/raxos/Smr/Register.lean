/-
The registration of a request under the SMR invariant (package `kit`): the pure facts of the
invariant are kept when a fresh request id is added to the registry and its client's counter
grows.
-/
module

public import Dsverify.Proof.raxos.Smr.Step
public import Dsverify.Proof.raxos.Smr.OpId

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.raxos

open Iris Perennial.raxos.pure

/-- The facts of `smrInv` (as stated there). -/
def SmrFacts (D : List (List GoString)) (Reg : GMap GoString RegEntry)
    (Res : GMap GoString (KOut)) (Cnt : GMap Nat Nat) : Prop :=
  (∀ c n, Cnt !! c = some n → c < 6 ∧ n ≤ 20) ∧
      Reg !! go!"nil" = some RegEntry.nil ∧
      (∀ x e, Reg !! x = some e → e = RegEntry.nil → x = go!"nil") ∧
      (∀ x, Reg !! x = some RegEntry.sum → ∃ p : List Nat, x = summaryId p ∧ sumPerm p) ∧
      (∀ x c j inp q t, Reg !! x = some (.op c j inp q t) →
        x = opId c j ∧ inputOk inp ∧ ∃ n, Cnt !! c = some n ∧ j < n) ∧
      (∀ x, (Res !! x).isSome ↔
        (∃ c j inp q tok, Reg !! x = some (.op c j inp q tok)) ∧
          x ∈ (execLog (fun y => (Reg !! y).map (RegEntry.batch y)) D).done) ∧
      (∀ x ∈ (execLog (fun y => (Reg !! y).map (RegEntry.batch y)) D).done,
        ∃ e, Reg !! x = some e ∧ msg.batchFit (e.batch x)) ∧
      (∀ x o, Res !! x = some o → ∃ c j inp q tok, Reg !! x = some (.op c j inp q tok) ∧
        (execLog (fun y => (Reg !! y).map (RegEntry.batch y)) D).results x = some [ansOf inp o] ∧
        ∀ v, o = ⟨true, v⟩ → v ≠ [] ∧ v ≠ go!"nil")

/-- Client `c`'s next request id is not registered. -/
theorem reg_fresh (D : List (List GoString)) (Reg : GMap GoString RegEntry)
    (Res : GMap GoString (KOut)) (Cnt : GMap Nat Nat) (c n : Nat)
    (hf : SmrFacts D Reg Res Cnt) (hc : Cnt !! c = some n) : Reg !! opId c n = none := by
  cases h : Reg !! opId c n with
  | none => rfl
  | some e =>
    cases e with
    | nil => exact absurd (hf.2.2.1 _ _ h rfl) (opid.opId_ne_nil c n)
    | sum =>
      obtain ⟨p, hp, -⟩ := hf.2.2.2.1 _ h
      exact absurd hp.symm (sumid.summaryId_ne_opId p c n)
    | op c' j' inp q t =>
      obtain ⟨hx, _, m, hm, hlt⟩ := hf.2.2.2.2.1 _ _ _ _ _ _ h
      obtain ⟨rfl, rfl⟩ := opid.opId_inj hx
      rw [hc] at hm; cases hm; omega

/-- A registered-later id is not in the executed log. -/
theorem fresh_not_done (D : List (List GoString)) (Reg : GMap GoString RegEntry)
    (Res : GMap GoString (KOut)) (Cnt : GMap Nat Nat) (x : GoString)
    (hf : SmrFacts D Reg Res Cnt) (hx : Reg !! x = none) :
    ∀ y ∈ D.flatten, y ≠ x := by
  intro y hy h
  subst h
  obtain ⟨e, he, _⟩ := hf.2.2.2.2.2.2.1 y ((execLog_done _ _ _).2 hy)
  rw [hx] at he; cases he

theorem execLog_insert (D : List (List GoString)) (Reg : GMap GoString RegEntry) (x : GoString)
    (e : RegEntry) (hx : ∀ y ∈ D.flatten, y ≠ x) :
    execLog (fun y => ((<[x := e]> Reg) !! y).map (RegEntry.batch y)) D =
      execLog (fun y => (Reg !! y).map (RegEntry.batch y)) D := by
  apply execLog_congr
  intro y hy
  rw [GMap.lookup_insert_ne _ _ (Ne.symm (hx y hy))]

/-- The facts after registering client `c`'s `n`-th request. -/
theorem facts_register (D : List (List GoString)) (Reg : GMap GoString RegEntry)
    (Res : GMap GoString (KOut)) (Cnt : GMap Nat Nat) (c n : Nat)
    (hcn : c < 6 ∧ n < 20)
    (inp : KIn) (hinp : inputOk inp) (q tok : GName)
    (hf : SmrFacts D Reg Res Cnt) (hc : Cnt !! c = some n) :
    SmrFacts D (<[opId c n := RegEntry.op c n inp q tok]> Reg) Res (<[c := n + 1]> Cnt) := by
  have hfr := reg_fresh D Reg Res Cnt c n hf hc
  have hnd := fresh_not_done D Reg Res Cnt _ hf hfr
  have hex := execLog_insert D Reg (opId c n) (RegEntry.op c n inp q tok) hnd
  have hdone : ∀ y ∈ (execLog (fun y => (Reg !! y).map (RegEntry.batch y)) D).done,
      y ≠ opId c n := fun y hy => hnd y ((execLog_done _ _ _).1 hy)
  have hRes : Res !! opId c n = none := by
    cases h : Res !! opId c n with
    | none => rfl
    | some o =>
      obtain ⟨_, _, _, _, _, he⟩ := ((hf.2.2.2.2.2.1 _).1 (by rw [h]; rfl)).1
      rw [hfr] at he; cases he
  obtain ⟨h0, h1, h2, hs, h3, h4, h5, h6⟩ := hf
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c' n' hc'
    by_cases hcc : c' = c
    · subst hcc; rw [GMap.lookup_insert] at hc'; cases hc'; omega
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hcc)] at hc'; exact h0 c' n' hc'
  · rw [GMap.lookup_insert_ne _ _ (opid.opId_ne_nil c n)]; exact h1
  · intro x e hx he
    by_cases hxe : x = opId c n
    · subst hxe; rw [GMap.lookup_insert] at hx; cases hx; cases he
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hxe)] at hx; exact h2 x e hx he
  · intro x hx
    by_cases hxe : x = opId c n
    · subst hxe; rw [GMap.lookup_insert] at hx; cases hx
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hxe)] at hx; exact hs x hx
  · intro x c' j inp' q' t hx
    by_cases hxe : x = opId c n
    · subst hxe
      rw [GMap.lookup_insert] at hx; cases hx
      exact ⟨rfl, hinp, n + 1, GMap.lookup_insert _ _ _, by omega⟩
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hxe)] at hx
      obtain ⟨hx1, hx2, m, hm, hlt⟩ := h3 x c' j inp' q' t hx
      refine ⟨hx1, hx2, ?_⟩
      by_cases hcc : c' = c
      · subst hcc; rw [hc] at hm; cases hm
        exact ⟨n + 1, GMap.lookup_insert _ _ _, by omega⟩
      · exact ⟨m, by rw [GMap.lookup_insert_ne _ _ (Ne.symm hcc)]; exact hm, hlt⟩
  · intro x
    rw [hex, h4 x]
    by_cases hxe : x = opId c n
    · subst hxe
      constructor
      · rintro ⟨_, h⟩; exact absurd rfl (hdone _ h)
      · rintro ⟨_, h⟩; exact absurd rfl (hdone _ h)
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hxe)]
  · intro x hx
    rw [hex] at hx
    rw [GMap.lookup_insert_ne _ _ (Ne.symm (hdone x hx))]
    exact h5 x hx
  · intro x o hx
    obtain ⟨c', j', inp', q', tok', hR, hr⟩ := h6 x o hx
    have hxe : x ≠ opId c n := by rintro rfl; rw [hRes] at hx; cases hx
    refine ⟨c', j', inp', q', tok', ?_, ?_⟩
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hxe)]; exact hR
    · rw [hex]; exact hr

/-- The facts after registering an epoch summary's id `summaryId p`. -/
theorem facts_register_sum (D : List (List GoString)) (Reg : GMap GoString RegEntry)
    (Res : GMap GoString (KOut)) (Cnt : GMap Nat Nat) (p : List Nat) (hp : sumPerm p)
    (hf : SmrFacts D Reg Res Cnt) (hfr : Reg !! summaryId p = none) :
    SmrFacts D (<[summaryId p := RegEntry.sum]> Reg) Res Cnt := by
  have hnd := fresh_not_done D Reg Res Cnt _ hf hfr
  have hex := execLog_insert D Reg (summaryId p) RegEntry.sum hnd
  have hdone : ∀ y ∈ (execLog (fun y => (Reg !! y).map (RegEntry.batch y)) D).done,
      y ≠ summaryId p := fun y hy => hnd y ((execLog_done _ _ _).1 hy)
  obtain ⟨h0, h1, h2, hs, h3, h4, h5, h6⟩ := hf
  have hne : ∀ x, Reg !! x ≠ none → x ≠ summaryId p := by
    rintro x hx rfl; exact hx hfr
  refine ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [GMap.lookup_insert_ne _ _ (sumid.summaryId_ne_nil p)]; exact h1
  · intro x e hx he
    by_cases hxe : x = summaryId p
    · subst hxe; rw [GMap.lookup_insert] at hx; cases hx; cases he
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hxe)] at hx; exact h2 x e hx he
  · intro x hx
    by_cases hxe : x = summaryId p
    · subst hxe; exact ⟨p, rfl, hp⟩
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hxe)] at hx; exact hs x hx
  · intro x c' j inp' q' t hx
    by_cases hxe : x = summaryId p
    · subst hxe; rw [GMap.lookup_insert] at hx; cases hx
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hxe)] at hx; exact h3 x c' j inp' q' t hx
  · intro x
    rw [hex, h4 x]
    by_cases hxe : x = summaryId p
    · subst hxe
      constructor
      · rintro ⟨_, h⟩; exact absurd rfl (hdone _ h)
      · rintro ⟨⟨_, _, _, _, _, h⟩, _⟩; rw [GMap.lookup_insert] at h; cases h
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hxe)]
  · intro x hx
    rw [hex] at hx
    rw [GMap.lookup_insert_ne _ _ (Ne.symm (hdone x hx))]
    exact h5 x hx
  · intro x o hx
    obtain ⟨c', j', inp', q', tok', hR, hr⟩ := h6 x o hx
    have hxe : x ≠ summaryId p := hne x (by rw [hR]; simp)
    refine ⟨c', j', inp', q', tok', ?_, ?_⟩
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hxe)]; exact hR
    · rw [hex]; exact hr

end Perennial.raxos
