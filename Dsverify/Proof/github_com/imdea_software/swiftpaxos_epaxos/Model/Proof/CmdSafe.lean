/-
SLOW-WIT (seventh agent): the command-level Paxos invariant (`InvPM.cmdSafe`) and the support of
Accepts (`InvPM.accSup`): stability lemmas and their consequence, "an Accept's commands are the
commands of every Phase 1 above it, unless the instance is committed" (`accept_forces`), which
makes the slow path's counted ACCEPTED no-op reply at a Phase 1 of the batch impossible.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.Safe

@[expose] public section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

open github_com.imdea_software.swiftpaxos_epaxos.kvs

namespace CmdSafeProof

open SafeProof

section
variable {S S' : Sys}

/-- `cmdBlocked` is kept by a step whose `bal`s only grow and whose new votes are at ballots at
least their voter's `bal`. -/
theorem cmdBlocked_mono' (hbal : ∀ r y w, (S.rep r).inst y = some w →
      ∃ w', (S'.rep r).inst y = some w' ∧ zz w.bal ≤ zz w'.bal)
    (hvote : ∀ q y c st u, S'.ev q (.vote y c st u) → S.ev q (.vote y c st u) ∨
      ∀ w, (S.rep q).inst y = some w → zz w.bal ≤ zz c)
    {x : InstId} {c : w32} {Z : List WCmd} (h : S.cmdBlocked x c Z) : S'.cmdBlocked x c Z := by
  obtain ⟨Q, hQ, hl, hQm⟩ := h
  refine ⟨Q, hQ, hl, fun a ha => ?_⟩
  obtain ⟨han, hnv, wa, hwa, hlt⟩ := hQm a ha
  obtain ⟨wa', hwa', hle⟩ := hbal a x wa hwa
  refine ⟨han, fun st u hs hv => ?_, wa', hwa', Int.lt_of_lt_of_le hlt hle⟩
  rcases hvote a x c st u hv with h | h
  · exact hnv st u hs h
  · have := h wa hwa; omega

theorem cmdBlocked_mono (hm : SafeMono S S') {x : InstId} {c : w32} {Z : List WCmd}
    (h : S.cmdBlocked x c Z) : S'.cmdBlocked x c Z :=
  cmdBlocked_mono' (fun r y w h => let ⟨w', h1, h2, _⟩ := hm.bal r y w h; ⟨w', h1, h2⟩)
    (fun q y c st u h => (hm.vote q y c st u h).imp id (fun h w hw => (h.1 w hw).1)) h

theorem cmdChosen_mono (hmono : ∀ r e, S.ev r e → S'.ev r e) {x : InstId} {c : w32}
    {Z : List WCmd} (h : S.cmdChosen x c Z) : S'.cmdChosen x c Z := by
  obtain ⟨Q, hQ, hl, hQm⟩ := h
  exact ⟨Q, hQ, hl, fun a ha =>
    let ⟨h1, st, u, h0, h2, h3⟩ := hQm a ha; ⟨h1, st, u, h0, hmono _ _ h2, h3⟩⟩

/-- The statement of `InvPM.cmdSafe`. -/
def CmdSafeP (S : Sys) : Prop :=
  ∀ ℓ x n v, S.ev ℓ (.phase1 x n v) →
    (∃ st u, isPA st ∧ S.ev ℓ (.vote x n st u) ∧ u.cmds = v.cmds) ∧
    ∀ c, realBal x c → zz c < zz n → ∀ Z, Z ≠ v.cmds → S.cmdBlocked x c Z

/-- `cmdSafe` under a step that makes no Phase 1 (events grow, `bal`s grow, new votes at least
the voter's `bal`). -/
theorem cmdSafe_frame' (hP : InvPM S)
    (hph : ∀ r y b v, S'.ev r (.phase1 y b v) → S.ev r (.phase1 y b v))
    (hmono : ∀ r e, S.ev r e → S'.ev r e)
    (hbal : ∀ r y w, (S.rep r).inst y = some w →
      ∃ w', (S'.rep r).inst y = some w' ∧ zz w.bal ≤ zz w'.bal)
    (hvote : ∀ q y c st u, S'.ev q (.vote y c st u) → S.ev q (.vote y c st u) ∨
      ∀ w, (S.rep q).inst y = some w → zz w.bal ≤ zz c) : CmdSafeP S' := by
  intro ℓ x n v h
  obtain ⟨⟨st, u, h1, h2, h3⟩, h4⟩ := hP.cmdSafe ℓ x n v (hph _ _ _ _ h)
  exact ⟨⟨st, u, h1, hmono _ _ h2, h3⟩,
    fun c hc hlt Z hZ => cmdBlocked_mono' hbal hvote (h4 c hc hlt Z hZ)⟩

/-- `cmdSafe` under a `SafeMono` step whose new Phase 1s satisfy it. -/
theorem cmdSafe_step (hP : InvPM S) (hm : SafeMono S S')
    (hph : ∀ r y b v, S'.ev r (.phase1 y b v) → S.ev r (.phase1 y b v) ∨
      ((∃ st u, isPA st ∧ S'.ev r (.vote y b st u) ∧ u.cmds = v.cmds) ∧
        ∀ c, realBal y c → zz c < zz b → ∀ Z, Z ≠ v.cmds → S.cmdBlocked y c Z)) :
    CmdSafeP S' := by
  intro ℓ x n v h
  rcases hph _ _ _ _ h with h | ⟨h1, h2⟩
  · obtain ⟨⟨st, u, g1, g2, g3⟩, g4⟩ := hP.cmdSafe ℓ x n v h
    exact ⟨⟨st, u, g1, hm.hist _ _ g2, g3⟩,
      fun c hc hlt Z hZ => cmdBlocked_mono hm (g4 c hc hlt Z hZ)⟩
  · exact ⟨h1, fun c hc hlt Z hZ => cmdBlocked_mono hm (h2 c hc hlt Z hZ)⟩

/-- `cmdSafe` under a `SafeMono` step that makes no Phase 1. -/
theorem cmdSafe_frame (hP : InvPM S) (hm : SafeMono S S')
    (hph : ∀ r y b v, S'.ev r (.phase1 y b v) → S.ev r (.phase1 y b v)) : CmdSafeP S' :=
  cmdSafe_step hP hm (fun r y b v h => Or.inl (hph r y b v h))

/-- `accSup` under a step whose new Accepts satisfy it (events only grow). -/
theorem accSup_step (hP : InvPM S) (hmono : ∀ r e, S.ev r e → S'.ev r e)
    (hacc : ∀ r y b v, S'.ev r (.accept y b v) → S.ev r (.accept y b v) ∨
      (∃ r' b' u, S.ev r' (.commit y b' u)) ∨
      ∃ c0, realBal y c0 ∧ zz c0 ≤ zz b ∧ S.cmdChosen y c0 v.cmds) :
    ∀ r x c v, S'.ev r (.accept x c v) → (∃ r' b u, S'.ev r' (.commit x b u)) ∨
      ∃ c0, realBal x c0 ∧ zz c0 ≤ zz c ∧ S'.cmdChosen x c0 v.cmds := by
  intro r x c v h
  have key : ∀ (h : (∃ r' b u, S.ev r' (.commit x b u)) ∨
      ∃ c0, realBal x c0 ∧ zz c0 ≤ zz c ∧ S.cmdChosen x c0 v.cmds),
      (∃ r' b u, S'.ev r' (.commit x b u)) ∨
      ∃ c0, realBal x c0 ∧ zz c0 ≤ zz c ∧ S'.cmdChosen x c0 v.cmds := by
    rintro (⟨r', b, u, h⟩ | ⟨c0, h1, h2, h3⟩)
    · exact Or.inl ⟨r', b, u, hmono _ _ h⟩
    · exact Or.inr ⟨c0, h1, h2, cmdChosen_mono hmono h3⟩
  rcases hacc _ _ _ _ h with h | h
  · exact key (hP.accSup r x c v h)
  · exact key h

/-- `accSup` under a step that makes no Accept. -/
theorem accSup_frame (hP : InvPM S) (hmono : ∀ r e, S.ev r e → S'.ev r e)
    (hacc : ∀ r y b v, S'.ev r (.accept y b v) → S.ev r (.accept y b v)) :
    ∀ r x c v, S'.ev r (.accept x c v) → (∃ r' b u, S'.ev r' (.commit x b u)) ∨
      ∃ c0, realBal x c0 ∧ zz c0 ≤ zz c ∧ S'.cmdChosen x c0 v.cmds :=
  accSup_step hP hmono (fun r y b v h => Or.inl (hacc r y b v h))

end

/-- Commands chosen at the command level at `c0` are the commands of every Phase 1 above `c0`. -/
theorem chosen_forces {S : Sys} (hP : InvPM S) {x : InstId} {c0 : w32} {Z : List WCmd}
    (hc0 : realBal x c0) (hch : S.cmdChosen x c0 Z) {ℓ : Nat} {n : w32} {v : Val}
    (hph : S.ev ℓ (.phase1 x n v)) (hlt : zz c0 < zz n) : v.cmds = Z := by
  refine Classical.byContradiction fun hne => ?_
  obtain ⟨Q, hQ, hl, hQm⟩ := (hP.cmdSafe ℓ x n v hph).2 c0 hc0 hlt Z (Ne.symm hne)
  obtain ⟨Q', hQ', hl', hQm'⟩ := hch
  obtain ⟨a, ha, ha'⟩ := meet_maj hQ hQ' (fun a h => (hQm a h).1) (fun a h => (hQm' a h).1) hl hl'
  obtain ⟨-, st, u, hs, hv, hu⟩ := hQm' a ha'
  exact (hQm a ha).2.1 st u hs hv hu

/-- **An Accept forces every Phase 1 above it** to carry its commands, unless the instance is
committed somewhere. -/
theorem accept_forces {S : Sys} (hP : InvPM S) {x : InstId} {r : Nat} {c : w32} {u : Val}
    (hacc : S.ev r (.accept x c u)) {ℓ : Nat} {n : w32} {v : Val}
    (hph : S.ev ℓ (.phase1 x n v)) (hlt : zz c < zz n) :
    v.cmds = u.cmds ∨ ∃ r' b w, S.ev r' (.commit x b w) := by
  rcases hP.accSup r x c u hacc with h | ⟨c0, h1, h2, h3⟩
  · exact Or.inr h
  · exact Or.inl (chosen_forces hP h1 h3 hph (Int.lt_of_le_of_lt h2 hlt))

end CmdSafeProof

end Perennial.github_com.imdea_software.swiftpaxos_epaxos.model
