/-
SLOW-WIT (seventh agent): the recovery's decision keeps the command-level invariants.
* `cmd_sub56`: a Phase 1 of sub-case 5 (the commands of a pre-accepted report at `maxVbal`) or 6
  (a no-op; every report NONE) is `cmdSafe`: above `maxVbal` the reporters voted nothing below
  `n`; at `maxVbal` every vote (by anyone) carries the commands of the Phase 1 there; below it
  that Phase 1 was `cmdSafe` (`InvPM.cmdSafe`).
* `sup_sub2`: an Accept of sub-case 2 (an ACCEPTED report at `maxVbal`) is supported (`accSup`)
  as the reported Accept is.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.Decide
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.CmdSafe

@[expose] public section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

open github_com.imdea_software.swiftpaxos_epaxos.kvs

namespace DecideProof

open SafeProof

section
variable {S : Sys} {x : InstId} {n : w32} {reps : List PReply}

/-- The reporters block commands `Z` at `c < n` if none of them voted for `Z` at `c`. -/
theorem cmdBlocked_reps (hrr : Inv.repliesReportVotes S) (hA : DecAux S) (hR : Reports S x n reps)
    {c : w32} {Z : List WCmd} (hc : zz c < zz n)
    (hno : ∀ e ∈ reps, ∀ st u, (isPA st ∨ st = stACCEPTED) →
      S.ev (toN e.m.acceptorId) (.vote x c st u) → u.cmds ≠ Z) :
    S.cmdBlocked x c Z := by
  refine ⟨reps.map (fun e => toN e.m.acceptorId), reps_nodup hrr hR (List.Sublist.refl _), ?_,
    fun a ha => ?_⟩
  · simp only [List.length_map]; have := hR.len; simp only [nR] at this ⊢; omega
  · simp only [List.mem_map] at ha
    obtain ⟨e, he, rfl⟩ := ha
    obtain ⟨han, hn, -, hx, E, hE⟩ := hR.mem e he
    obtain ⟨wa, hwa, hle⟩ := hA.bal _ e.m E han hE
    rw [hx, hn] at *
    exact ⟨han, hno e he, wa, hwa, by omega⟩

/-- **Sub-cases 5 and 6 keep `cmdSafe`**: the Phase 1's commands `Y` are those of a
pre-accepted report at `maxVbal`, if there is one. -/
theorem cmd_sub56 (hI : Inv0 S) (hA : DecAux S) (hP : InvPM S) (hxq : x.q < nR)
    (hR : Reports S x n reps)
    (hnov : ∀ r st u, isPA st → ¬ S.ev r (.vote x n st u))
    (hnc : ∀ e ∈ reps, stGe e.m.status stCOMMITTED = false)
    (hna : ∀ e ∈ reps, ¬ (e.m.vballot = reps.foldl maxStep (W32 (-1)) ∧ e.m.status = stACCEPTED))
    (Y : List WCmd)
    (hY : (∀ e ∈ reps, ¬ (e.m.vballot = reps.foldl maxStep (W32 (-1)) ∧ isPA e.m.status)) ∨
      ∃ e ∈ reps, e.m.vballot = reps.foldl maxStep (W32 (-1)) ∧ isPA e.m.status ∧
        Y = e.m.command) :
    ∀ c, realBal x c → zz c < zz n → ∀ Z, Z ≠ Y → S.cmdBlocked x c Z := by
  obtain ⟨-, -, -, -, -, hown, hop, hvf, hrr, hhi, -⟩ := hI
  have hfm := foldl_max reps (W32 (-1))
  intro c hc hcn Z hZ
  have hcase : zz (reps.foldl maxStep (W32 (-1))) = -1 ∨
      ∃ e0 ∈ reps, e0.m.vballot = reps.foldl maxStep (W32 (-1)) ∧ isPA e0.m.status := by
    rcases hfm.2.2 with h | ⟨e0, he0, h⟩
    · left; rw [h]; decide
    · obtain ⟨-, -, -, -, E0, hE0⟩ := hR.mem e0 he0
      rcases hA.status _ e0.m E0 hE0 with hs | hs | hs | hs
      · left; rw [← h]; exact hA.none _ e0.m E0 hE0 hs
      · exact Or.inr ⟨e0, he0, h, hs⟩
      · exact absurd ⟨h, hs⟩ (hna e0 he0)
      · exact absurd (stGe_of_committed hs) (by rw [hnc e0 he0]; simp)
  -- above `maxVbal` the reporters voted nothing below `n`
  have habove : zz (reps.foldl maxStep (W32 (-1))) < zz c → S.cmdBlocked x c Z := by
    intro hlt
    refine cmdBlocked_reps hrr hA hR hcn (fun e he st u _ hv => ?_)
    exfalso
    obtain ⟨-, hne, -, hxe, E, hE⟩ := hR.mem e he
    have := (rep_vote hrr hhi hne hxe hE hv hcn).2
    have := hfm.2.1 e he
    omega
  rcases hcase with hm1 | ⟨e0, he0, hv0, hpa0⟩
  · exact habove (by have := (zz_real hxq hc).1; omega)
  · rcases hY with hY | ⟨e, he, hve, hpae, rfl⟩
    · exact absurd ⟨hv0, hpa0⟩ (hY e0 he0)
    obtain ⟨-, hne, -, hxe, E, hE⟩ := hR.mem e he
    have hv := rep_reported hrr hxe hE (Or.inl hpae)
    rw [hve] at hv
    obtain ⟨ℓ0, v0, hph, hcv⟩ := hvf.1 _ x _ _ _ hv hpae
    simp only at hcv
    have hmn : zz (reps.foldl maxStep (W32 (-1))) < zz n := by
      have h1 := hA.vbal _ e.m E hE
      rw [hne, hve] at h1
      rcases Int.lt_or_eq_of_le h1 with h | h
      · exact h
      · rw [zz_inj h] at hv; exact absurd hv (hnov _ _ _ hpae)
    rcases Int.lt_trichotomy (zz c) (zz (reps.foldl maxStep (W32 (-1)))) with h | h | h
    · exact (hP.cmdSafe ℓ0 x _ v0 hph).2 c hc h Z (by rw [← hcv]; exact hZ)
    · have hc' : c = reps.foldl maxStep (W32 (-1)) := zz_inj h
      subst hc'
      refine cmdBlocked_reps hrr hA hR hcn (fun e' _ st u hs hv' => ?_)
      rcases hs with hs | hs
      · obtain ⟨ℓ1, v1, hph1, hc1⟩ := hvf.1 _ x _ _ _ hv' hs
        obtain ⟨-, rfl, -⟩ := hop.1 _ _ _ _ _ _ hph1 hph
        rw [hc1, ← hcv]; exact Ne.symm hZ
      · subst hs
        obtain ⟨ℓ1, hacc1⟩ := hvf.2 _ x _ _ hv'
        rw [hop.2.2 _ _ _ _ _ _ hph hacc1, ← hcv]; exact Ne.symm hZ
    · exact habove h

/-- **Sub-case 2 keeps `accSup`**: the reported Accept (at `maxVbal ≤ n`) is supported. -/
theorem sup_sub2 (hI : Inv0 S) (hA : DecAux S) (hP : InvPM S) (hR : Reports S x n reps)
    {e : PReply} (he : e ∈ reps) (hes : e.m.status = stACCEPTED) :
    (∃ r' b u, S.ev r' (.commit x b u)) ∨
      ∃ c0, realBal x c0 ∧ zz c0 ≤ zz n ∧ S.cmdChosen x c0 e.m.command := by
  obtain ⟨-, -, -, -, -, -, -, hvf, hrr, -⟩ := hI
  obtain ⟨-, hne, -, hxe, E, hE⟩ := hR.mem e he
  have hv := rep_reported hrr hxe hE (Or.inr hes)
  rw [hes] at hv
  obtain ⟨ℓ0, hacc⟩ := hvf.2 _ x _ _ hv
  have hle := hA.vbal _ e.m E hE
  rw [hne] at hle
  rcases hP.accSup ℓ0 x _ _ hacc with h | ⟨c0, h1, h2, h3⟩
  · exact Or.inl h
  · exact Or.inr ⟨c0, h1, Int.le_trans h2 hle, h3⟩

end

/-- What `prepDecide` chose outside sub-cases 1-3: a pre-accepted reply at `maxVbal` (sub-case
5) or nothing, there being no such reply (sub-case 6). -/
theorem prepDecide_56 (reps : List PReply) (mx : w32) (lr : Bool) (rep : w32)
    (h1 : (prepDecide reps mx lr rep).1 ≠ 1) (h2 : (prepDecide reps mx lr rep).1 ≠ 2)
    (h3 : (prepDecide reps mx lr rep).1 ≠ 3) :
    ((prepDecide reps mx lr rep).2 = none ∧ ∀ e ∈ reps, isPreAcceptedAt mx e = false) ∨
    ∃ e, (prepDecide reps mx lr rep).2 = some e ∧ e ∈ reps ∧ isPreAcceptedAt mx e = true := by
  revert h1 h2 h3
  unfold prepDecide
  split
  · intro h1; exact absurd rfl h1
  split
  · intro _ h2; exact absurd rfl h2
  split
  · intro _ _ h3; exact absurd rfl h3
  split
  · rename_i e' he'
    intro _ _ _
    exact Or.inr ⟨e', rfl, List.mem_of_find?_eq_some he', List.find?_some he'⟩
  · rename_i h'
    intro _ _ _
    rw [List.find?_eq_none] at h'
    exact Or.inl ⟨rfl, fun e he => by simpa using h' e he⟩

end DecideProof

end Perennial.github_com.imdea_software.swiftpaxos_epaxos.model
