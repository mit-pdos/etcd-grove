/-
`InvExec` (p-modelexec) under the deliveries: only `handleCommit` re-proposes (`reprops_nil`);
a handler step that changes one record (`x` at `i`), keeps the commands of an executed one and
keeps its bookkeeping's proposals (or drops them) keeps `InvExec` (`invExec_hs`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.HStep

@[expose] public section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

open github_com.imdea_software.swiftpaxos_epaxos.kvs HStepProof

namespace ExecOrd

/-! ## Re-proposals -/

theorem rp_sp1 (σ : RState) a b c d e f :
    (startPhase1 σ a b c d e f).2.filterMap Out.reprop = [] := by
  unfold startPhase1; simp [Out.reprop]

theorem rp_nack (σ : RState) x inst lb : (nackBranch σ x inst lb).2.filterMap Out.reprop = [] := by
  unfold nackBranch; simp only []; repeat (first | split | simp [Out.reprop])

theorem snd_ite {c : Prop} [Decidable c] (a b : RState × List Out) :
    (if c then a else b).2 = if c then a.2 else b.2 := by split <;> rfl

theorem fm_ite {c : Prop} [Decidable c] (a b : List Out) :
    (if c then a else b).filterMap Out.reprop =
      if c then a.filterMap Out.reprop else b.filterMap Out.reprop := by split <;> rfl

macro "rpt" : tactic => `(tactic| repeat (first | rfl | (simp only [snd_ite, fm_ite, ite_self, List.filterMap_cons, List.filterMap_nil, List.filterMap_append, Out.reprop, rp_nack, rp_sp1, List.append_nil, List.nil_append, Option.map]; done) | split | dsimp only))

theorem rp_prepare (σ : RState) (m : Prepare) : (hPrepare σ m).2.filterMap Out.reprop = [] := by
  unfold hPrepare; simp [Out.reprop]

theorem rp_accept (σ : RState) (m : Accept) : (hAccept σ m).2.filterMap Out.reprop = [] := by
  unfold hAccept; simp only []; split <;> (try split) <;> (try split) <;> simp [Out.reprop]

theorem rp_preAccept (σ : RState) (m : PreAccept) :
    (hPreAccept σ m).2.filterMap Out.reprop = [] := by
  unfold hPreAccept; simp only []; repeat (first | split | simp [Out.reprop])

theorem rp_par (σ : RState) (m : PreAcceptReply) :
    (hPreAcceptReply σ m).2.filterMap Out.reprop = [] := by
  unfold hPreAcceptReply; rpt

theorem rp_ar (σ : RState) (m : AcceptReply) :
    (hAcceptReply σ m).2.filterMap Out.reprop = [] := by
  unfold hAcceptReply; rpt

theorem rp_pr (σ : RState) (m : PrepareReply) :
    (hPrepareReply σ m).2.filterMap Out.reprop = [] := by
  unfold hPrepareReply; rpt

/-- Only `handleCommit` re-proposes. -/
theorem reprops_nil (σ : RState) (m : Msg) (h : ∀ c, m ≠ .commit c) :
    (hMsg σ m).2.filterMap Out.reprop = [] := by
  cases m with
  | prepare p => exact rp_prepare σ p
  | prepareReply p => exact rp_pr σ p
  | preAccept p => exact rp_preAccept σ p
  | preAcceptReply p => exact rp_par σ p
  | accept p => exact rp_accept σ p
  | acceptReply p => exact rp_ar σ p
  | commit p => exact absurd rfl (h p)
  | tryPreAccept p => rfl
  | tryPreAcceptReply p => rfl
  | beacon _ => rfl
  | beaconReply _ => rfl

theorem deliver_chan (S : Sys) (fr i n : Nat) (m : Msg) :
    (S.deliver fr i n m).proposeChan =
      fun r => S.proposeChan r ++ (if r = i then (hMsg (S.rep i) m).2.filterMap Out.reprop else []) := by
  funext r
  have hd : S.deliver fr i n m =
      ({ S with delivered := S.delivered ++ [(fr, i, n)] } : Sys).applyStep i
        ((hMsg (S.rep i) m).1, (hMsg (S.rep i) m).2) := rfl
  rw [hd, Sys.applyStep_proposeChan]

theorem deliver_chan_nil (S : Sys) (fr i n : Nat) (m : Msg) (h : ∀ c, m ≠ .commit c) :
    (S.deliver fr i n m).proposeChan = S.proposeChan := by
  rw [deliver_chan, reprops_nil _ _ h]; funext r; split <;> simp

/-! ## A handler step changing one record -/

/-- **Frame for a handler step.** -/
theorem invExec_hs {S S' : Sys} {i : Nat} {σ' : RState} {E : List Event}
    {snd : Nat → List Msg} {pend : Option Bcast} {x : InstId} {w' : InstRec}
    (h0 : Inv0 S) (hX : InvExec S) (hH : HS S S' i σ' E snd pend) (hidle : S.idle i)
    (hagr : Inv.agreement S') (hchan : S'.proposeChan = S.proposeChan)
    (hrec : ∀ r y, (r ≠ i ∨ y ≠ x) → (S'.rep r).inst y = (S.rep r).inst y)
    (hx : (S'.rep i).inst x = some w')
    (hex : ∀ w, (S.rep i).inst x = some w → w.status = stEXECUTED → w'.cmds = w.cmds)
    (hcp : ∀ lb', w'.lb = some lb' → lb'.clientProposals ≠ none →
      ∃ w lb, (S.rep i).inst x = some w ∧ w.lb = some lb ∧ lb.clientProposals ≠ none) :
    InvExec S' := by
  refine invExec_step h0 hX (fun r e h => hH.ev_old h) hagr hH.execLog hH.execCur hH.execIdx
    hH.gexec hH.owner hchan hH.ops (fun r _ y hy => ?_) (fun r _ hne y => ?_) ?_
  · by_cases hc : r = i ∧ y = x
    · obtain ⟨rfl, rfl⟩ := hc
      obtain ⟨w, hw, hs⟩ := hy
      simp only [cmdsAt, hx, hw, Option.bind_some, hex w hw hs]
    · have : r ≠ i ∨ y ≠ x := by
        by_cases h1 : r = i
        · exact Or.inr (fun h2 => hc ⟨h1, h2⟩)
        · exact Or.inl h1
      simp only [cmdsAt, hrec r y this]
  · have : r ≠ i := by intro e; subst e; exact hne hidle.2
    simp only [cmdsAt, hrec r y (Or.inl this)]
  · intro y w'' lb'' h2 hl2 hne
    by_cases hc : y.q = i ∧ y = x
    · obtain ⟨h1, rfl⟩ := hc
      rw [h1, hx] at h2; cases h2
      obtain ⟨w, lb, hw, hlb, hne'⟩ := hcp lb'' hl2 hne
      exact ⟨w, lb, by rw [h1]; exact hw, hlb, hne'⟩
    · have hne2 : y.q ≠ i ∨ y ≠ x := by
        by_cases h1 : y.q = i
        · exact Or.inr (fun h2 => hc ⟨h1, h2⟩)
        · exact Or.inl h1
      rw [hrec _ _ hne2] at h2
      exact ⟨w'', lb'', h2, hl2, hne⟩

end ExecOrd

end Perennial.github_com.imdea_software.swiftpaxos_epaxos.model
