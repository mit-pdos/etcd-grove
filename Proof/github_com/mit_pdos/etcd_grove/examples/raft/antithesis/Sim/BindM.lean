/-
Lean-first (no Rocq counterpart).

# Parity B2: C3 over the announced commits (`BindingOkM`)

`BindingOkM` is `BindingOk` with `TermLenOk`'s leader clause read at the leader's announced commit
(`MemCommit`, B 139). With no `mem` queued at a node the two clauses agree there
(`TermLenOkM.lead_nil`), and with none queued anywhere the two relations agree
(`bindingOkM_of_B1`, `BindingOkM.toB1`) (#33 parity B2, Sim round 11).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.StmtsB2
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.LiftC

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace AntSim

open AntCheck

section bindM
variable [GooseExts]

theorem BindingOkM.termLenOkM {R : RunCfg} {dec : CCDec} {S : State} (h : BindingOkM R dec S) :
    TermLenOkM R.N S :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem BindingOkM.ledConfOk {R : RunCfg} {dec : CCDec} {S : State} (h : BindingOkM R dec S) :
    LedConfOk R dec S :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem BindingOkM.tlSorted {R : RunCfg} {dec : CCDec} {S : State} (h : BindingOkM R dec S) :
    TlSorted S :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem BindingOkM.bootTermOk {R : RunCfg} {dec : CCDec} {S : State} (h : BindingOkM R dec S) :
    BootTermOk R.N S :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- The leader clause at a node with no `mem` queued is `TermLenOk`'s. -/
theorem TermLenOkM.lead_nil {N : Nat} {S : State} (h : TermLenOkM N S) {n : Fin N}
    (hq : S.queue[n.val]! = []) (hl : S.role[n.val]! = leader) :
    (termAt (S.log[n.val]!) (S.commitIndex[n.val]!) = S.currentTerm[n.val]! →
      S.commitIndex[n.val]! ≤ tlOld S.termLen (S.currentTerm[n.val]!)) ∧
    tlOld S.termLen (S.currentTerm[n.val]!) ≤ S.commitIndex[n.val]! := by
  obtain ⟨c, hc, h1, h2⟩ := h.2 n hl
  rw [memCommit_nil hq] at hc
  cases hc
  exact ⟨h1, h2⟩

/-- The leader clause at a node from `TermLenOk`'s, with no `mem` queued there. -/
theorem termLenOkM_lead_of {N : Nat} {S : State} {n : Fin N} (hq : S.queue[n.val]! = [])
    (h : (termAt (S.log[n.val]!) (S.commitIndex[n.val]!) = S.currentTerm[n.val]! →
      S.commitIndex[n.val]! ≤ tlOld S.termLen (S.currentTerm[n.val]!)) ∧
    tlOld S.termLen (S.currentTerm[n.val]!) ≤ S.commitIndex[n.val]!) :
    ∃ c, S.memCommit n.val = .ok c ∧
      (termAt (S.log[n.val]!) c = S.currentTerm[n.val]! → c ≤ tlOld S.termLen (S.currentTerm[n.val]!)) ∧
      tlOld S.termLen (S.currentTerm[n.val]!) ≤ c :=
  ⟨_, memCommit_nil hq, h⟩

theorem termLenOkM_of_B1 {N : Nat} {S : State} (hq : ∀ i : Fin N, S.queue[i.val]! = [])
    (h : TermLenOk N S) : TermLenOkM N S :=
  ⟨h.1, fun n hl => termLenOkM_lead_of (hq n) (h.2 n hl)⟩

theorem TermLenOkM.toB1 {N : Nat} {S : State} (hq : ∀ i : Fin N, S.queue[i.val]! = [])
    (h : TermLenOkM N S) : TermLenOk N S :=
  ⟨h.1, fun n hl => h.lead_nil (hq n) hl⟩

/-- `BindingOk` with the leader clause replaced. -/
theorem bindingOkM_of {R : RunCfg} {dec : CCDec} {S : State} (hb : BindingOk R dec S)
    (ht : TermLenOkM R.N S) : BindingOkM R dec S := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, -, h16, h17, h18⟩ := hb
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, ht, h16, h17, h18⟩

theorem BindingOkM.toB1' {R : RunCfg} {dec : CCDec} {S : State} (hb : BindingOkM R dec S)
    (ht : TermLenOk R.N S) : BindingOk R dec S := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, -, h16, h17, h18⟩ := hb
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, ht, h16, h17, h18⟩

theorem bindingOkM_of_B1 {R : RunCfg} {dec : CCDec} {S : State}
    (hq : ∀ i : Fin R.N, S.queue[i.val]! = []) (hb : BindingOk R dec S) : BindingOkM R dec S :=
  bindingOkM_of hb (termLenOkM_of_B1 hq hb.termLenOk)

theorem BindingOkM.toB1 {R : RunCfg} {dec : CCDec} {S : State}
    (hq : ∀ i : Fin R.N, S.queue[i.val]! = []) (hb : BindingOkM R dec S) : BindingOk R dec S :=
  hb.toB1' (hb.termLenOkM.toB1 hq)

theorem BindingOkM.factsWf {R : RunCfg} {dec : CCDec} {S : State} (hb : BindingOkM R dec S) :
    FactsWf R S :=
  ⟨hb.2.2.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.2.2.2.1⟩

/-- `GC` keeps `BindingOkM` (`gc_bindingOk`'s proof: `GC` moves no role, log, commit, term or queue). -/
theorem gc_bindingOkM {R : RunCfg} {dec : CCDec} {S : State} {g : List Fact} {o : List VoteRec} (hc : S.cfg = R.cfg)
    (hb : BindingOkM R dec S) (hg : S.garbage = .ok g) (ho : S.oldVotes = .ok o) :
    BindingOkM R dec (gcRes S g o) := by
  obtain ⟨hb1, hb4, hb5, hb6, hb7, hb8, hb9, hb10, hb11, hb12, hb13, hb14, hb15, hb16, hb17, hb18,
    hb19⟩ := hb
  refine ⟨hb1, hb4, hb5, hb6, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hb15, ?_, ?_, ?_, hb19.1,
    hb19.2.1, fun f hf hty => hb19.2.2 f (gcRes_msgs_sub hf) hty⟩
  · intro n l hl
    exact hb7 n l (gcRes_get_ok hl)
  · intro n a ha
    exact hb8 n a (gcRes_msgs_sub ha)
  · intro p hp
    obtain ⟨hp1, hp2⟩ := gcRes_ledLog_sub hp
    obtain ⟨l, hl, hlt⟩ := hb9 p hp1
    exact ⟨l, gcRes_leaders_keep hl (by rw [hlt]; exact hp2), hlt⟩
  · intro n l hl
    exact hb10 n l (gcRes_leaders_sub hl)
  · intro f hf
    exact hb11 f (gcRes_msgs_sub hf)
  · intro v hv
    exact hb12 v (gcRes_votes_sub hv)
  · intro n hv
    exact gcRes_votes_keep hc ho (hb13 n hv) n rfl (Int.le_refl _)
  · intro n a ha
    exact hb14 n a (gcRes_msgs_sub ha)
  · intro j
    obtain ⟨h1, h2⟩ := hb16 j
    refine ⟨?_, h2⟩
    rcases h1 with h | h | h
    · exact .inl h
    · cases hov : S.over (S.confirmed[j.val]!).term
      · exact .inr (.inl ((gcRes_has (g := g) (o := o) hov).trans h))
      · refine .inr (.inr fun i => ?_)
        refine Int.lt_of_not_ge fun hle => ?_
        rw [over_false (S := S) (t := (S.confirmed[j.val]!).term) hc i hle] at hov; cases hov
    · exact .inr (.inr h)
  · refine ⟨fun T hT => ?_, hb17.2⟩
    rcases hb17.1 T hT with ⟨l, hl, hlt⟩ | h
    · cases hov : S.over l.term
      · exact .inl ⟨l, gcRes_leaders_keep hl hov, hlt⟩
      · refine .inr fun i => ?_
        refine Int.lt_of_not_ge fun hle => ?_
        rw [over_false (S := S) (t := l.term) hc i (by rw [hlt]; exact hle)] at hov; cases hov
    · exact .inr h
  · intro T hT
    change (S.ledLog.without S.staleLed).has T = true at hT
    rw [has_without] at hT
    cases hs : S.staleLed.contains T
    · rw [hs] at hT
      obtain ⟨l, a, cs, h1, h2, h3, h4, h5⟩ := hb18 T (by simpa using hT)
      refine ⟨l, a, cs, ?_, ?_, h3, ?_, h5⟩
      · show (S.ledLog.without S.staleLed).get T = _; rw [get_without, hs]; exact h1
      · show (S.ledAt.without S.staleLed).get T = _; rw [get_without, hs]; exact h2
      · show (S.ledConf.without S.staleLed).get T = _; rw [get_without, hs]; exact h4
    · rw [hs] at hT; cases hT

end bindM

end AntSim
end EtcdGrove
end Perennial
