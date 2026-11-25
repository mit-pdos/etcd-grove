/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureT/EpReplies.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit A2 (totality): the proposer's reply handlers (`PreAcceptReply`, `PreAcceptOK`,
`AcceptReply`).
-/
module

public import Dsverify.Proof.gryff.PureT.EpSteps

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pure.tot

open model kahn

/-- A copy with bookkeeping replaced by one with bookkeeping of the same proposals and candidate. -/
theorem Good.setLb {st : Fin 3 → RState} {r : Fin 3} {S : RState} (h : Good st r S) {q i : w32}
    {c c' : Copy} (hc : S.inst q i = some c) {lb0 : LB} (hlb0 : c.lb = some lb0)
    (hne : c.status ≠ St.EXECUTED) (hcm : c'.cmds = c.cmds) (hl : c'.leader = c.leader)
    (hs : c'.slot = c.slot) (hst : stOk c'.status) (hnn : c'.status ≠ St.NONE)
    (hpre : (c'.status = St.PREACCEPTED ∨ c'.status = St.PREACCEPTED_EQ) → c'.cmds ≠ [])
    (hsome : c'.lb ≠ none)
    (hlbs : ∀ lb, c'.lb = some lb →
      lb.clientProposals = lb0.clientProposals ∧ lb.recoveryInst = lb0.recoveryInst) :
    Good st r (S.setInst q i c') := by
  obtain ⟨lb, hlb⟩ := Option.ne_none_iff_exists'.1 hsome
  obtain ⟨hp, hri⟩ := hlbs lb hlb
  obtain ⟨hb, hcok⟩ := h.copy hc
  obtain ⟨hcm0, -, hl0, hs0, -, hlbok⟩ := hcok
  have hLB : LBok lb := by
    obtain ⟨a, b⟩ := hlbok lb0 hlb0
    exact ⟨hp ▸ a, hri ▸ b⟩
  refine h.setInst hb ⟨hcm ▸ hcm0, hpre, hl ▸ hl0, hs ▸ hs0, hst,
    (fun lb' h => by rw [hlb] at h; simp only [Option.some.injEq] at h; subst h; exact hLB)⟩ ?_ ?_
  · intro hq'
    obtain ⟨-, -, o3⟩ := (h.si.ownOK i c (hq' ▸ hc))
    refine ⟨hnn, (fun h => by rw [hlb] at h; cases h), ?_⟩
    intro lb' h; rw [hlb] at h; simp only [Option.some.injEq] at h; subst h; rw [hp]; exact o3 lb0 hlb0
  · intro c1 h1; rw [hc] at h1; cases h1
    exact ⟨fun _ => Or.inl (by rw [hlb]; simp), fun hx => absurd hx hne⟩

theorem bcast_out {st : Fin 3 → RState} {r : Fin 3} {S' : RState} (hid : S'.id = rid32 r)
    (msg : Msg) (P : Fin 3 → Nat) (hm : ∀ d, d ≠ r → MInv P (upd st r S') d msg) :
    OkO (bcast S' msg) (fun outs => ∀ x ∈ outs, OutOk P (upd st r S') x) := by
  rw [bcast_eq hid]
  refine OkO.some ?_
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨d, hd, rfl⟩ := hx
  exact hm d (peers_ne hd)

/-- `r`'s own copy (in its new state) with bookkeeping: the proposer of a request. -/
theorem PropC.self {st : Fin 3 → RState} {r : Fin 3} {S' : RState} {q i : w32} {c : Copy}
    (hc : S'.inst q i = some c) (hl : c.lb ≠ none) : PropC (upd st r S') r q i :=
  ⟨c, by rw [upd_self]; exact hc, Or.inl hl⟩

/-- An Accept broadcast by `r` for its copy. -/
theorem accept_out {st : Fin 3 → RState} {r : Fin 3} {S' : RState} (hid : S'.id = rid32 r)
    {q i : w32} (hb : InstB (Pf st) q i) (hl : ∃ c, S'.inst q i = some c ∧ c.lb ≠ none)
    (b : w32) {cmds : List Cmd} (hcm : cmdsOk cmds = true) (seq : w32) (deps : Deps) (base : ValTag) :
    OkO (bcastAccept S' q i b cmds seq deps base)
      (fun outs => ∀ x ∈ outs, OutOk (Pf st) (upd st r S') x) := by
  obtain ⟨c, hc, hl⟩ := hl
  unfold bcastAccept
  refine bcast_out hid _ _ (fun d hd => ?_)
  simp only [MInv]
  exact ⟨⟨r, Ne.symm hd, hid, PropC.self hc hl⟩, hb, hcm⟩

/-- A PreAccept broadcast by `r` for its copy. -/
theorem preAccept_out {st : Fin 3 → RState} {r : Fin 3} {S' : RState} (hid : S'.id = rid32 r)
    {q i : w32} (hb : InstB (Pf st) q i) (hl : ∃ c, S'.inst q i = some c ∧ c.lb ≠ none)
    (b : w32) {cmds : List Cmd} (hcm : cmdsOk cmds = true) (hne : cmds ≠ []) (seq : w32)
    (deps : Deps) (base : ValTag) :
    OkO (bcastPreAccept S' q i b cmds seq deps base)
      (fun outs => ∀ x ∈ outs, OutOk (Pf st) (upd st r S') x) := by
  obtain ⟨c, hc, hl⟩ := hl
  unfold bcastPreAccept
  refine bcast_out hid _ _ (fun d hd => ?_)
  simp only [MInv]
  exact ⟨⟨r, Ne.symm hd, hid, PropC.self hc hl⟩, hb, hcm, hne⟩

/-- A Prepare broadcast by `r` for its copy. -/
theorem prepare_out {st : Fin 3 → RState} {r : Fin 3} {S' : RState} (hid : S'.id = rid32 r)
    {q i : w32} (hb : InstB (Pf st) q i) (hl : ∃ c, S'.inst q i = some c ∧ c.lb ≠ none)
    (b : w32) :
    OkO (bcastPrepare S' q i b) (fun outs => ∀ x ∈ outs, OutOk (Pf st) (upd st r S') x) := by
  obtain ⟨c, hc, hl⟩ := hl
  unfold bcastPrepare
  refine bcast_out hid _ _ (fun d hd => ?_)
  simp only [MInv]
  exact ⟨⟨r, Ne.symm hd, hid, PropC.self hc hl⟩, hb⟩

/-- A Commit broadcast by `r`. -/
theorem commit_out {st : Fin 3 → RState} {r : Fin 3} {S' : RState} (hid : S'.id = rid32 r)
    {q i : w32} (hb : InstB (Pf st) q i) {cmds : List Cmd} (hcm : cmdsOk cmds = true) (seq : w32)
    (deps : Deps) (base : ValTag) :
    OkO (bcastCommit S' q i cmds seq deps base)
      (fun outs => ∀ x ∈ outs, OutOk (Pf st) (upd st r S') x) := by
  unfold bcastCommit
  refine bcast_out hid _ _ (fun d hd => ?_)
  simp only [MInv]
  exact ⟨hb, hcm⟩

set_option hygiene false in
/-- The side conditions of `Good.setLb` for a copy whose status and commands are kept. -/
macro "lbclose" : tactic => `(tactic| first
  | rfl
  | exact hcok.2.2.2.2.1
  | ((try simp only); rw [hacc]; first | decide | exact stOk_of (by decide))
  | (simp only; exact hcok.2.1)
  | exact hcok.2.1
  | simp
  | (intro lb' h; simp only [Option.some.injEq] at h; subst h; exact ⟨rfl, rfl⟩))

set_option hygiene false in
/-- The proposer's Accept branch: `bcastAccept` of its accepted copy, outputs checked. -/
macro "accleaf" : tactic => `(tactic|
  (split
   · rename_i outs heq
     refine Ok.ret (Good.post ?_
       (OkO.of_eq (accept_out (by simpa using hid) hb (by simp) _ hcok.1 _ _ _) heq))
     refine Good.setLb (Good.refl hI) hc hlb hne ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
     all_goals first
       | rfl
       | exact stOk_of (by simp only; decide)
       | (simp only; decide)
       | (intro h; exfalso; simp only at h; revert h; decide)
       | simp
       | (intro lb' h; simp only [Option.some.injEq] at h; subst h; exact ⟨rfl, rfl⟩)
   · rename_i hx
     exact (OkO.not_none (accept_out (by simpa using hid) hb (by simp) _ hcok.1 _ _ _) hx).elim))

theorem stepAcceptReply_ok (st : Fin 3 → RState) (r : Fin 3) (hI : InvS st) (m : AcceptReplyM)
    (hm : MInv (Pf st) st r (.acceptReply m)) : Ok (stepAcceptReply (st r) m) (Post st r) := by
  simp only [MInv] at hm
  obtain ⟨hb, c, hc, hlbc⟩ := hm
  obtain ⟨q', hq', -⟩ := id hb
  have hcok := ((hI r).inst _ _ c hc).2
  tsimp [stepAcceptReply, hb.inBox hI, hc]
  split
  · exact Ok.ret ((Good.refl hI).post (by simp))
  · next hacc0 =>
    have hacc : c.status = St.ACCEPTED := Classical.not_not.1 hacc0
    have hne : c.status ≠ St.EXECUTED := by rw [hacc]; decide
    split
    · exact Ok.ret ((Good.refl hI).post (by simp))
    · split
      · next lb hlb =>
        split
        · refine Ok.ret (Good.post (Good.setLb (Good.refl hI) hc hlb hne ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
            (by simp))
          all_goals lbclose
        · split
          · exact leaderCommit_ok hI (Good.refl hI) hq' hc hne rfl rfl rfl hlb rfl rfl
          · refine Ok.ret (Good.post (Good.setLb (Good.refl hI) hc hlb hne ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
              (by simp))
            all_goals lbclose
      · next hx =>
        exfalso
        rcases hlbc with h | h
        · apply h; cases h' : c.lb
          · rfl
          · exact absurd h' (hx _)
        · rw [hacc] at h; revert h; simp only [committedSt]; decide

theorem stepPreAcceptReply_ok (st : Fin 3 → RState) (r : Fin 3) (hI : InvS st)
    (m : PreAcceptReplyM) (hm : MInv (Pf st) st r (.preAcceptReply m)) :
    Ok (stepPreAcceptReply (st r) m) (Post st r) := by
  simp only [MInv] at hm
  obtain ⟨hb, c, hc, hlbc⟩ := hm
  obtain ⟨q', hq', -⟩ := id hb
  have hcok := ((hI r).inst _ _ c hc).2
  have hid := (hI r).id
  tsimp [stepPreAcceptReply, hb.inBox hI, hc]
  split
  · exact Ok.ret ((Good.refl hI).post (by simp))
  · next hpre0 =>
    have hpre : c.status = St.PREACCEPTED := Classical.not_not.1 hpre0
    have hne : c.status ≠ St.EXECUTED := by rw [hpre]; decide
    split
    · exact Ok.ret ((Good.refl hI).post (by simp))
    · split
      · next lb hlb =>
        have hacc := hpre
        split
        · refine Ok.ret (Good.post (Good.setLb (Good.refl hI) hc hlb hne ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
            (by simp))
          all_goals lbclose
        · split
          · split
            · accleaf
            · refine Ok.ret (Good.post (Good.setLb (Good.refl hI) hc hlb hne ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
                (by simp))
              all_goals lbclose
          · split
            · refine leaderCommit_ok hI (Good.refl hI) hq' hc hne ?_ ?_ ?_ hlb ?_ ?_ <;> rfl
            · split
              · accleaf
              · refine Ok.ret (Good.post (Good.setLb (Good.refl hI) hc hlb hne ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
                  (by simp))
                all_goals lbclose
      · next hx =>
        exfalso
        rcases hlbc with h | h
        · apply h; cases h' : c.lb
          · rfl
          · exact absurd h' (hx _)
        · rw [hpre] at h; revert h; simp only [committedSt]; decide

theorem stepPreAcceptOK_ok (st : Fin 3 → RState) (r : Fin 3) (hI : InvS st)
    (m : PreAcceptOKM) (hm : MInv (Pf st) st r (.preAcceptOK m)) :
    Ok (stepPreAcceptOK (st r) m) (Post st r) := by
  simp only [MInv] at hm
  obtain ⟨hb, c, hc, hlbc⟩ := hm
  have hq' : rid32 r = rid32 r := rfl
  have hcok := ((hI r).inst _ _ c hc).2
  have hid := (hI r).id
  tsimp [stepPreAcceptOK, hid, hb.inBox hI, hc, setInst_id]
  split
  · exact Ok.ret ((Good.refl hI).post (by simp))
  · next hpre0 =>
    have hpre : c.status = St.PREACCEPTED := Classical.not_not.1 hpre0
    have hne : c.status ≠ St.EXECUTED := by rw [hpre]; decide
    have hacc := hpre
    split
    · exact Ok.ret ((Good.refl hI).post (by simp))
    · split
      · next lb hlb =>
        split
        · refine leaderCommit_ok hI (Good.refl hI) hq' hc hne ?_ ?_ ?_ hlb ?_ ?_ <;> rfl
        · split
          · accleaf
          · refine Ok.ret (Good.post (Good.setLb (Good.refl hI) hc hlb hne ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
              (by simp))
            all_goals lbclose
      · next hx =>
        exfalso
        rcases hlbc with h | h
        · apply h; cases h' : c.lb
          · rfl
          · exact absurd h' (hx _)
        · rw [hpre] at h; revert h; simp only [committedSt]; decide

end Perennial.gryff.pure.tot
