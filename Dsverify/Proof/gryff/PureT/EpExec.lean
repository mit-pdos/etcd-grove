/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureT/EpExec.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit A2 (totality): the executor (`exec`), `ExecuteOverwrite`, `Executed`.
-/
module

public import Dsverify.Proof.gryff.PureT.EpRecovery

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pure.tot

open model kahn

theorem Good.ofEq {st : Fin 3 → RState} {r : Fin 3} {S S' : RState} (h : Good st r S)
    (he : EqE S S') (hg : EqG S S') : Good st r S' :=
  ⟨h.mono.trans (Mono.of_eq he hg), h.si.congr he hg,
    by rw [← h.crt]; simp [RState.crt, he.crtInstance]⟩

/-- A copy's bookkeeping replaced (same proposals and candidate), its shape kept. -/
theorem Good.setLbS {st : Fin 3 → RState} {r : Fin 3} {S : RState} (h : Good st r S) {q i : w32}
    {c c' : Copy} (hc : S.inst q i = some c) {lb0 : LB} (hlb0 : c.lb = some lb0)
    (hcm : c'.cmds = c.cmds) (hst : c'.status = c.status) (hl : c'.leader = c.leader)
    (hs : c'.slot = c.slot) {lb : LB} (hlb : c'.lb = some lb)
    (hp : lb.clientProposals = lb0.clientProposals) (hri : lb.recoveryInst = lb0.recoveryInst) :
    Good st r (S.setInst q i c') := by
  obtain ⟨hb, hcok⟩ := h.copy hc
  obtain ⟨hcm0, hpre0, hl0, hs0, hst0, hlbok⟩ := hcok
  have hLB : LBok lb := by
    obtain ⟨a, b⟩ := hlbok lb0 hlb0
    exact ⟨hp ▸ a, hri ▸ b⟩
  refine h.setInst hb ⟨hcm ▸ hcm0, by rw [hst, hcm]; exact hpre0, hl ▸ hl0, hs ▸ hs0, hst ▸ hst0,
    (fun lb' h => by rw [hlb] at h; simp only [Option.some.injEq] at h; subst h; exact hLB)⟩ ?_ ?_
  · intro hq'
    obtain ⟨o1, -, o3⟩ := (h.si.ownOK i c (hq' ▸ hc))
    refine ⟨(by rw [hst]; exact o1), (fun h => by rw [hlb] at h; cases h), ?_⟩
    intro lb' h; rw [hlb] at h; simp only [Option.some.injEq] at h; subst h; rw [hp]; exact o3 lb0 hlb0
  · intro c1 h1; rw [hc] at h1; cases h1
    exact ⟨fun _ => Or.inl (by rw [hlb]; simp), fun hx => ⟨hst ▸ hx, hcm⟩⟩

/-- `handleExecuted` at a state `S` (the replica's, maybe with a store overwrite). -/
theorem handleExecuted_ok {st : Fin 3 → RState} {r : Fin 3} (hI : InvS st) {S : RState}
    (hG : Good st r S) (hid : S.id = rid32 r) (m : ExecutedM) (hrep : m.replica = rid32 r)
    (hb : InstB (Pf st) m.replica m.inst) :
    Ok (handleExecuted S m) (Post st r) := by
  cases hc : S.inst m.replica m.inst with
  | none =>
    tsimp [handleExecuted, hb.inBox hI, hc]
    exact Ok.ret (hG.post (by simp))
  | some c =>
    cases hlb : c.lb with
    | none =>
      tsimp [handleExecuted, hb.inBox hI, hc, hlb]
      exact Ok.ret (hG.post (by simp))
    | some lb =>
      have hown := hG.si.ownOK m.inst c (by rw [← hrep]; exact hc)
      have hp : lb.clientProposals ≠ [] := hown.2.2 lb hlb
      obtain ⟨p0, ps, hps⟩ := List.exists_cons_of_ne_nil hp
      have h1 : lb.clientProposals.head? = some p0 := by rw [hps]; rfl
      tsimp [handleExecuted, hb.inBox hI, hc, hlb, h1]
      split
      · refine Ok.ret (Good.post (hG.setLbS hc hlb rfl rfl rfl rfl rfl rfl rfl) ?_)
        intro x hx; simp at hx; subst hx; trivial
      · exact Ok.ret (Good.post (hG.setLbS hc hlb rfl rfl rfl rfl rfl rfl rfl) (by simp))

theorem stepExecuteOverwrite_ok (st : Fin 3 → RState) (r : Fin 3) (hI : InvS st)
    (m : ExecuteOverwriteM) (hm : MInv (Pf st) st r (.executeOverwrite m)) :
    Ok (stepExecuteOverwrite (st r) m) (Post st r) := by
  simp only [MInv] at hm
  obtain ⟨hb, cx, hcx, hx1, hx2⟩ := hm
  obtain ⟨L, hL, -⟩ := id hb
  have hid := (hI r).id
  have hG := (Good.refl (r := r) hI).ofEq (overwrite_eqE (st r) m.v m.t) (overwrite_eqG (st r) m.v m.t)
  by_cases hLr : L = r
  · subst hLr
    have hle : m.leader = ((st L).overwrite m.v m.t).id := by rw [ow_id, hid, hL]
    simp only [stepExecuteOverwrite]
    rw [if_pos hle]
    exact handleExecuted_ok hI hG (by rw [ow_id, hid]) _ hL hb
  · have hle : ¬ m.leader = ((st r).overwrite m.v m.t).id := by
      rw [ow_id, hid, hL]; exact fun h => hLr (rid32_inj h)
    simp only [stepExecuteOverwrite, hle, if_false, hL, sendPeer_eq, ow_id, hid, rid32_eq_iff, hLr]
    refine Ok.ret (hG.post ?_)
    intro x hx; simp only [List.mem_singleton] at hx; subst hx
    simp only [OutOk, MInv]
    refine ⟨?_, ?_, r, cx, ?_, hx1, hx2⟩
    · first | rfl | trivial | exact hL
    · first | exact hb | (rw [← hL]; exact hb)
    · rw [upd_self, ow_inst]; first | exact hcx | (rw [← hL]; exact hcx)

theorem stepExec_ok (st : Fin 3 → RState) (r : Fin 3) (hI : InvS st) (q i : w32) (c : Copy)
    (hbx : inBox q i = true) (hc : (st r).inst q i = some c) (hs : c.status = St.COMMITTED)
    (hg : execGuard (st r) (sint.Z q, sint.Z i)) :
    Ok (stepExec (st r) q i) (Post st r) := by
  have hid := (hI r).id
  obtain ⟨hb, hcm0, hpre0, hl0, hs0, hst0, hlbok⟩ := (hI r).inst q i c hc
  have hown : q = rid32 r → OwnOK c := fun hq => (hI r).ownOK i c (hq ▸ hc)
  have hGe : ∀ S : RState, Good st r S → S.inst q i = some c →
      Good st r (S.setInst q i { c with status := St.EXECUTED }) := by
    intro S hS hSc
    refine hS.setInst hb ⟨hcm0, fun h => by exfalso; simp only at h; revert h; decide, hl0, hs0,
      stOk_of (by simp only; decide), hlbok⟩ ?_ ?_
    · intro hq
      obtain ⟨o1, -, o3⟩ := hown hq
      exact ⟨(by simp only; decide), (fun _ => Or.inr rfl), o3⟩
    · intro c1 h1; rw [hSc] at h1; cases h1
      exact ⟨fun _ => Or.inr (Or.inr rfl), fun _ => ⟨rfl, rfl⟩⟩
  unfold stepExec
  simp only [hbx, hc, hs, hg, Bool.not_true, Bool.false_eq_true, if_false, not_true_eq_false,
    ne_eq, not_false_eq_true]
  split
  · exact Ok.ret ((hGe _ (Good.refl hI) hc).post (by simp))
  · rename_i c0 tail hcs
    rw [hid, sendTo_rid]
    simp only
    apply Ok.ret
    refine (hGe _ ?_ ?_).post ?_
    · exact (Good.refl hI).ofEq ⟨hid.symm, rfl, rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    · exact hc
    intro x hx; simp only [List.mem_singleton] at hx; subst hx
    simp only [OutOk, MInv]
    refine ⟨by rw [hl0, hs0]; exact hb, { c with status := St.EXECUTED }, ?_, rfl, by simp [hcs]⟩
    rw [upd_self, hl0, hs0]; simp

end Perennial.gryff.pure.tot
