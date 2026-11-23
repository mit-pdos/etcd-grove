/-
`handlePreAcceptReply`: The counting branch (below both quorums): `LbCountProof.inv_deliver_lbc` in mode 2.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.HPARBase

@[expose] public section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

open github_com.imdea_software.swiftpaxos_epaxos.kvs

namespace PARProof

open HStepProof HLocal SafeProof AuxProof PrepReplyProof LbCountProof

theorem par_bump_inst (σ : RState) (b : w32) : (bumpRecvBallot σ b).inst = σ.inst := by
  unfold bumpRecvBallot; split <;> rfl

theorem par_bump_fields (σ : RState) (b : w32) :
    (bumpRecvBallot σ b).id = σ.id ∧ (bumpRecvBallot σ b).peerOrder = σ.peerOrder ∧
    (bumpRecvBallot σ b).crtInstance = σ.crtInstance ∧
    (bumpRecvBallot σ b).conflicts = σ.conflicts ∧
    (bumpRecvBallot σ b).execedUpTo = σ.execedUpTo ∧ (bumpRecvBallot σ b).store = σ.store := by
  unfold bumpRecvBallot; split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- No reply carries a ballot above its target's `lastTriedBallot` (the nack branch is dead). -/
theorem par_dead (S : Sys) (fr i n : Nat) (hS : Inv S) (hi : i < nR) (p : PreAcceptReply)
    (hm : (S.sent fr i)[n]? = some (.preAcceptReply p)) (w : InstRec) (lb : LbRec)
    (hw : (S.rep i).inst (parX p) = some w) (hlb : w.lb = some lb)
    (h : lb.lastTriedBallot.slt p.ballot = true) : False := by
  have hrrv : Inv.repliesReportVotes S := let ⟨_, _, _, _, _, _, _, _, h, _⟩ := hS.1; h
  have hlbI : Inv.lbInv S := let ⟨_, _, _, _, _, _, _, _, _, _, h, _⟩ := hS.1; h
  obtain ⟨⟨v0, hv0⟩, -⟩ := hrrv.2.1 fr i p (mem_msgs_of_sent S hm)
  obtain ⟨-, -, -, a4, -⟩ := hlbI i hi _ w lb hw hlb
  have h1 := a4 _ _ (Or.inl hv0)
  have h2 := (slt_iff _ _).mp h
  omega

/-- The counting branch (below both quorums): `LbCountProof.inv_deliver_lbc` in mode 2. -/
theorem par_count (S : Sys) (fr i n : Nat) (hS : Inv S) (hi : i < nR) (hfr : fr < nR)
    (hidle : S.idle i) (hn : (fr, i, n) ∉ S.delivered) (p : PreAcceptReply)
    (hm : (S.sent fr i)[n]? = some (.preAcceptReply p)) (w : InstRec) (lb : LbRec)
    (hw : (S.rep i).inst (parX p) = some w) (hlb : w.lb = some lb)
    (hnc : stGe w.status stCOMMITTED = false) (hlt : lb.lastTriedBallot.slt w.bal = false)
    (hb : p.ballot = lb.lastTriedBallot) (hpa : isPA lb.status)
    (hfast : parFast lb p = false) (hslow : parSlow lb p = false)
    (h : hPreAcceptReply (S.rep i) p =
      ((bumpRecvBallot (S.rep i) p.ballot).setInst (parX p) { w with lb := some (parLb lb p) }, [])) :
    Inv (S.deliver fr i n (.preAcceptReply p)) := by
  obtain ⟨hfi, ⟨v0, hv0, hcmds⟩, hprep, hbal, -, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, kst,
    -, kball, kle, kdeps, ⟨Q, q1, q2, q3⟩, kae⟩ :=
    par_common S fr i n hS hi hfr hidle hn p hm w lb hw hlb hnc hlt hb hpa
  have hlbI : Inv.lbInv S := let ⟨_, _, _, _, _, _, _, _, _, _, h, _⟩ := hS.1; h
  obtain ⟨-, -, -, -, -, -, ⟨Q', q1', q2', q3'⟩, -, -⟩ := hlbI i hi _ w lb hw hlb
  have hne : (parLb lb p).preAcceptOKs ≠ W64 0 := by
    intro h0
    have : (parLb lb p).preAcceptOKs.toNat = 0 := by rw [h0]; rfl
    omega
  refine inv_deliver_lbc S fr i n (.preAcceptReply p) _ (parX p) w lb (parLb lb p) hS hi hidle hm h
    (by simp [RState.setInst, par_bump_inst])
    (by obtain ⟨e1, e2, e3, e4, e5, e6⟩ := par_bump_fields (S.rep i) p.ballot
        exact ⟨by simp [RState.setInst, e1], by simp [RState.setInst, e2],
          by simp [RState.setInst, e3], by simp [RState.setInst, e4],
          by simp [RState.setInst, e5], by simp [RState.setInst, e6]⟩)
    (AuxProof.bumpRB_cls _ _)
    hw hlb ⟨k1, k2, k3, k4, k5, hprep, k6, k7, k8, by rw [k1]; exact kle,
      Or.inr ⟨hpa, hne, kst⟩⟩
    kdeps
    (fun h1 _ => ⟨by rw [k1]; exact kball h1, v0, by rw [k1]; exact hv0, by rw [k2]; exact hcmds⟩)
    ⟨Q, q1, q2, fun a m' hq => by
      obtain ⟨c1, c2, c3, c4, c5, c6⟩ := q3 a m' hq
      refine ⟨c1, c2, ?_, c4, by rw [k1]; exact c5, c6⟩
      rcases c3 with c3 | ⟨e1, e2⟩
      · exact Or.inl c3
      · exact Or.inr ⟨e1, by rw [e2]⟩⟩
    ⟨Q', q1', by rw [k9]; exact q2', fun a ha => by
      obtain ⟨c1, c2, m', c3, c4, c5⟩ := q3' a ha
      exact ⟨c1, c2, m', Or.inl c3, c4, by rw [k1]; exact c5⟩⟩
    (fun _ _ hws hwb => by
      have := (hS.2.paLeader i hi _ w lb hw hlb hpa ⟨v0, hv0⟩ hnc hwb).2
      rw [hws] at this; exact acc_not_pa this)
    (fun h1 h2 => by rw [k1]; exact kae h1 h2)

end PARProof

end Perennial.github_com.imdea_software.swiftpaxos_epaxos.model
