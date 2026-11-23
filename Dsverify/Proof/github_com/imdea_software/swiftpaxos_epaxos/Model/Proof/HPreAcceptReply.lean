/-
`handlePreAcceptReply` keeps the invariant (`inv_deliver_preAcceptReply'`): the no-op branches
(`PrepReplyProof.inv_deliver_same`), the dead nack branch (`par_dead`: no reply is above the
bookkeeping's ballot), the counting branch (`par_count`), the slow path (`par_slow`) and the
fast path (`par_fast`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.HPARCount
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.HPARSlow
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.HPARFast

@[expose] public section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

open github_com.imdea_software.swiftpaxos_epaxos.kvs

namespace PARProof

open HStepProof HLocal PrepReplyProof

theorem bump_inst' (σ : RState) (b : w32) : (bumpRecvBallot σ b).inst = σ.inst := by
  unfold bumpRecvBallot; split <;> rfl

theorem bump_fields' (σ : RState) (b : w32) :
    (bumpRecvBallot σ b).id = σ.id ∧ (bumpRecvBallot σ b).peerOrder = σ.peerOrder ∧
    (bumpRecvBallot σ b).crtInstance = σ.crtInstance ∧
    (bumpRecvBallot σ b).conflicts = σ.conflicts ∧
    (bumpRecvBallot σ b).execedUpTo = σ.execedUpTo ∧ (bumpRecvBallot σ b).store = σ.store := by
  unfold bumpRecvBallot; split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **`handlePreAcceptReply` keeps the invariant.** -/
theorem inv_deliver_preAcceptReply' (S : Sys) (fr i n : Nat) (hS : Inv S) (hi : i < nR)
    (hfr : fr < nR) (hidle : S.idle i) (hn : (fr, i, n) ∉ S.delivered) (p : PreAcceptReply)
    (hm : (S.sent fr i)[n]? = some (.preAcceptReply p)) :
    Inv (S.deliver fr i n (.preAcceptReply p)) := by
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := bump_fields' (S.rep i) p.ballot
  rcases par_cases (S.rep i) p with h | h | ⟨w, lb, hw, hlb, hd⟩ |
    ⟨w, lb, hw, hlb, hnc, hlt, hb, hpa, ⟨hf, h⟩ | ⟨hf, hs, h⟩ | ⟨hf, hs, h⟩⟩
  · exact inv_deliver_same S fr i n _ _ hS hm h ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl ⟨rfl, rfl⟩
  · exact inv_deliver_same S fr i n _ _ hS hm h ⟨e1, bump_inst' _ _, e3, e4, e5, e6⟩ e2
      (AuxProof.bumpRB_cls _ _)
  · exact (par_dead S fr i n hS hi p hm w lb hw hlb hd).elim
  · exact par_fast S fr i n hS hi hfr hidle hn p hm w lb hw hlb hnc hlt hb hpa hf h
  · exact par_slow S fr i n hS hi hfr hidle hn p hm w lb hw hlb hnc hlt hb hpa hf hs h
  · exact par_count S fr i n hS hi hfr hidle hn p hm w lb hw hlb hnc hlt hb hpa hf hs h

end PARProof

end Perennial.github_com.imdea_software.swiftpaxos_epaxos.model
