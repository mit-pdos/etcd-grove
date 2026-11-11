/-
Lean-first (no Rocq counterpart). **A leader's response of its term that does not move its match index:
the receive line** (2026-11-11, trace-check Q8 stage 1 slice 22b, `notes/decisions.md`, "Q8 stage 1
(slice 22b)").

A rejected `MsgAppResp` (raft's `MaybeDecrTo` moves `Next` only) and a `MsgHeartbeatResp` (raft's flow
control and read acknowledgements; `Match` untouched) at a leader of their term. The specification's
`HandleAppendEntriesResponse` records the response in `respSrv`: nothing for a rejection, the sender's
match index raised to the response's `0` for a heartbeat's (`msgAbs` gives it no match index), which a
leader's match indices (`SimServerR`'s leader clause, `uint.Z` of raft's) already reach. So the share's
server is unchanged up to `toC` (`toC_respSrv_keep`), and the receive line's phase step keeps the pinned
idle phase (`phaseStepR_leadResp`); its facts are a dropped response's (`fxPresR_staleResp`).

**Not here** (`notes/decisions.md`, "Q8 stage 1 (slice 22b)"): the paths. After the receive line both
send an append to the responder through `leaderGates`' `"Hgsapp"`, whose premises (`AppOk`, the commit,
the destination, `Match ≤ Index`) do not bound the message's `RejectHint`, which the send line's
`TraceEv.Ok` reads (raft's `maybeSendAppend` sends `0`).
-/
module

public import Proof.go_etcd_io.raft.v3.TracedRaftStepRecvCand

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 TraceSim

section pure
variable [GooseExts]

/-- **A response that does not move a match index the share reads**: a rejection, or a success at match
index `0` where the server's match indices (on `S`) are non-negative. -/
theorem toC_respSrv_keep (S : Etcdraft.SetIds) (a : Etcdraft.Server) (ma : Etcdraft.Msg)
    (hty : ma.type = .appendEntriesResponse) (hm : ma.success = false ∨ ma.matchIndex = 0)
    (hnn : ∀ k ∈ S, 0 ≤ a.matchIndex k) :
    toC S (respSrv a ma) = toC S a := by
  unfold respSrv
  rw [if_neg (by rw [hty]; decide)]
  split
  · rename_i hs
    have h0 : ma.matchIndex = 0 := by
      rcases hm with h | h
      · rw [h] at hs; cases hs
      · exact h
    simp only [toC]
    congr 1
    apply List.map_congr_left
    intro k hk
    split
    · rename_i hks; subst hks; rw [h0]; exact Int.max_eq_left (hnn _ hk)
    · rfl
  · rfl

/-- The responses of this file, at the specification: an append response that does not raise a match
index. -/
theorem msgAbs_leadResp {C : List w64} {bl : Nat} {m : Msg} {ma : Etcdraft.Msg}
    (hty : (m.ty = .appResp ∧ m.reject = true) ∨ m.ty = .heartbeatResp)
    (hma : TraceSim.msgAbs C bl m = some ma) :
    ma.type = .appendEntriesResponse ∧ (ma.success = false ∨ ma.matchIndex = 0) := by
  rcases hty with ⟨h, hr⟩ | h <;> simp [TraceSim.msgAbs, h] at hma <;> subst hma
  · simp [hr]
  · simp

end pure

section steps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **A leader's rejected append response or heartbeat response of its term: the receive line's phase
step** (the pinned idle phase kept: `respSrv` changes no match index the share reads,
`toC_respSrv_keep`; `lineEffect_resp`). -/
theorem phaseStepR_leadResp (id : w64) (c : CfgM) (s : NState) (ty : MsgType) (m : MessageM)
    (ents : List EntryM) (evt : w64) (C0 : List w64) (cs0 : ServerC) (P0 : List Etcdraft.Msg)
    (ma : Etcdraft.Msg) (hev : RecvEvTy (absMsg ty m ents) evt) (hto : m.To' = id)
    (hresp : (ty = .appResp ∧ m.Reject' = true) ∨ ty = .heartbeatResp)
    (hterm : m.Term' = s.term) (hlead : s.role = .leader)
    (hb : (absMsg ty m ents).NumsBelow traceNumBound)
    (hma : TraceSim.msgAbs C0 C0.length (absMsg ty m ents) = some ma) :
    PhaseStepR id c ma (SendEvOf evt id s c (absMsg ty m ents)) (fun _ => False) (recvPhantoms ma)
      (IdlePin s C0 cs0 P0) (IdlePin s C0 cs0 P0) := by
  rintro C cs P ⟨rfl, rfl, rfl, hI⟩ ⟨hin, hout, hC, -⟩ e he
  have hI' := hI
  obtain ⟨a1, ha1, hR0, hs, hP, bt, bc, bl⟩ := hI'
  have hpre : s.role ≠ .preCandidate := by rw [hlead]; decide
  have hdst : (absMsg ty m ents).dst = id := hto
  have he' : SendEvOf evt (absMsg ty m ents).dst s c (absMsg ty m ents) e := by rw [hdst]; exact he
  obtain ⟨bmt, bk, blt, bi, bmc⟩ := numsBelow_63 hb
  have hnb := recvEvTy_notBoot hev
  refine ⟨he.2.1, sendEvOf_notBoot he hnb.1 hnb.2.1 hnb.2.2.1,
    recvLine_pred C e s c _ evt ma hev he' hout bmt bi blt bk bmc hma, ?_⟩
  intro a ha
  have hR : SimServerR C C.length (toPState s) a := simServerR_toC (ha1.trans ha.symm) hR0
  have hC' : (absMsg ty m ents).dst ∈ C := by rw [hdst]; exact hC
  have hty' : ((absMsg ty m ents).ty = .appResp ∧ (absMsg ty m ents).reject = true) ∨
      (absMsg ty m ents).ty = .heartbeatResp := by
    rcases hresp with ⟨rfl, hr⟩ | rfl
    · exact .inl ⟨rfl, hr⟩
    · exact .inr rfl
  obtain ⟨hmty, hms⟩ := msgAbs_leadResp hty' hma
  have hlr : (toPState s).role = .leader := by simp [toPState, hlead, proleRole]
  have hnn : ∀ k ∈ confAbs C, 0 ≤ a.matchIndex k := by
    intro k hk
    obtain ⟨w, hw, rfl⟩ := mem_confAbs_inv C k hk
    rw [hR.2.2.2.2.2.2.2.2.2.2 hlr w hw]
    exact uint_Z_nonneg _
  have hkeep := toC_respSrv_keep (confAbs C) a ma hmty hms hnn
  have hph := recvPhantoms_resp ma a (.inl hmty)
  have hrev : (absMsg ty m ents).ty = .appResp ∧ evt = W64 12 ∨ (absMsg ty m ents).ty = .voteResp ∧ evt = W64 16 ∨
      (absMsg ty m ents).ty = .heartbeatResp ∧ (absMsg ty m ents).reject = false ∧ evt = W64 12 := by
    rcases hev with ⟨h, -⟩ | ⟨h, -, -⟩ | ⟨h, -⟩ | h
    · rcases hty' with ⟨h', -⟩ | h' <;> rw [h'] at h <;> cases h
    · rcases hty' with ⟨h', -⟩ | h' <;> rw [h'] at h <;> cases h
    · rcases hty' with ⟨h', -⟩ | h' <;> rw [h'] at h <;> cases h
    · exact h
  refine ⟨respSrv a ma, [], ⟨rfl, by rw [hkeep]; exact ha, by rw [List.append_nil], by rw [hkeep, ha, List.append_nil]; exact hI⟩,
    fun x hx => by simp at hx, ?_⟩
  rw [← hdst]
  simp only [List.nil_append, hph, List.foldl_nil]
  exact lineEffect_resp C e s c _ evt a ma _ hrev he' hin hout hC' hR hs hpre hterm bt bc bl bi hma

/-- **Its facts** (`FxPresR` at `recvPhantoms m`, none for a response): a dropped response's, the pinned
phase kept (`fxPresR_staleResp`). -/
theorem fxPresR_leadResp (γ : RaftNames) (id : w64) (ma : Etcdraft.Msg) (E : TraceEv → Prop) (s : NState)
    (C0 : List w64) (cs0 : ServerC) (P0 : List Etcdraft.Msg) (hty : ma.type = .appendEntriesResponse) :
    ⊢ FxPresR (GF := GF) γ id ma E (fun _ => False) (recvPhantoms ma) (IdlePin s C0 cs0 P0) (IdlePin s C0 cs0 P0) :=
  fxPresR_staleResp γ id ma E _ _ (.inl hty) (by
    rintro C cs P cs' P' ⟨-, rfl, rfl, -⟩ ⟨-, rfl, hP, -⟩
    exact ⟨rfl, by simpa using hP.symm⟩)

end steps

end EtcdGrove
end Perennial
