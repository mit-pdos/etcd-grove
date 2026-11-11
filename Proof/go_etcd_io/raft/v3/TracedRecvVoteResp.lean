/-
Lean-first (no Rocq counterpart). **A candidate's vote response of its term, its receive line**
(2026-11-10, trace-check amendment A3, Q17 (d); `notes/decisions.md`, "Amendment A3 (Q17)"): the
sufficiency check of the relaxed tally (`TallyGranted` in `SimServerR`). The receive line's pieces
for a `MsgVoteResp` of the candidate's term, granting or refusing, from a voter raft has or has not
heard from: the step to raft's state after `recordVote` (which `poll` reaches in all three outcomes;
the won and lost lines follow it, the path proof's):
- `simServerR_respSrv_cand`: the idle relation after raft's `recordVote` and the specification's
  `HandleRequestVoteResponse` (`respSrv`), by `sim_recordVote`;
- `specInv_respCand`: `SpecInv` after it (`CandS`: an unpersisted candidate with no granted vote has
  no granted vote of its term in `messages`, so the received one refuses or the candidate persisted);
- `simFx_respCand`, `fxPresR_voteRespCand`: the receive line's facts (`FxPresR`, no phantom);
- `phaseStepR_voteRespCand`: its phase step, from the pinned idle phase at `s` to the one at raft's
  state after `recordVote`.
The path proof (the bundle's `MsgVoteResp` at a candidate: `poll`, then the won and lost lines) is
not here.
-/
module

public import Proof.go_etcd_io.raft.v3.TracedRaftStepRecv

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 TraceSim

section pure
variable [GooseExts]

/-- **The idle relation after a vote response at a candidate** (amendment A3): raft's
`recordVote` (a known voter's response ignored) against the specification's recording (`respSrv`). -/
theorem simServerR_respSrv_cand {C : List w64} {bl : Nat} {p : PState} {a : Etcdraft.Server}
    (ma : Etcdraft.Msg) (src : w64) (h : SimServerR C bl p a) (hc : p.role = .candidate)
    (hty : ma.type = .requestVoteResponse) (hsrc : ma.source = idAbs src) :
    SimServerR C bl { p with votes := recordVote p.votes src ma.voteGranted } (respSrv a ma) := by
  unfold respSrv
  simp only [hty, ↓reduceIte]
  rw [hsrc]
  exact sim_recordVote C bl p a src ma.voteGranted h hc

/-- **`SpecInv` after a vote response of a candidate's term** (amendment A3): the response consumed
from `messages`, the tally recorded (`respSrv`). Only `CandS` reads the tally (an unpersisted
candidate's granted votes empty), and a granted response of its term in `messages` means the
candidate persisted (`CandS` again). -/
theorem specInv_respCand (σ : Etcdraft.State) (i : Etcdraft.ID) (ma : Etcdraft.Msg)
    (h : TraceSpecInv.SpecInv σ) (hi : i ∈ σ.server) (hm : ma ∈ σ.messages.domain) (hd : ma.dest = i)
    (hty : ma.type = .requestVoteResponse) (ht : ma.term = (σ.s i).currentTerm) :
    TraceSpecInv.SpecInv (withNode σ i (respSrv (σ.s i) ma) (fun b => b.without ma) _root_.id) := by
  have hdis := TraceSpecInv.specInv_discard ma h
  have hs : ∀ j, (withNode σ i (respSrv (σ.s i) ma) (fun b => b.without ma) _root_.id).s j =
      if j = i then respSrv (σ.s i) ma else (σ.discard ma).s j := fun _ => rfl
  refine TraceSpecInv.specInv_congr_v hdis rfl rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    (try (intro j; rw [hs]; split <;> (try subst_vars) <;> simp only [respSrv, hty, ↓reduceIte] <;> rfl))
  intro j hcand hnp hg0
  rw [hs]
  split
  · rename_i hj; subst hj
    simp only [respSrv, hty, ↓reduceIte]
    cases hv : ma.voteGranted
    · simp only [Bool.false_eq_true, ↓reduceIte]; exact hg0
    · exfalso
      obtain ⟨-, -, c3⟩ := h.2.2.2.1 j hi hcand
      rcases c3 with hp | ⟨-, -, c5, -⟩
      · exact hnp hp
      · have := c5 ma hm hd hty hv
        rw [ht] at this; exact Int.lt_irrefl _ this
  · exact hg0

end pure

section cand
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **The facts after a vote response of a candidate's term** (amendment A3). -/
theorem simFx_respCand (γ : RaftNames) (C : List w64) (σ : Etcdraft.State) (i : Etcdraft.ID) (ma : Etcdraft.Msg)
    (hi : i ∈ σ.server) (hm : ma ∈ σ.messages.domain) (hd : ma.dest = i)
    (hty : ma.type = .requestVoteResponse) (ht : ma.term = (σ.s i).currentTerm) :
    simFx (GF := GF) γ C σ ⊢ simFx γ C (withNode σ i (respSrv (σ.s i) ma) (fun b => b.without ma) _root_.id) := by
  have hF : ∀ j, ((withNode σ i (respSrv (σ.s i) ma) (fun b => b.without ma) _root_.id).s j).log = (σ.s j).log ∧
      ((withNode σ i (respSrv (σ.s i) ma) (fun b => b.without ma) _root_.id).s j).commitIndex = (σ.s j).commitIndex ∧
      ((withNode σ i (respSrv (σ.s i) ma) (fun b => b.without ma) _root_.id).s j).currentTerm = (σ.s j).currentTerm ∧
      ((withNode σ i (respSrv (σ.s i) ma) (fun b => b.without ma) _root_.id).s j).state = (σ.s j).state ∧
      ((withNode σ i (respSrv (σ.s i) ma) (fun b => b.without ma) _root_.id).s j).config = (σ.s j).config := by
    intro j
    have hj : (withNode σ i (respSrv (σ.s i) ma) (fun b => b.without ma) _root_.id).s j =
        if j = i then respSrv (σ.s i) ma else σ.s j := rfl
    rw [hj]
    split
    · rename_i hj; subst hj
      obtain ⟨h1, h2, h3, h4, h5, -⟩ := respSrv_fields (σ.s j) ma
      exact ⟨h1, h2, h3, h4, h5⟩
    · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hsub : ∀ x ∈ (withNode σ i (respSrv (σ.s i) ma) (fun b => b.without ma) _root_.id).messages.domain ++
      (withNode σ i (respSrv (σ.s i) ma) (fun b => b.without ma) _root_.id).pendingMessages.domain,
      x ∈ σ.messages.domain ++ σ.pendingMessages.domain := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact List.mem_append_left _ (TraceSpecInv.mem_without _ _ _ hx)
    · exact List.mem_append_right _ hx
  iintro Hfx
  iunfold simFx at Hfx
  iunfold simFx
  icases Hfx with ⟨#Hal, #Hmf, #Hq, %Hp⟩
  obtain ⟨hsi, hu, hsh, has⟩ := Hp
  isplitl
  · iunfold allFacts at Hal
    iunfold allFacts
    imodintro
    iintro %j %hj
    obtain ⟨h1, h2, h3, h4, -⟩ := hF (idAbs j)
    iapply srvFacts_congr γ C j _ _ h1 h2 h3 h4
    iapply Hal $$ %j %hj
  isplitl
  · imodintro
    iintro %x %hx
    iapply Hmf
    ipureintro
    exact hsub x hx
  isplitl
  · iapply quorumLogF_congr γ C σ (withNode σ i (respSrv (σ.s i) ma) (fun b => b.without ma) _root_.id) rfl
      (fun k => (hF k).1) (fun k => (hF k).2.1) (fun k => by rw [(hF k).2.2.1]; exact Int.le_refl _) $$ Hq
  ipureintro
  refine ⟨specInv_respCand σ i ma hsi hi hm hd hty ht,
    msgsUniq_mono hsub hu, fun x hx => hsh x (hsub x hx), ?_⟩
  intro m hm' hty' j hj hlj htj hs k e he
  rw [(hF j).1]
  rw [(hF j).2.2.2.1] at hlj; rw [(hF j).2.2.1] at htj
  exact has m (hsub m hm') hty' j hj hlj htj hs k e he

/-- **The facts of a vote response's receive line at a candidate of its term** (`FxPresR` at
`recvPhantoms m`, none for a response; amendment A3): the specification records the response
(`respSrv`); the phases name the voters (with the node), a candidate of the response's term, and take
the server to the recorded one (`hΦ'`). -/
theorem fxPresR_voteRespCand (γ : RaftNames) (id : w64) (ma : Etcdraft.Msg) (E : TraceEv → Prop)
    (Φ Φ' : List w64 → ServerC → List Etcdraft.Msg → Prop)
    (hty : ma.type = .requestVoteResponse) (hd : ma.dest = idAbs id)
    (hrole : ∀ C cs P, Φ C cs P → id ∈ C ∧ ma.term = cs.currentTerm)
    (hΦ' : ∀ C cs P cs' P', Φ C cs P → Φ' C cs' (P ++ P') →
      P' = [] ∧ ∀ a, toC (confAbs C) a = cs → cs' = toC (confAbs C) (respSrv a ma)) :
    ⊢ FxPresR (GF := GF) γ id ma E (fun _ => False) (recvPhantoms ma) Φ Φ' := by
  iunfold FxPresR
  imodintro
  iintro %C %cs %P %e %a %a' %P' %σ %hpre Htbl #Hfx
  obtain ⟨hΦ, -, hcs, hΦ1, -, hsrv, hσa, -, -, -, hm⟩ := hpre
  obtain ⟨hP', hcs'⟩ := hΦ' C cs P _ P' hΦ hΦ1
  subst hP'
  have hcs1 := hcs' a hcs
  have hph : recvPhantoms ma a = [] := recvPhantoms_resp ma a (.inr hty)
  obtain ⟨hC, ht⟩ := hrole C cs P hΦ
  have hT : (σ.s (idAbs id)).currentTerm = cs.currentTerm := by rw [hσa, ← hcs]; rfl
  have hi : idAbs id ∈ σ.server := by rw [hsrv, mem_confAbs]; exact hC
  ihave #H1 := simFx_respCand γ C σ (idAbs id) ma hi hm hd hty (by rw [hT]; exact ht) $$ Hfx
  have hs : ∀ j, toC (withNode σ (idAbs id) (respSrv (σ.s (idAbs id)) ma) (fun b => b.without ma) _root_.id).server
      ((withNode σ (idAbs id) a' (fun b => b.without ma)
        (fun b => ([] ++ recvPhantoms ma a).foldl Etcdraft.Bag.with b)).s j) =
      toC (withNode σ (idAbs id) (respSrv (σ.s (idAbs id)) ma) (fun b => b.without ma) _root_.id).server
        ((withNode σ (idAbs id) (respSrv (σ.s (idAbs id)) ma) (fun b => b.without ma) _root_.id).s j) := by
    intro j
    show toC σ.server (if j = idAbs id then a' else σ.s j) =
      toC σ.server (if j = idAbs id then respSrv (σ.s (idAbs id)) ma else σ.s j)
    split
    · rw [hsrv, hcs1, hσa]
    · rfl
  ihave #H3 := simFx_congr γ C
    (withNode σ (idAbs id) (respSrv (σ.s (idAbs id)) ma) (fun b => b.without ma) _root_.id)
    (withNode σ (idAbs id) a' (fun b => b.without ma) (fun b => ([] ++ recvPhantoms ma a).foldl Etcdraft.Bag.with b))
    rfl rfl (by rw [hph]; rfl) hs $$ H1
  iframe Htbl
  isplitl
  · iexact H3
  · iintro %v %hv
    exact hv.elim

/-- **A vote response's receive line's phase step at a candidate of its term** (amendment A3): from
the pinned idle phase at `s` to the one at raft's state after `recordVote` (whatever `poll` then decides),
the server recorded (`respSrv`, at the pinned server `toC a0`), the list kept (`lineEffect_resp`);
granting or refusing, whether raft has heard from the voter or not. -/
theorem phaseStepR_voteRespCand (id : w64) (c : CfgM) (s : NState) (m : MessageM)
    (ents : List EntryM) (evt : w64) (C0 : List w64) (cs0 : ServerC) (P0 : List Etcdraft.Msg)
    (a0 : Etcdraft.Server) (ha0 : toC (confAbs C0) a0 = cs0)
    (ma : Etcdraft.Msg) (hev : RecvEvTy (absMsg .voteResp m ents) evt) (hto : m.To' = id)
    (hterm : m.Term' = s.term) (hc : s.role = .candidate)
    (hb : (absMsg .voteResp m ents).NumsBelow traceNumBound)
    (hma : TraceSim.msgAbs C0 C0.length (absMsg .voteResp m ents) = some ma) :
    PhaseStepR id c ma (SendEvOf evt id s c (absMsg .voteResp m ents)) (fun _ => False) (recvPhantoms ma)
      (IdlePin s C0 cs0 P0)
      (IdlePin { s with votes := recordVote s.votes m.From' (!m.Reject') } C0 (toC (confAbs C0) (respSrv a0 ma)) P0) := by
  rintro C cs P ⟨rfl, rfl, rfl, hI⟩ ⟨hin, hout, hC⟩ e he
  obtain ⟨a1, ha1, hR0, hs, hP, bt, bc, bl⟩ := hI
  have hpre : s.role ≠ .preCandidate := by rw [hc]; decide
  have hdst : (absMsg .voteResp m ents).dst = id := hto
  have he' : SendEvOf evt (absMsg .voteResp m ents).dst s c (absMsg .voteResp m ents) e := by rw [hdst]; exact he
  obtain ⟨bmt, bk, blt, bi, bmc⟩ := numsBelow_63 hb
  have hnb := recvEvTy_notBoot hev
  refine ⟨he.2.1, sendEvOf_notBoot he hnb.1 hnb.2.1 hnb.2.2.1,
    recvLine_pred C e s c _ evt ma hev he' hout bmt bi blt bk bmc hma, ?_⟩
  intro a ha
  have hR : SimServerR C C.length (toPState s) a := simServerR_toC (ha1.trans ha.symm) hR0
  have hC' : (absMsg .voteResp m ents).dst ∈ C := by rw [hdst]; exact hC
  obtain ⟨-, -, hsrc, -, -, -, hvr⟩ := msgAbs_recvTy hev hma
  have hty : ma.type = .requestVoteResponse := hvr rfl
  have hvg : ma.voteGranted = !m.Reject' := by
    simp [TraceSim.msgAbs, absMsg, absMsgFrom] at hma; subst hma; rfl
  have hpc : (toPState s).role = .candidate := by simp [toPState_role, hc, proleRole]
  have hRr := simServerR_respSrv_cand ma m.From' hR hpc hty hsrc
  rw [hvg] at hRr
  have hps : toPState { s with votes := recordVote s.votes m.From' (!m.Reject') } =
      { toPState s with votes := recordVote (toPState s).votes m.From' (!m.Reject') } := by
    simp [toPState, hpre]
  have htoC : toC (confAbs C) (respSrv a ma) = toC (confAbs C) (respSrv a0 ma) :=
    toC_respSrv _ _ _ ma (ha.trans ha0.symm)
  have hph := recvPhantoms_resp ma a (.inr hty)
  have hrev : (absMsg .voteResp m ents).ty = .appResp ∧ evt = W64 12 ∨
      (absMsg .voteResp m ents).ty = .voteResp ∧ evt = W64 16 ∨
      (absMsg .voteResp m ents).ty = .heartbeatResp ∧ (absMsg .voteResp m ents).reject = false ∧ evt = W64 12 := by
    rcases hev with ⟨h, -⟩ | ⟨h, -, -⟩ | ⟨h, -⟩ | h
    · cases h
    · cases h
    · cases h
    · exact h
  refine ⟨respSrv a ma, [], ⟨rfl, htoC, by rw [List.append_nil],
      ⟨respSrv a ma, by first | exact htoC | rfl, by rw [hps]; exact hRr, by rw [hps]; exact hs,
        by rw [hps]; simpa using hP, bt, bc, by rw [hps]; exact bl⟩⟩,
    fun x hx => by simp at hx, ?_⟩
  rw [← hdst]
  simp only [List.nil_append, hph, List.foldl_nil]
  exact lineEffect_resp C e s c _ evt a ma _ hrev he' hin hout hC' hR hs hpre hterm bt bc bl bi hma

end cand

end EtcdGrove
end Perennial
