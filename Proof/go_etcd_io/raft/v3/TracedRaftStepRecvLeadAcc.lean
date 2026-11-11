/-
Lean-first (no Rocq counterpart). **A leader's accepted `MsgAppResp` of its term: the receive line**
(2026-11-11, trace-check Q8 stage 1 slice 27c, `notes/decisions.md`, "Q8 stage 1 (slice 27c)").

The specification's `HandleAppendEntriesResponse` at the leader raises the sender's match index to the
response's (`respSrv`: `max`), as raft's `MaybeUpdate` raises its `Match` (`appRespMatch`), after the
line. So the receive line's phase step leaves the share's server at the leader's idle server of a state
whose `Match` values are `appRespMatch`'s (`AccIdle`, `phaseStepR_leadAcc`; the sender must have a
`Progress`, which `RawNode.Step` checks for every response before `raft.Step`); its facts are the
recorded acknowledgement's (`simFx_respLead`: `ackHists_resp` for the histories, the leader's durable
bound `DurS` for `SpecInv`, `specInv_respLead`).

**Not here** (`notes/decisions.md`, "Q8 stage 1 (slice 27c)"): `maybeCommit`'s `Commit` line and what
follows it, which need raft's ghost state moved past the commit inside `"Hgcommit"` and the close given
back there (a `CloseMid` case for `MsgAppResp`, `Step`'s `MsgAppResp` arm split).
-/
module

public import Proof.go_etcd_io.raft.v3.TracedRaftStepRecvLeadNA

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 TraceSim

section pure
variable [GooseExts]

/-- `prvalsMatch` of a map with one `Progress` replaced. -/
theorem prvalsMatch_insert (pvs : GMap w64 Progress) (i : w64) (p : Progress) :
    prvalsMatch (<[i := p]> pvs) = <[i := p.matched]> (prvalsMatch pvs) := by
  apply GMap.map_eq; intro k
  simp only [prvalsMatch, GMap.fmap_eq, GMap.lookup_fmap]
  by_cases hk : i = k
  · subst hk; rw [GMap.lookup_insert_eq, GMap.lookup_insert_eq]; rfl
  · rw [GMap.lookup_insert_ne _ _ hk, GMap.lookup_insert_ne _ _ hk]; simp [GMap.lookup_fmap]

/-- **`MaybeUpdate`'s `Progress` map** (a witness: the sender's `Match` raised to the index). -/
def arPv (s : NState) (src idx : w64) : GMap w64 Progress :=
  match s.prvals !! src with
  | some p => <[src := { p with matched := if uint.Z p.matched < uint.Z idx then idx else p.matched }]> s.prvals
  | none => s.prvals

theorem prvalsMatch_arPv (s : NState) (src idx : w64) :
    prvalsMatch (arPv s src idx) = appRespMatch s src idx := by
  unfold arPv appRespMatch
  have hl : prvalsMatch s.prvals !! src = Progress.matched <$> (s.prvals !! src) := by
    simp only [prvalsMatch, GMap.fmap_eq, GMap.lookup_fmap]; rfl
  cases h : s.prvals !! src with
  | none => rw [hl, h]; rfl
  | some p => rw [hl, h, prvalsMatch_insert]; rfl

/-- **The leader's idle server after an accepted append response**: its `Match` values
`MaybeUpdate`'s. -/
def AccIdle (C : List w64) (s : NState) (src idx : w64) (cs : ServerC) (P : List Etcdraft.Msg) : Prop :=
  ∃ pvs, prvalsMatch pvs = appRespMatch s src idx ∧ SimIdle C { s with prvals := pvs } cs P

/-- The receive line's result, pinned: the voters, the recorded server and the list named, the
sender a voter. -/
abbrev AccPin (s : NState) (C0 : List w64) (cs1 : ServerC) (P0 : List Etcdraft.Msg) (src idx : w64) :
    List w64 → ServerC → List Etcdraft.Msg → Prop :=
  fun C cs P => C = C0 ∧ cs = cs1 ∧ P = P0 ∧ AccIdle C s src idx cs P ∧ src ∈ C

end pure

section facts
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **The idle relation after the recorded acknowledgement**: the sender's match index raised as raft's
`Match` is (`respSrv_matchIndex` against `appRespMatch`), nothing else read moved. -/
theorem simServerR_respLead (C : List w64) (bl : Nat) (s : NState) (a : Etcdraft.Server) (ma : Etcdraft.Msg)
    (src idx : w64) (pvs : GMap w64 Progress) (hR : SimServerR C bl (toPState s) a) (hl : s.role = .leader)
    (hty : ma.type = .appendEntriesResponse) (hsu : ma.success = true) (hsrc : ma.source = idAbs src)
    (hmi : ma.matchIndex = uint.Z idx) (hdom : ∃ x, prvalsMatch s.prvals !! src = some x)
    (hpvs : prvalsMatch pvs = appRespMatch s src idx) :
    SimServerR C bl (toPState { s with prvals := pvs }) (respSrv a ma) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hR
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := respSrv_fields a ma
  obtain ⟨x, hx⟩ := hdom
  refine ⟨by rw [g3]; exact h1, by rw [g4]; exact h2, ?_, ?_, h5, by rw [g1]; exact h6, by rw [g2]; exact h7,
    by rw [g5]; exact h8, ?_, ?_, ?_⟩
  · unfold respSrv; rw [if_neg (by rw [hty]; decide)]; split <;> exact h3
  · unfold respSrv; rw [if_neg (by rw [hty]; decide)]; split <;> exact h4
  · unfold respSrv; rw [if_neg (by rw [hty]; decide)]; split <;> exact h9
  · intro hc; simp [toPState, hl, proleRole] at hc
  · intro _ j hj
    have hlx : (toPState { s with prvals := pvs }).matched = appRespMatch s src idx := by
      simp only [toPState, hl, ↓reduceIte]; exact hpvs
    rw [hlx, respSrv_matchIndex a ma hty, appRespMatch_of_some s src idx x hx]
    have hold := h11 (by simp [toPState, hl, proleRole]) j hj
    have hm0 : (toPState s).matched = prvalsMatch s.prvals := by simp only [toPState, hl, ↓reduceIte]
    rw [hm0] at hold
    by_cases hjs : j = src
    · subst hjs
      rw [if_pos ⟨hsu, hsrc.symm⟩, GMap.lookup_insert_eq, hold, hx, hmi]
      simp only [Option.getD_some]
      split
      · rename_i hlt; rw [Int.max_eq_right (by omega)]
      · rename_i hlt; rw [Int.max_eq_left (by omega)]
    · have hne : idAbs j ≠ ma.source := by rw [hsrc]; exact fun h => hjs (idAbs_inj h)
      rw [if_neg (fun h => hne h.2), GMap.lookup_insert_ne _ _ (Ne.symm hjs), hold]

/-- **`SpecInv` after a leader records an append response of its term** (the leader's durable bound
`DurS`: a successful response of its term addressed to it is within its durable log). -/
theorem specInv_respLead (σ : Etcdraft.State) (i : Etcdraft.ID) (ma : Etcdraft.Msg)
    (h : TraceSpecInv.SpecInv σ) (hi : i ∈ σ.server) (hty : ma.type = .appendEntriesResponse)
    (hm : ma ∈ σ.messages.domain) (hd : ma.dest = i) (ht : ma.term = (σ.s i).currentTerm) :
    TraceSpecInv.SpecInv (withNode σ i (respSrv (σ.s i) ma) (fun b => b.without ma) _root_.id) := by
  have hd' := TraceSpecInv.specInv_discard ma h
  have hs : ∀ j, (withNode σ i (respSrv (σ.s i) ma) (fun b => b.without ma) _root_.id).s j =
      if j = i then respSrv (σ.s i) ma else (σ.discard ma).s j := fun _ => rfl
  have hv : ma.type ≠ .requestVoteResponse := by rw [hty]; decide
  refine TraceSpecInv.specInv_congr_m hd' rfl rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    (try (intro j; rw [hs]; split <;> (try subst_vars) <;> simp only [respSrv, hv, ↓reduceIte] <;>
      (try split) <;> rfl))
  intro j hj hlead k hk
  rw [hs]
  split
  · rename_i hji; subst hji
    have hold := (hd'.2.1 j hj hlead).2.2.1 k hk
    have hD := h.2.1 j hj hlead
    rw [respSrv_matchIndex _ _ hty]
    split
    · rename_i hc
      refine Int.max_le.2 ⟨hold, ?_⟩
      exact hD.2.2.2.2.2.1 ma hm hd hty ht hc.1
    · exact hold
  · exact (hd'.2.1 j hj hlead).2.2.1 k hk


/-- **The facts after a leader records an append response of its term** (`simFx_resp` at a leader):
the servers' facts, logs, commit indices and terms unchanged; the acknowledgement histories by
`ackHists_resp` (the raised match index's history is the response's); `SpecInv` by
`specInv_respLead`. -/
theorem simFx_respLead (γ : RaftNames) (C : List w64) (σ : Etcdraft.State) (i : Etcdraft.ID) (ma : Etcdraft.Msg)
    (hi : i ∈ σ.server) (hty : ma.type = .appendEntriesResponse) (hm : ma ∈ σ.messages.domain)
    (hd : ma.dest = i) (ht : ma.term = (σ.s i).currentTerm) :
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
  · iunfold QuorumLogF at Hq
    icases Hq with ⟨#Hk, #Ha⟩
    iunfold QuorumLogF
    isplitl
    · iapply quorumKept_mono γ C σ (withNode σ i (respSrv (σ.s i) ma) (fun b => b.without ma) _root_.id) rfl
        (fun j hj => ⟨j, hj, by unfold committedL; rw [(hF j).1, (hF j).2.1]; exact List.prefix_refl _⟩)
        (fun _ _ h => keptFrom_congr (σ := σ)
          (σ' := withNode σ i (respSrv (σ.s i) ma) (fun b => b.without ma) _root_.id) rfl
          (fun k => (hF k).1) (fun k => by rw [(hF k).2.2.1]; exact Int.le_refl _) h)
        $$ Hk
    · iapply ackHists_resp γ C σ i ma hm hd hty ht $$ Ha
  ipureintro
  refine ⟨specInv_respLead σ i ma hsi hi hty hm hd ht,
    msgsUniq_mono hsub hu, msgsShape_resp σ i ma hm hsh, ?_⟩
  intro m hm hty' j hj hlj htj hs k e he
  rw [(hF j).1]
  rw [(hF j).2.2.2.1] at hlj; rw [(hF j).2.2.1] at htj
  exact has m (hsub m hm) hty' j hj hlj htj hs k e he

/-- **The facts of an accepted append response's receive line at a leader** (`FxPresR` at
`recvPhantoms m`, none for a response): the recorded acknowledgement's (`simFx_respLead`); the phases
take the server to the recorded one and keep the list (`hΦ'`). -/
theorem fxPresR_leadAcc (γ : RaftNames) (id : w64) (ma : Etcdraft.Msg) (E : TraceEv → Prop)
    (Φ Φ' : List w64 → ServerC → List Etcdraft.Msg → Prop)
    (hty : ma.type = .appendEntriesResponse) (hdst : ma.dest = idAbs id)
    (hlead : ∀ C cs P, Φ C cs P → id ∈ C ∧ ma.term = cs.currentTerm)
    (hΦ' : ∀ C cs P cs' P', Φ C cs P → Φ' C cs' (P ++ P') →
      P' = [] ∧ ∀ a, toC (confAbs C) a = cs → cs' = toC (confAbs C) (respSrv a ma)) :
    ⊢ FxPresR (GF := GF) γ id ma E (fun _ => False) (recvPhantoms ma) Φ Φ' := by
  iunfold FxPresR
  imodintro
  iintro %C %cs %P %e %a %a' %P' %σ %hpre Htbl #Hfx
  obtain ⟨hΦ, -, hcs, hΦ1, -, hsrv, hσa, -, -, -, hmem⟩ := hpre
  obtain ⟨hP', hcs'⟩ := hΦ' C cs P _ P' hΦ hΦ1
  subst hP'
  have hcs1 := hcs' a hcs
  have hph : recvPhantoms ma a = [] := recvPhantoms_resp ma a (.inl hty)
  obtain ⟨hidC, hterm⟩ := hlead C cs P hΦ
  have hi : idAbs id ∈ σ.server := by rw [hsrv]; exact (mem_confAbs C id).2 hidC
  have ht : ma.term = (σ.s (idAbs id)).currentTerm := by
    rw [hterm, hσa, ← hcs]; rfl
  ihave #H1 := simFx_respLead γ C σ (idAbs id) ma hi hty hmem hdst ht $$ Hfx
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

end facts

section steps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **A leader's accepted append response of its term: the receive line's phase step**, from the
pinned idle phase to the recorded server (`respSrv` at the pinned server), idle-related to a state with
`MaybeUpdate`'s `Match` values (`simServerR_respLead`), the list kept, the sender a voter (the receive
law's premise); the sender has a `Progress` (`hdom`). -/
theorem phaseStepR_leadAcc (id : w64) (c : CfgM) (s : NState) (m : MessageM) (ents : List EntryM) (evt : w64)
    (C0 : List w64) (cs0 : ServerC) (P0 : List Etcdraft.Msg) (a0 : Etcdraft.Server) (ha0 : toC (confAbs C0) a0 = cs0)
    (ma : Etcdraft.Msg) (hev : RecvEvTy (absMsg .appResp m ents) evt) (hto : m.To' = id)
    (hrej : m.Reject' = false) (hterm : m.Term' = s.term) (hlead : s.role = .leader)
    (hdom : ∃ x, prvalsMatch s.prvals !! m.From' = some x)
    (hb : (absMsg .appResp m ents).NumsBelow traceNumBound)
    (hma : TraceSim.msgAbs C0 C0.length (absMsg .appResp m ents) = some ma) :
    PhaseStepR id c ma (SendEvOf evt id s c (absMsg .appResp m ents)) (fun _ => False) (recvPhantoms ma)
      (IdlePin s C0 cs0 P0) (AccPin s C0 (toC (confAbs C0) (respSrv a0 ma)) P0 m.From' m.Index') := by
  rintro C cs P ⟨rfl, rfl, rfl, hI⟩ ⟨hin, hout, hC, hsrcC, -⟩ e he
  have hI' := hI
  obtain ⟨a1, ha1, hR0, hs, hP, bt, bc, bl⟩ := hI'
  have hpre : s.role ≠ .preCandidate := by rw [hlead]; decide
  have hdst : (absMsg .appResp m ents).dst = id := hto
  have he' : SendEvOf evt (absMsg .appResp m ents).dst s c (absMsg .appResp m ents) e := by rw [hdst]; exact he
  obtain ⟨bmt, bk, blt, bi, bmc⟩ := numsBelow_63 hb
  have hnb := recvEvTy_notBoot hev
  refine ⟨he.2.1, sendEvOf_notBoot he hnb.1 hnb.2.1 hnb.2.2.1,
    recvLine_pred C e s c _ evt ma hev he' hout bmt bi blt bk bmc hma, ?_⟩
  intro a ha
  have hR : SimServerR C C.length (toPState s) a := simServerR_toC (ha1.trans ha.symm) hR0
  have hC' : (absMsg .appResp m ents).dst ∈ C := by rw [hdst]; exact hC
  have hfa : ma.type = .appendEntriesResponse ∧ ma.success = true ∧ ma.source = idAbs m.From' ∧
      ma.matchIndex = uint.Z m.Index' := by
    simp only [TraceSim.msgAbs, absMsg, absMsgFrom] at hma
    injection hma with hma
    rw [← hma]
    simp [hrej]
  obtain ⟨hmty, hsu, hms, hmi⟩ := hfa
  have hfrom : m.From' ∈ C := by
    rw [hms] at hsrcC
    exact (mem_confAbs C _).1 hsrcC
  have hph := recvPhantoms_resp ma a (.inl hmty)
  have hrev : (absMsg .appResp m ents).ty = .appResp ∧ evt = W64 12 ∨
      (absMsg .appResp m ents).ty = .voteResp ∧ evt = W64 16 ∨
      (absMsg .appResp m ents).ty = .heartbeatResp ∧ (absMsg .appResp m ents).reject = false ∧ evt = W64 12 := by
    rcases hev with ⟨h, -⟩ | ⟨h, -, -⟩ | ⟨h, -⟩ | h
    · cases h
    · cases h
    · cases h
    · exact h
  have hR' := simServerR_respLead C C.length s a ma m.From' m.Index' (arPv s m.From' m.Index') hR hlead hmty hsu hms
    hmi hdom (prvalsMatch_arPv s m.From' m.Index')
  refine ⟨respSrv a ma, [], ⟨rfl, toC_respSrv _ _ _ ma (ha.trans ha0.symm) |>.symm ▸ rfl, by rw [List.append_nil],
    ⟨arPv s m.From' m.Index', prvalsMatch_arPv s m.From' m.Index',
      ⟨respSrv a ma, rfl, hR', hs, by rw [List.append_nil]; exact hP, bt, bc, bl⟩⟩, hfrom⟩,
    fun x hx => by simp at hx, ?_⟩
  rw [← hdst]
  simp only [List.nil_append, hph, List.foldl_nil]
  exact lineEffect_resp C e s c _ evt a ma _ hrev he' hin hout hC' hR hs hpre hterm bt bc bl bi hma

end steps

end EtcdGrove
end Perennial
