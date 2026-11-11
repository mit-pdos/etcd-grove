/-
Lean-first (no Rocq counterpart). **A traced family's ghost step through a candidate's won election**
(2026-11-11, trace-check Q8 stage 1 slice 25b, `notes/decisions.md`, "Q8 stage 1 (slice 25b)";
`ghost_stepWin`, slice 24b's item 3): raft's ghost state, which `Step` hands the family at the receive
line (`ghostIn`), is moved by the family to the won state in the win's three phases
(`Protocol/Refinement.lean`): the vote's record and the registration at the `BecomeLeader` gate
(`ghost_stepWin_reg`: before the line, whose facts read the new leader's `isLeader` and its campaign
log), the term log inside that line's `FxPresU` (the registration's wand), and the empty entry's record
at its `Replicate` gate with the receipt `Step` lends it (`StepG.Tw`, `ghost_stepWin_entry`); the family
gives the ghost state back at the won state (`CloseMid`'s second case, `ghost_stepWin_close`), from
which `Step` steps the broadcast (`raft__Step/VoteWin.lean`).
-/
module

public import Proof.go_etcd_io.raft.v3.TracedStepGates
public import Proof.go_etcd_io.raft.v3.Protocol.RefinementDyn
public import Proof.go_etcd_io.raft.v3.StepLemmasC

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section pure
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

/-- The tally's state (the vote recorded). -/
abbrev votedState (s : NState) (m : MessageM) : NState :=
  { s with votes := recordVote s.votes m.From' (!m.Reject') }

/-- The won state (the tally recorded, `becomeLeader` run), at a `Progress` map `pvs`. -/
abbrev wonStateW (id : w64) (s : NState) (m : MessageM) (pvs : GMap w64 Progress) : NState :=
  { becomeLeader id (votedState s m) with prvals := pvs }

theorem toPState_votedState (s : NState) (m : MessageM) (hr : s.role ≠ .preCandidate) :
    toPState (votedState s m) =
      { toPState s with votes := recordVote (toPState s).votes m.From' (!m.Reject') } := by
  rw [toPState_votes _ _ hr, toPState_votes_nonpre _ hr]

/-- A won election's result with no broadcast is the won state. -/
theorem voteRespResult_won_nil (id : w64) (s : NState) (m : MessageM) (pvs : GMap w64 Progress) :
    ({ voteRespResult id s m.From' m.Reject' true false [] with prvals := pvs } : NState) =
      wonStateW id s m pvs := by
  simp [voteRespResult, sendMsgs]

/-- **A won election, the vote's record and the win, up to the broadcast** (`StepC.recordVote` then
`StepC.win` with no message; `StepR` likewise), at the bound of the empty entry's index. -/
theorem stepCD_wonW (c : CfgM) (id : w64) (s : NState) (m : MessageM) (ents : List EntryM)
    (pvs : GMap w64 Progress)
    (Hto : m.To' = id) (Hteq : m.Term' = s.term) (Hrole : s.role = .candidate)
    (Hid : id ∈ domSet s.prvals)
    (Hq : JQuorum c (granted (recordVote s.votes m.From' (!m.Reject'))))
    (Hmt : prvalsMatch pvs = resetMatched id (logLast s.logst) s.prvals) :
    StepCD c id (plogLastIndexZ (toPState s).base (toPState s).log + 1) m s [absMsg .voteResp m ents]
      (wonStateW id s m pvs) := by
  rw [← voteRespResult_won_nil]
  have Hnp : s.role ≠ .preCandidate := by rw [Hrole]; decide
  have Hvotes : (toPState s).votes = s.votes := toPState_votes_nonpre _ Hnp
  have Hpr : (toPState s).role = .candidate := by rw [toPState_role, Hrole]; rfl
  rw [← Hvotes] at Hq
  have Hmt' : LeaderMatchOk id { toPState s with
      votes := recordVote (toPState s).votes m.From' (!m.Reject') } (prvalsMatch pvs) := by
    rw [Hmt]
    exact resetMatched_leader_ok id s Hid _ rfl rfl
  refine ⟨?_, fun Adm dec g hc hd => ⟨g.cidx, .inl rfl, ?_⟩⟩
  · rw [toPState_voteRespResult _ _ _ _ _ _ _ _ Hrole]
    unfold pvoteRespResult
    simp only [↓reduceIte]
    exact stepC_record_then_win c id (toPState s) (absMsg .voteResp m ents)
      (prvalsMatch pvs) [] rfl Hto Hteq Hpr Hmt' (by simp) Hq (Int.le_refl _) (by simp)
  · change StepR Adm dec id _ (rOf s g) ([absMsg .voteResp m ents] ++ [])
      (rOf { voteRespResult id s m.From' m.Reject' true false [] with prvals := pvs } g)
    have Hr : rOf { voteRespResult id s m.From' m.Reject' true false [] with prvals := pvs } g =
        { rOf s g with
          p := toPState { voteRespResult id s m.From' m.Reject' true false [] with prvals := pvs },
          pci := plastIndex (toPState s) } := by
      unfold rOf pciR
      simp [voteRespResult, becomeLeader, becomeLeaderLog, becomeLeaderPre, sendMsgs,
        resetTo, resetTo0, plastIndex_toPState]
    rw [Hr, toPState_voteRespResult _ _ _ _ _ _ _ _ Hrole]
    unfold pvoteRespResult
    simp only [↓reduceIte]
    have Hrc : (rOf s g).cfg.cfg = c := hc
    refine .trans _ _ _ _ _ (StepR.recordVote (absMsg .voteResp m ents) (rOf s g) rfl Hto
      Hteq Hpr) ?_
    exact StepR.win _ (prvalsMatch pvs) [] Hpr (by rw [Hrc]; exact Hq) (Int.le_refl _) Hmt'
      (by simp) (by simp)

/-- The won state's new message (the self-acknowledgement) is all its outbox adds. -/
theorem outTr_wonW (γ : RaftNames) (id : w64) (s : NState) (m : MessageM) (pvs : GMap w64 Progress)
    (H : NsLink γ s) (hsa : MsgTrOk γ (selfAck id (becomeLeaderLog id (votedState s m)))) :
    NsLink γ (wonStateW id s m pvs) := by
  refine ⟨H.1, H.2.1, fun x hx => ?_⟩
  simp only [becomeLeader, becomeLeaderLog, becomeLeaderPre, resetTo, resetTo0, sendMsgs,
    List.mem_append, List.mem_singleton] at hx
  rcases hx with hx | rfl
  · exact H.2.2 x hx
  · exact hsa

end pure

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- A fupd at the mask with the commit invariant's registry half closed, at `⊤`. -/
theorem fupd_top_of_reg (γ : RaftNames) (P : IProp GF) :
    iprop(|={⊤ \ ↑(raftRegN γ)}=> P) ⊢ iprop(|={⊤}=> P) :=
  fupd_mask_mono CoPset.subseteq_top

/-- **The ghost state's environment at the tally** (`dynEnv`, which the registration reads): statically
the configuration's; dynamically from the invariant at the tally's state (`RInv` after
`StepR.recordVote`, `ownRaftGhostR_env`). -/
theorem ghostRest_dynEnv_vote (γ : RaftNames) (md : GMode) (c : CfgM) (id : w64) (s : NState)
    (m : MessageM) (ents : List EntryM) (Hto : m.To' = id) (Hteq : m.Term' = s.term)
    (Hrole : s.role = .candidate) :
    ghostRest (GF := GF) γ md c id s ⊢
      dynEnv γ id c (toPState (votedState s m)) ∗ ghostRest γ md c id s := by
  have Hnp : s.role ≠ .preCandidate := by rw [Hrole]; decide
  have Hpr : (toPState s).role = .candidate := by rw [toPState_role, Hrole]; rfl
  cases md with
  | static =>
    unfold ghostRest
    simp only [ghostRestM]
    iintro ⟨%Hnl, %HC, #Hcl, #Hw, #Hx⟩
    isplitr
    · iapply dynEnv_static γ id c _ HC.1
    iframe Hcl Hw Hx
    ipureintro; exact ⟨Hnl, HC⟩
  | dyn dec c0 h0 g =>
    unfold ghostRest
    simp only [ghostRestM]
    iintro ⟨%Hnl, ⟨%Hd, #HM, #Hfr⟩, #Hcl, #Hw, #Hx⟩
    obtain ⟨HD, hc, HI⟩ := Hd
    have HR : StepR (AdmFold (effDec dec g.decs) c0) (effDec dec g.decs) id
        0 (rOf s g) [absMsg .voteResp m ents]
        { rOf s g with p := toPState (votedState s m) } := by
      rw [toPState_votedState s m Hnp]
      exact StepR.recordVote (absMsg .voteResp m ents) (rOf s g) rfl Hto Hteq Hpr
    have HI' := RInv_stepR (fun _ _ h => h) HR (by omega)
      (fun _ x hx hty => by
        simp only [List.mem_singleton] at hx; subst hx
        simp [absMsg, absMsgFrom, Msg.mkV] at hty) HI
    isplitr
    · have Henv0 := ownRaftGhostR_env (GF := GF) γ dec g.decs c0 h0 HD id
        { rOf s g with p := toPState (votedState s m) } HI'
      rw [show ({ rOf s g with p := toPState (votedState s m) } : RState).fp = g.fp from rfl,
        show ({ rOf s g with p := toPState (votedState s m) } : RState).cfg.cfg = c from hc,
        show ({ rOf s g with p := toPState (votedState s m) } : RState).p = toPState (votedState s m)
          from rfl] at Henv0
      ihave H := Henv0 $$ HM Hfr
      iexact H
    iframe Hcl Hw Hx HM Hfr
    ipureintro; exact ⟨Hnl, HD, hc, HI⟩

/-- **The won election's ghost state, pending its last phase** (what the registration leaves the
family): the win's last phase (`winPend`) at the tally's state, and the rest of the mode's ghost state
at `s`. -/
def winGhost (γ : RaftNames) (md : GMode) (c : CfgM) (id : w64) (s : NState) (m : MessageM) : IProp GF :=
  iprop(winPend γ id (toPState (votedState s m)) md.isDyn ∗ ghostRest γ md c id s)

/-- **The win's first phase, a family's** (at the `BecomeLeader` gate, before the line): the vote's
record (`ownRaftGhost_step_recordVote`, the response's `isMessage`) and the registration
(`ownRaftGhost_step_win_reg`, at `⊤`); the term map's authority lent out, its return giving the new
term's full log and the pending ghost state (`winGhost`). -/
theorem ghost_stepWin_reg (γ : RaftNames) (md : GMode) (c : CfgM) (id : w64) (s : NState)
    (m : MessageM) (ents : List EntryM) (Hto : m.To' = id) (Hteq : m.Term' = s.term)
    (Hrole : s.role = .candidate)
    (Hq : JQuorum c (granted (recordVote s.votes m.From' (!m.Reject')))) :
    ⊢ isMessage (GF := GF) γ (absMsg .voteResp m ents) -∗ ownStepGhost γ md c id s ={⊤}=∗
      isLeader γ id s.term ∗
      ∃ fp : List EntryM, ⌜FullOk (toPState s).base fp⌝ ∗ isCamp γ id s.term (fp ++ (toPState s).log) ∗
        logRecs γ base0 (fp ++ (toPState s).log) ∗
        ∃ (γm : GName) (terms : GMap w64 TermRec),
          ⌜γ.reTerms !! id = some γm ∧ terms !! s.term = none⌝ ∗ ghostMapAuth γm 1 terms ∗
          (ghostMapAuth γm 1 terms ==∗ leadFull γ s.term (fp ++ (toPState s).log) ∗
            winGhost γ md c id s m) := by
  have Hnp : s.role ≠ .preCandidate := by rw [Hrole]; decide
  have Hpr : (toPState s).role = .candidate := by rw [toPState_role, Hrole]; rfl
  have Hvs := toPState_votedState s m Hnp
  have Hq' : JQuorum c (granted (toPState (votedState s m)).votes) := by
    have hv := toPState_votes_nonpre s Hnp
    rw [Hvs]; simp only [hv]; exact Hq
  have Hr' : (toPState (votedState s m)).role = .candidate := by rw [Hvs]; exact Hpr
  iintro #Hm Hgs
  iunfold ownStepGhost at Hgs
  icases Hgs with ⟨Hg, Hrest⟩
  icases ghostRest_dynEnv_vote γ md c id s m ents Hto Hteq Hrole $$ Hrest with ⟨#Henv, Hrest⟩
  imod rdCred_zero (GF := GF) γ with Hz
  ihave Hg := ownRaftGhost_step_recordVote γ id (absMsg .voteResp m ents) (toPState s) rfl Hto Hteq Hpr
    $$ [] [Hz] Hg
  · iapply (BigSepL.bigSepL_singleton (Φ := fun _ x => isMessage (GF := GF) γ x)).2
    iexact Hm
  · rw [show rdCount ([absMsg MsgType.voteResp m ents] : List Msg) = 0 by rfl]; iexact Hz
  ihave Hg := fupd_top_of_reg γ _ $$ Hg
  imod Hg with Hg
  have Hvs' : toPState (votedState s m) =
      { toPState s with votes := recordVote (toPState s).votes (absMsg .voteResp m ents).src (!((absMsg .voteResp m ents).reject)) } := by
    rw [Hvs]; rfl
  ihave Hg : ownRaftGhost γ id (toPState (votedState s m)) md.isDyn $$ [Hg]
  · rw [Hvs']; iexact Hg
  have Hreg0 := ownRaftGhost_step_win_reg (GF := GF) (md := md.isDyn) γ c id (toPState (votedState s m)) Hr' Hq'
  rw [show (toPState (votedState s m)).term = s.term from rfl,
    show (toPState (votedState s m)).base = (toPState s).base from rfl,
    show (toPState (votedState s m)).log = (toPState s).log from rfl] at Hreg0
  ihave Hreg := Hreg0 $$ Henv Hg
  ihave Hreg := fupd_top_of_reg γ _ $$ Hreg
  imod Hreg with ⟨#Hl, %fp, %Hfp, #Hc, #Hrec, %γm, %terms, %Hfree, Ha, Hw⟩
  imodintro
  iframe Hl
  iexists fp
  iframe Hc Hrec
  isplitr
  · ipureintro; exact Hfp
  iexists γm, terms
  iframe Ha
  isplitr
  · ipureintro; exact Hfree
  iintro Ha
  imod Hw $$ Ha with ⟨#Hf, Hp⟩
  imodintro
  iframe Hf
  iunfold winGhost
  iframe Hp Hrest

/-- **The win's last phase, a family's** (at the empty entry's `Replicate` gate, with the receipt `Step`
lends it, `winLend`): the pending ghost state to raft's ghost state at the won state, at `reset`'s
`Match` values and no broadcast, and the rest of the mode's ghost state to it given the whole step
(`stepCD_wonW`) and the self-acknowledgement's numbers; at the mode unchanged (a win moves no ghost part). -/
theorem ghost_stepWin_entry (γ : RaftNames) (md : GMode) (c : CfgM) (id : w64) (s : NState)
    (m : MessageM) (ents : List EntryM) (pvs : GMap w64 Progress) (Hty : m.Type' = MsgVoteResp)
    (Hto : m.To' = id) (Hteq : m.Term' = s.term) (Hrole : s.role = .candidate)
    (Hid : id ∈ domSet s.prvals)
    (Hq : JQuorum c (granted (recordVote s.votes m.From' (!m.Reject'))))
    (Hmt : prvalsMatch pvs = resetMatched id (logLast s.logst) s.prvals)
    (Hnw : plogLastIndexZ (toPState s).base (toPState s).log + 1 < 2 ^ 64)
    (hsa : MsgTrOk γ (selfAck id (becomeLeaderLog id (votedState s m)))) :
    ⊢ isMessage (GF := GF) γ (absMsg .voteResp m ents) -∗
      ⧖ ((plogLastIndexZ (toPState s).base (toPState s).log).toNat - γ.reBoot.length + 1) -∗
      winGhost γ md c id s m ==∗ ownStepGhost γ md c id (wonStateW id s m pvs) := by
  have Hnp : s.role ≠ .preCandidate := by rw [Hrole]; decide
  have Hvs := toPState_votedState s m Hnp
  have Hstep := stepCD_wonW c id s m ents pvs Hto Hteq Hrole Hid Hq Hmt
  iintro #Hm #Hrc Hw
  iunfold winGhost at Hw
  icases Hw with ⟨Hp, Hrest⟩
  -- the ghost state at the won state (`toPState_becomeLeader`)
  have Hps : toPState (wonStateW id s m pvs) =
      psendMsgs (pwinState id (toPState (votedState s m)) (prvalsMatch pvs))
        ([pselfAck id (pwinState id (toPState (votedState s m)) (prvalsMatch pvs))] ++ []) := by
    rw [toPState_becomeLeader]; simp
  have HLv : plogLastIndexZ (toPState (votedState s m)).base (toPState (votedState s m)).log =
      plogLastIndexZ (toPState s).base (toPState s).log := by rw [Hvs]
  imod ownRaftGhost_step_win_entry γ id (toPState (votedState s m)) (prvalsMatch pvs) []
      ((plogLastIndexZ (toPState s).base (toPState s).log).toNat - γ.reBoot.length + 1)
      (by rw [HLv]; exact Hnw)
      (by rw [Hmt]; exact resetMatched_leader_ok id (votedState s m) Hid _ rfl rfl)
      (by simp) (by simp) (by simp)
      (by rw [HLv]; have := plogLastIndexZ_nonneg (toPState s).base (toPState s).log; omega)
    $$ Hrc Hp with Hg
  rw [← Hps]
  iunfold ownStepGhost
  iframe Hg
  -- the rest of the mode's ghost state, by the whole step
  iunfold ghostRest at Hrest
  icases Hrest with ⟨%Hnl, Hrm, #Hcl, #Hlw, #Hx⟩
  ihave #Hrecv : ([∗list] x ∈ [absMsg .voteResp m ents], isMessage (GF := GF) γ x) $$ []
  · iapply (BigSepL.bigSepL_singleton (Φ := fun _ x => isMessage (GF := GF) γ x)).2
    iexact Hm
  ihave #Hlw' := leadW_stepC γ c id _ (toPState s) _ (toPState (wonStateW id s m pvs)) Hstep.1
    $$ Hrecv Hlw
  imodintro
  iunfold ghostRest
  isplitr
  · ipureintro; exact outTr_wonW γ id s m pvs Hnl hsa
  rw [show certLink (GF := GF) γ (wonStateW id s m pvs).gh.sn = certLink γ s.gh.sn from rfl,
    show xfW (GF := GF) γ (wonStateW id s m pvs) = xfW γ s from rfl]
  isplitr [Hcl Hlw' Hx]
  rotate_left
  · isplitr
    · iexact Hcl
    isplitr
    · iexact Hlw'
    iexact Hx
  cases md with
  | static =>
    simp only [ghostRestM]
    iexact Hrm
  | dyn dec c0 h0 g =>
    simp only [ghostRestM]
    icases Hrm with ⟨%Hd, #HM, #Hfr⟩
    obtain ⟨HD, hc, HI⟩ := Hd
    have Hdh : DynHyp (effDec dec g.decs) m s (wonStateW id s m pvs) g :=
      ⟨by rw [Hty]; simp only [MsgVoteResp, MsgSnap]; exact of_decide_eq_true rfl, fun hp => absurd hp Hnp, HI.full,
        fun h => absurd (Hty.symm.trans h) (by simp only [MsgVoteResp, MsgStorageApplyResp]; exact of_decide_eq_true rfl),
        fun h => absurd (Hty.symm.trans h) (by simp only [MsgVoteResp, MsgProp]; exact of_decide_eq_true rfl)⟩
    obtain ⟨cidx', Hcm, HR⟩ := Hstep.2 (AdmFold (effDec dec g.decs) c0) (effDec dec g.decs) g hc Hdh
    have hci : cidx' = g.cidx := Hcm.elim (fun h => h) (fun h => absurd (Hty.symm.trans h.1)
      (by simp only [MsgVoteResp, MsgStorageApplyResp]; exact of_decide_eq_true rfl))
    subst hci
    have HI' := RInv_stepR (fun _ _ h => h) HR Hnw
      (fun _ x hx hty => by
        simp only [List.mem_singleton] at hx; subst hx
        simp [absMsg, absMsgFrom, Msg.mkV] at hty) HI
    iframe HM Hfr
    ipureintro; exact ⟨HD, hc, HI'⟩
