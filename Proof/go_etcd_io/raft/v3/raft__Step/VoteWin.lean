/-
Lean-first (no Rocq counterpart). **`Step`'s `MsgVoteResp` arm past a won election** (2026-11-11,
trace-check Q8 stage 1 slice 25b, `notes/decisions.md`, "Q8 stage 1 (slice 25b)"): a traced caller's
family moves raft's ghost state to the won state inside the gates (the registration at the
`BecomeLeader` line, the empty entry's record at its `Replicate` line), and gives it back there
(`CloseMid`'s second case); `Step` then steps the broadcast alone from the won state, with the whole
step's model witness, the mode unchanged. The vote versions of `MsgProp`'s `stepCD_sendApps` (reused:
the broadcast from a leader's state), `stepOut_of_stepCD_prop` and `stepOut_prop_md`.

Proof structure, not specification: only `Proof/raft__Step.lean` imports it.
-/
module

public import Proof.go_etcd_io.raft.v3.raft__Step.MsgProp

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section pure
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

namespace StepProof

/-- A vote response's step keeps the mode (`GMove`: no ghost part moves). -/
theorem stepOut_vote_md {md md' : GMode} {c : CfgM} {id : w64} {m : MessageM} {s s' : NState}
    (hty : m.Type' = MsgVoteResp) (h : md.StepOut c id m s s' md') : md' = md := by
  cases md with
  | static => exact h.1
  | dyn dec c0 h0 g =>
    obtain ⟨g', hmv, rfl, -⟩ := h
    rcases hmv with ⟨h1, -⟩ | rfl | ⟨h1, -⟩ | ⟨h1, -⟩
    · exact absurd (hty.symm.trans h1) (by w32_ne)
    · rfl
    · exact absurd (hty.symm.trans h1) (by w32_ne)
    · exact absurd (hty.symm.trans h1) (by w32_ne)

/-- **A vote response's whole step, the model's witness at the mode unchanged** (`StepCD`, the
dynamic premises at `s`). -/
theorem stepOut_of_stepCD_vote {md : GMode} {c : CfgM} {id : w64} {m : MessageM} {s s' : NState}
    {B : Int} {recv : List Msg} (Hstep : StepCD c id B m s recv s') (hty : m.Type' = MsgVoteResp)
    (Hdyn : ∀ dec c0 h0 g, md = .dyn dec c0 h0 g → g.cfg.cfg = c ∧ DynHyp (effDec dec g.decs) m s s' g) :
    md.StepOut c id m s s' md := by
  cases md with
  | static => exact ⟨rfl, B, recv, Hstep.1⟩
  | dyn dec c0 h0 g =>
    obtain ⟨hc, hd⟩ := Hdyn dec c0 h0 g rfl
    obtain ⟨cidx', Hcm, HR⟩ := Hstep.2 (AdmFold (effDec dec g.decs) c0) (effDec dec g.decs) g hc hd
    have hci : cidx' = g.cidx := by
      rcases Hcm with h | ⟨h, -⟩
      · exact h
      · exact absurd (hty.symm.trans h) (by w32_ne)
    subst hci
    exact ⟨g, .inr (.inl rfl), rfl, B, recv, HR⟩

/-- The dynamic premises of a vote response at a state that is no pre-candidate. -/
theorem gmodePre_vote {md : GMode} {m : MessageM} {ents : List EntryM} {s1 : NState}
    (hty : m.Type' = MsgVoteResp) (hrole : s1.role ≠ .preCandidate) : md.Pre m ents s1 := by
  cases md with
  | static => trivial
  | dyn dec c0 h0 g =>
    exact ⟨fun _ hp => absurd hp hrole,
      fun h => absurd (hty.symm.trans h) (by w32_ne), fun h => absurd (hty.symm.trans h) (by w32_ne)⟩

/-- The won state (the tally recorded, `becomeLeader` run) at a `Progress` map `pvs1`. -/
abbrev wonState (id : w64) (s : NState) (m : MessageM) (pvs1 : GMap w64 Progress) : NState :=
  { becomeLeader id { s with votes := recordVote s.votes m.From' (!m.Reject') } with prvals := pvs1 }

theorem wonState_role (id : w64) (s : NState) (m : MessageM) (pvs1 : GMap w64 Progress) :
    (wonState id s m pvs1).role = .leader := rfl

theorem wonState_gh (id : w64) (s : NState) (m : MessageM) (pvs1 : GMap w64 Progress) :
    (wonState id s m pvs1).gh = s.gh := rfl

theorem wonState_storage (id : w64) (s : NState) (m : MessageM) (pvs1 : GMap w64 Progress) :
    (wonState id s m pvs1).logst.storage = s.logst.storage := rfl

theorem wonState_progress (id : w64) (s : NState) (m : MessageM) (pvs1 : GMap w64 Progress) :
    (wonState id s m pvs1).progress = s.progress := rfl

/-- The won state's log is past `s`'s (the empty entry appended). -/
theorem wonState_logst_ne (id : w64) (s : NState) (m : MessageM) (pvs1 : GMap w64 Progress) :
    (wonState id s m pvs1).logst ≠ s.logst := by
  intro h
  have h1 := congrArg (fun l => l.uents.length) h
  simp [becomeLeader, becomeLeaderLog, becomeLeaderPre, resetTo, resetTo0, sendMsgs, logAppend] at h1

/-- The new messages' numbers from the won state (whose outbox is `s`'s and the
self-acknowledgement). -/
theorem outTrStep_won (id : w64) (s : NState) (m : MessageM) (pvs1 : GMap w64 Progress) (s' : NState)
    (h : OutTrStep s s') : OutTrStep (wonState id s m pvs1) s' := by
  intro htr x hx
  rcases h htr x hx with h1 | h1
  · left
    simp only [becomeLeader, becomeLeaderLog, becomeLeaderPre, resetTo, resetTo0, sendMsgs]
    exact List.mem_append_left _ h1
  · right; exact h1

/-- **The end state of a won election, from `Step`'s end and a close past the won state**: the close's
log the won state's, so the tally was won (not pending, not lost: those keep the log); the broadcast
`ms` judged at `becomeLeader`'s state, at `reset`'s `Match` values. -/
theorem voteWin_end {c : CfgM} {id : w64} {m : MessageM} {ents : List EntryM} {ctx : List w8}
    {s s' : NState} (pvs1 : GMap w64 Progress)
    (hty : m.Type' = MsgVoteResp) (hrole : s.role = .candidate) (hterm : m.Term' = s.term)
    (Hend : StepEnd c id m ents ctx s s') (hlog : (wonState id s m pvs1).logst = s'.logst) :
    ∃ (lost : Bool) (ms : List Msg) (pvs : GMap w64 Progress),
      s' = { voteRespResult id s m.From' m.Reject' true lost ms with prvals := pvs } ∧
      JQuorum c (granted (recordVote s.votes m.From' (!m.Reject'))) ∧
      ReplSends id (becomeLeader id { s with votes := recordVote s.votes m.From' (!m.Reject') }) ms ∧
      prvalsMatch pvs = resetMatched id (logLast s.logst) s.prvals := by
  have hety : StepEndTy m.Type' := by rw [hty]; unfold StepEndTy; simp
  have hns : ¬ StaleMsg s m := fun h => absurd h.2 (by rw [hterm]; omega)
  have hnh : m.Type' ≠ MsgHup := by rw [hty]; w32_ne
  have hnv : m.Type' ≠ MsgVote := by rw [hty]; w32_ne
  have hnbf : ¬ PreBF m s := fun h => absurd h.1 (by rw [hterm]; omega)
  obtain ⟨pvs0, h⟩ := (Hend hety).2.2.2 hns hnh hnv
  rw [show preState s m pvs0 = s by simp [preState, hnbf]] at h
  obtain ⟨scfg, sv, d, c', hf⟩ := h.2.1 (.inl hrole)
  unfold CandidateStepResultC at hf
  obtain ⟨-, hf⟩ := hf
  rw [ite_eq_left hty] at hf
  obtain ⟨-, hf⟩ := hf
  rw [ite_eq_right (by rw [hrole]; decide)] at hf
  obtain ⟨won, lost, ms, pvs, hw, -, -, hs'⟩ := hf
  cases won with
  | true =>
    obtain ⟨hq, hms, hpm⟩ := hw rfl
    exact ⟨lost, ms, pvs, hs', hq, hms, hpm⟩
  | false =>
    exfalso
    apply wonState_logst_ne id s m pvs1
    rw [hlog, hs']
    cases lost <;> simp [voteRespResult, becomeFollower, resetTo, resetTo0]

end StepProof

end pure

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

namespace StepProof

/-- **The broadcast after a won election, alone** (`stepCD_sendApps` from the won state). -/
theorem stepCD_won_sendApps [GoSemanticsFunctions] (c : CfgM) (id : w64) (B : Int) (m : MessageM) (s : NState)
    (pvs1 pvs : GMap w64 Progress) (lost : Bool) (ms : List Msg)
    (Hms : ReplSends id (becomeLeader id { s with votes := recordVote s.votes m.From' (!m.Reject') }) ms)
    (Hpvs : prvalsMatch pvs = prvalsMatch pvs1)
    (Hpc : domSet s.progress ⊆ c.voters ∪ c.learners) :
    StepCD c id B m (wonState id s m pvs1) []
      { voteRespResult id s m.From' m.Reject' true lost ms with prvals := pvs } := by
  have h := stepCD_sendApps c id B m (wonState id s m pvs1) ms pvs rfl
    ((replSends_prvals id _ pvs1 ms).2 Hms) Hpvs Hpc
  have he : ({ sendMsgs (wonState id s m pvs1) ms with prvals := pvs } : NState) =
      { voteRespResult id s m.From' m.Reject' true lost ms with prvals := pvs } := by
    simp [voteRespResult, sendMsgs]
  rw [he] at h
  exact h

/-- **`finish_branch0` from a state past `s`** (`CloseMid`): the ghost state given back at `s1`, the
rest of the step (`s1` to `s'`, receiving nothing) stepped from there, at the mode unchanged; the post's
facts are the whole step's (`s` to `s'`, its model witness `Hout`). -/
theorem finish_branch_mid (γ : RaftNames) (md : GMode) (c : CfgM) (r : Loc) (id : w64)
    (s s1 s' : NState) (m : MessageM) (err : GoInterface) (Gq : NState → IProp GF) (Φ : val → IProp GF)
    (Hdh1 : DynHypFor md m s1 s') (Hwf' : NStateWf s')
    (Hstep1 : StepCD c id (plogLastIndexZ (toPState s1).base (toPState s1).log) m s1 [] s')
    (Hfr : m.Type' ≠ MsgSnap → NetFrame s s') (Htm : m.Type' ≠ MsgSnap → TermStep m s s')
    (Hresp : RespStep m s s') (Hng1 : s'.gh = s1.gh ∧ s'.logst.storage = s1.logst.storage)
    (Hot1 : OutTrStep s1 s')
    (Hmd : ∀ md', md.StepOut c id m s1 s' md' → md' = md) (Hout : md.StepOut c id m s s' md) :
    ⊢ ownRaftGhost γ id (toPState s1) md.isDyn -∗ ghostRest γ md c id s1 -∗
      ownRaftPhysCV c c.voters r id s' -∗
      (⌜err = interface.nil⌝ ∨
        (⌜m.Type' = MsgProp⌝ ∗ globalAddr ErrProposalDropped ↦□ err)) -∗
      Gq s' -∗ stepPost γ md c r id s m Gq Φ -∗
      |={⊤}=> Φ #err := by
  iintro Hghost Hrest Hphys Herr HG HΦ
  unfold stepPost
  icases HΦ with ⟨Hlc, HΦ⟩
  imod ghost_step_md0 γ md c id m s1 s' Hstep1 Hdh1 Hng1 Hot1 $$ Hlc Hghost Hrest
    with ⟨%md', %Hout', Hghost⟩
  obtain rfl := Hmd md' Hout'
  imodintro
  iapply HΦ $$ %err %s' %c %md'
  iframe Hphys Hghost Herr HG
  ipureintro
  exact ⟨Hwf', Hout, fun _ => rfl, Hfr, Htm, Hresp⟩

end StepProof

end ghost

end EtcdGrove
end Perennial
