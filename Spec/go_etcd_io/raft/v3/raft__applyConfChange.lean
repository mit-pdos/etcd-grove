/-
`raft.applyConfChange` (raft.go), Lean-first (2026-10-13, reconfiguration stage D): for a
change that leaves the configuration unchanged; since stage A2 (2026-10-13) for any change.
-/
module

public import Proof.go_etcd_io.raft.v3.InvApplyConf
public import Proof.go_etcd_io.raft.v3.InvApplyConfC
public import Spec.go_etcd_io.raft.v3.raft__switchToConfig

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section pure
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

/-- What `applyConfChange` did to the node: installed new `Progress` objects (`prs`, records
`pvs`, each `Match` the old one or `0` at a leader), then `switchToConfig`'s rest
(`SwitchOk`). -/
def ApplyCCOk (cfg : GSet w64) (id : w64) (s s' : NState) : Prop :=
  ∃ (prs : GMap w64 Loc) (pvs : GMap w64 Progress),
    (s.role = .leader → MatchKept s.prvals pvs) ∧
    SwitchOk cfg id { s with progress := prs, prvals := pvs, isLearner := learnerOf cfg prs id } s'

/-- The protocol reading of `ApplyCCOk`: one `Step` that receives nothing (at a leader
`Step.reMatch`, then `Step.commit` if `maybeCommit` moved the commit index, then
`Step.sendApps`; at a non-leader `Step.refl`), and what is kept of the physical state: the
role, `r.step`, `r.tick`, the term, pre-vote, the ghost bounds, the log but for a raised
commit index. -/
theorem applyCCOk_step (cfg : GSet w64) (id : w64) (s s' : NState) (H : ApplyCCOk cfg id s s') :
    Step cfg id (toPState s) [] (toPState s') ∧
    s'.role = s.role ∧ s'.stepfn = s.stepfn ∧ s'.ticking = s.ticking ∧ s'.term = s.term ∧
    s'.prevote = s.prevote ∧ s'.gh = s.gh ∧
    s'.logst = { s.logst with committed := s'.logst.committed } ∧
    uint.Z s.logst.committed ≤ uint.Z s'.logst.committed := by
  obtain ⟨prs, pvs, Hmk, Hsw⟩ := H
  unfold SwitchOk at Hsw
  by_cases Hl : s.role = .leader
  · rw [if_pos (show ({ s with progress := prs, prvals := pvs, isLearner := learnerOf cfg prs id } : NState).role = .leader from Hl)]
      at Hsw
    obtain ⟨c, ms, pvs2, lt', Hc, Hms, Hmm, rfl⟩ := Hsw
    have Hpl : (toPState s).role = .leader := by simp [toPState, Hl, proleRole]
    -- the new `Progress` values
    have H1 : Step cfg id (toPState s) []
        (toPState { s with progress := prs, prvals := pvs, isLearner := learnerOf cfg prs id }) := by
      have e : toPState { s with progress := prs, prvals := pvs, isLearner := learnerOf cfg prs id } =
          { toPState s with matched := prvalsMatch pvs } := by simp [toPState, Hl]
      rw [e]
      refine .reMatch _ _ Hpl (fun v i hv => ?_)
      simp only [prvalsMatch, GMap.lookup_fmap'] at hv
      cases hp : pvs !! v with
      | none => rw [hp] at hv; cases hv
      | some p' =>
        rw [hp] at hv
        simp only [Option.map_some, Option.some.injEq] at hv
        subst hv
        rcases Hmk Hl v p' hp with h0 | ⟨p, hp0, hm⟩
        · exact .inl h0
        · right
          simp [toPState, Hl, prvalsMatch, GMap.lookup_fmap', hp0, hm]
    generalize Hs1 : ({ s with progress := prs, prvals := pvs, isLearner := learnerOf cfg prs id } : NState) = s1 at H1 Hc Hms Hmm
    have Hl1 : s1.role = .leader := by rw [← Hs1]; exact Hl
    have Hpl1 : (toPState s1).role = .leader := by simp [toPState, Hl1, proleRole]
    -- the commit
    have H2 : Step cfg id (toPState s1) []
        (toPState { s1 with logst := { s1.logst with committed := c } }) := by
      rcases Hc with rfl | ⟨Hlt, Hle, Htm, Hq⟩
      · have e : ({ s1 with logst := { s1.logst with committed := s1.logst.committed } } : NState)
            = s1 := by cases s1; rfl
        rw [e]; exact .refl _
      · have e : toPState { s1 with logst := { s1.logst with committed := c } } =
            { toPState s1 with commit := c } := by simp [toPState, Hl1]
        rw [e]
        exact .commit _ c Hpl1 Hlt Hle Htm Hq
    generalize Hs2 : ({ s1 with logst := { s1.logst with committed := c } } : NState) = s2
      at H2 Hms
    have Hl2 : s2.role = .leader := by rw [← Hs2]; exact Hl1
    -- the appends
    have H3 : Step cfg id (toPState s2) []
        (toPState { sendMsgs s2 ms with prvals := pvs2, lt := lt' }) := by
      have e : toPState { sendMsgs s2 ms with prvals := pvs2, lt := lt' } =
          toPState { sendMsgs s2 ms with prvals := pvs2 } := rfl
      rw [e, toPState_prvals (sendMsgs s2 ms) pvs2 (fun _ => by
        rw [Hmm]; rw [← Hs2]; rfl), toPState_sendMsgs]
      exact .sendApps _ ms (by simp [toPState, Hl2, proleRole]) Hms
    refine ⟨.trans _ _ _ _ _ H1 (.trans _ _ _ _ _ H2 H3), ?_⟩
    subst Hs1 Hs2
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    rcases Hc with rfl | ⟨Hlt, -⟩
    · exact Int.le_refl _
    · simp only [toPState] at Hlt; simp only [sendMsgs]; omega
  · rw [if_neg (show ¬ ({ s with progress := prs, prvals := pvs, isLearner := learnerOf cfg prs id } : NState).role = .leader
      from Hl)] at Hsw
    subst Hsw
    have e : toPState { s with progress := prs, prvals := pvs, isLearner := learnerOf cfg prs id } = toPState s := by
      simp [toPState, Hl]
    rw [e]
    exact ⟨.refl _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Int.le_refl _⟩

/-- What `applyConfChange` did at a node moved to the configuration `c'` (2026-10-13,
reconfiguration stage A2): installed new `Progress` objects (`prs`, tracking `c'`'s ids, records
`pvs`, each `Match` the old one or `0`), then `switchToConfig`'s rest (`SwitchOkC`). -/
def ApplyCCOkC (c' : CfgM) (id : w64) (s s' : NState) : Prop :=
  ∃ (prs : GMap w64 Loc) (pvs : GMap w64 Progress),
    domSet prs = c'.ids ∧ MatchKept s.prvals pvs ∧
    SwitchOkC c' id { s with progress := prs, prvals := pvs, isLearner := learnerOfC c' id } s'

end pure

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `r.applyConfChange(cc)`: builds a `confchange.Changer` on the node's tracker and last
index, runs `LeaveJoint`, `EnterJoint` or `Simple` as `cc` says (panicking on an error),
and installs the result (`switchToConfig`), returning the new `ConfState`.

**Scope: a change that keeps the voters** -- its model answer is a non-joint state with the
voters it started from and some learners `lrn'`: `ccApplyM cc.Transition ccs (cfgState cfg
lrn) = some (cfgState cfg lrn')` for the node's learners `lrn = domSet s.progress \ cfg`
(since 2026-10-13, stage L; until then `lrn' = lrn = ∅`): e.g. a change with `NodeId = 0`
(`ccApplyM_single_noop`), an `AddLearnerNode` or a `RemoveNode` of a non-voter
(`ccVoterKeep_addLearner`, `ccVoterKeep_removeLearner`); only `Simple` can answer that
(`ccApplyM_simple`). `ownRaftPhys` stays at `cfg`. Even so the Go code installs new
`Progress` objects (`checkAndCopy`'s copies, or fresh ones for a peer removed and re-added
in one change, whose `Match` is `0`), and at a leader commits and sends appends: the result
is `ApplyCCOk`, a protocol `Step` that receives nothing (`applyCCOk_step`). (Until
2026-10-13 it took `id ∈ cfg`, which a leader's `maybeCommit` needs; a leader is a voter by
`ownRaftPhys` now, and a learner may call this.)

The order in which an application must call this relative to `Advance`
(`issues/raft-advance-before-applyconfchange.md`) is `RawNode.ApplyConfChange`'s
concern; for an unchanged configuration it does not matter. -/
abbrev raft.applyConfChange.spec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (cc : raftpb.ConfChangeV2)
    (ccs : List raftpb.ConfChangeSingle) (dq : DFrac) (c' : CCState),
  -- the model's answer: `confchange`'s errors (which `applyConfChange` turns into a panic)
  -- and an undefined `Transition` with joint consensus (`ConfChangeV2.EnterJoint`'s panic,
  -- `issues/raft-unknown-transition-panic.md`) are `none`
  ccApplyM cc.Transition' ccs (cfgStateC c) = some c' →
  -- not too many tracked ids (`ownTrackerC`'s bound)
  (GMap.size c'.cfg.ids : Int) ≤ 2 ^ 62 →
  -- a removed or demoted leader steps down (`switchToConfig`)
  (s.role = .leader → id ∉ c'.cfg.voters → s.sdr = true) →
  -- a candidate stays a voter (`switchToConfig`)
  (s.role = .candidate ∨ s.role = .preCandidate → id ∈ c'.cfg.voters) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
      "Hccs" ∷ cc.Changes' ↦*{dq} ccs }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"applyConfChange")) (Val #cc))
  {{ (cs : raftpb.ConfState) (xs os ls lns : List w64) (s' : NState), RET #cs;
      ownRaftPhysCV c'.cfg c'.cfg.voters r id s' ∗
      cc.Changes' ↦*{dq} ccs ∗
      cs.Voters' ↦* xs ∗ cs.VotersOutgoing' ↦* os ∗ cs.Learners' ↦* ls ∗
      cs.LearnersNext' ↦* lns ∗
      ⌜xs ≡ₚ elements c'.cfg.incoming ∧ os ≡ₚ elements c'.cfg.outgoing ∧
        ls ≡ₚ elements c'.cfg.learners ∧ lns ≡ₚ elements c'.cfg.learnersNext ∧
        cs.AutoLeave' = c'.cfg.autoLeave⌝ ∗
      ⌜ApplyCCOkC c'.cfg id s s'⌝ }}

/-- The statement on `ownRaftPhys` until 2026-10-13 (a change that keeps the voters `cfg`),
derived by `spec_simple`. -/
abbrev raft.applyConfChange.specS : Prop :=
  ∀ (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (cc : raftpb.ConfChangeV2)
    (ccs : List raftpb.ConfChangeSingle) (dq : DFrac) (lrn' : GSet w64),
  (∀ k, k ∈ lrn' → k ∉ cfg) →
  (GMap.size (cfg ∪ lrn') : Int) ≤ 2 ^ 62 →
  ccApplyM cc.Transition' ccs (cfgState cfg (domSet s.progress \ cfg)) =
    some (cfgState cfg lrn') →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhys cfg r id s ∗
      "Hccs" ∷ cc.Changes' ↦*{dq} ccs }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"applyConfChange")) (Val #cc))
  {{ (cs : raftpb.ConfState) (xs ls : List w64) (s' : NState), RET #cs;
      ownRaftPhys cfg r id s' ∗
      cc.Changes' ↦*{dq} ccs ∗
      cs.Voters' ↦* xs ∗ cs.Learners' ↦* ls ∗
      ⌜xs ≡ₚ elements cfg ∧ ls ≡ₚ elements lrn' ∧
        cs.VotersOutgoing'.len = W64 0 ∧
        cs.LearnersNext'.len = W64 0 ∧
        cs.AutoLeave' = false⌝ ∗
      ⌜ApplyCCOk cfg id s s'⌝ }}


open Iris.ProofMode in
theorem raft.applyConfChange.spec_simple
    (H : raft.applyConfChange.spec (GF := GF) (hG := hG)) :
    raft.applyConfChange.specS (GF := GF) (hG := hG) := by
  intro cfg r id s cc ccs dq lrn' Hd' Hsz' Happ
  iintro %Φ ⟨#Hpkg, Hphys, Hccs⟩ HΦ
  icases ownRaftPhys_voter cfg r id s $$ Hphys with ⟨%Hv, Hphys⟩
  ihave Hphys := ownRaftPhys_toC' $$ Hphys
  have Hv' : (cfgState cfg lrn').cfg.voters = cfg := CfgM.voters_simple cfg lrn'
  have Hids : (cfgState cfg lrn').cfg.ids = cfg ∪ lrn' := by
    show (CfgM.simple cfg lrn').ids = _
    unfold CfgM.ids; rw [CfgM.voters_simple]; rfl
  iapply H (CfgM.simple cfg (domSet s.progress \ cfg)) r id s cc ccs dq (cfgState cfg lrn')
      (by rw [cfgStateC_simple]; exact Happ) (by rw [Hids]; exact Hsz')
      (fun hl hn => absurd (Hv (by rw [hl]; decide)) (by rw [Hv'] at hn; exact hn))
      (fun hc => by rw [Hv']; exact Hv (by rcases hc with h | h <;> rw [h] <;> decide))
    $$ [$Hpkg $Hphys $Hccs]
  inext
  iintro %cs %xs %os %ls %lns %s' ⟨Hphys, Hccs, Hxs, Hos, Hls, Hlns, %Hcs, %Hok⟩
  ihave Hphys := (show ownRaftPhysCV (GF := GF) (cfgState cfg lrn').cfg (cfgState cfg lrn').cfg.voters r id s'
      ⊢ ownRaftPhysC (CfgM.simple cfg lrn') r id s' from .rfl) $$ Hphys
  ihave Hphys := ownRaftPhysC_toS $$ Hphys
  obtain ⟨H1, H2, H3, H4, H5⟩ := Hcs
  have Hos0 : os = [] := perm_elements_empty _ H2
  have Hlns0 : lns = [] := perm_elements_empty _ H4
  subst Hos0 Hlns0
  ihave %Hol := ownSlice_len $$ Hos
  ihave %Hll := ownSlice_len $$ Hlns
  iapply HΦ $$ %cs %xs %ls %s'
  iframe Hphys Hccs Hxs Hls
  ipureintro
  obtain ⟨prs, pvs, Hpd, Hmk, Hsw⟩ := Hok
  refine ⟨⟨H1, H3, ?_, ?_, H5⟩, prs, pvs, fun _ => Hmk, ?_⟩
  · simp at Hol; word
  · simp at Hll; word
  · have Hl : learnerOfC (cfgState cfg lrn').cfg id = learnerOf cfg prs id := by
      unfold learnerOfC learnerOf
      rw [Hpd, Hids]
      show decide (id ∈ lrn') = decide (id ∈ cfg ∪ lrn' ∧ id ∉ cfg)
      by_cases h : id ∈ lrn'
      · simp [h, GMap.elem_of_union, Hd' id h]
      · simp [h, GMap.elem_of_union]
    rw [Hl] at Hsw
    unfold SwitchOkC at Hsw
    unfold SwitchOk
    split
    · rename_i hl
      have hin : id ∈ cfg := Hv (by rw [hl]; decide)
      rw [if_pos hl, if_pos (by rw [Hv']; exact hin)] at Hsw
      exact Hsw.simple (fun h => by rw [h] at hin; exact GMap.not_elem_of_empty _ hin)
    · rename_i hl
      rw [if_neg hl] at Hsw
      exact Hsw

end spec

end EtcdGrove
end Perennial
