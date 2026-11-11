/-
Lean-first (no Rocq counterpart). **`raft.Step`'s traced bundle on a report of an unreachable peer**
(2026-11-11, trace-check Q8 stage 1 slice 27n, Q27 (a) taken by the coordinator; `notes/decisions.md`,
"Q8 stage 1 (slice 27n)"): `stepBundle_traced.on UnreachPath` (`TracedRaftStep.lean`).

`RawNode.ReportUnreachable` steps `MsgUnreachable` (term zero, so no preamble), which logs no line at any
role: a follower and a candidate ignore it, a leader moves the peer's `Progress` back to probing
(`pr.BecomeProbe()`), its `Match` unchanged. Since Q27 (a), `MsgUnreachable` is a `StepEndTy` and its end
state is the step function's (`StepFnEnd`), which `LeaderNonpropResultC`'s report case now pins (nothing
queued, the transferee kept): `unreach_end`. The caller's resources are `TracedRaftStepPaths.lean`'s
`localR` (one family, `localF`, wherever `Step` may end); every gate but the receive hook (no line, the
type is untraced) and the preamble's (no step-down at term zero) is guarded by a type `MsgUnreachable` is
not; the closing wand re-reads the idle server, which does not see the `Progress` values beyond their
`Match` (`simIdleS_prvals`).
-/
module

public import Proof.go_etcd_io.raft.v3.TracedRaftStepPaths
public import Proof.go_etcd_io.raft.v3.TracedRaftStepLocal
public import Proof.go_etcd_io.raft.v3.raft__Step.MsgRest

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 TraceSim

set_option hygiene false in
/-- `m.Type' = MsgUnreachable` (`hu`) refutes a hypothesis `h` about another type. -/
local macro "unr_absurd" : tactic => `(tactic| (rw [hu] at h; simp [MsgUnreachable, MsgHup, MsgBeat,
  MsgProp, MsgApp, MsgAppResp, MsgVote, MsgVoteResp, MsgSnap, MsgHeartbeat, MsgHeartbeatResp,
  MsgSnapStatus, MsgCheckQuorum, MsgTransferLeader, MsgTimeoutNow, MsgReadIndex, MsgReadIndexResp,
  MsgPreVote, MsgPreVoteResp, MsgStorageAppendResp, MsgStorageApplyResp, MsgForgetLeader] at h))

set_option hygiene false in
/-- A gate guarded by a type `MsgUnreachable` is not (`hu` in context): vacuous. -/
local macro "unr_gate" : tactic => `(tactic| (iintro %h; exact False.elim (by
  first
  | unr_absurd
  | (rcases h with h | h <;> unr_absurd)
  | (rcases h with h | h | h <;> unr_absurd)
  | (obtain ⟨h, -⟩ := h; unr_absurd)
  | (rcases h with ⟨h, -⟩ | ⟨h, -⟩ <;> unr_absurd)
  | (rcases h with h | ⟨h, -⟩ <;> unr_absurd)
  | (obtain ⟨⟨h, -⟩ | ⟨h, -⟩, -⟩ := h <;> unr_absurd))))

section pure
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

/-- **A report of an unreachable peer** (`RawNode.ReportUnreachable`'s message: term zero). -/
def UnreachPath (_s : NState) (m : MessageM) : Prop := m.Type' = MsgUnreachable ∧ m.Term' = W64 0

/-- A report's end state is idle at the same server. -/
theorem unreach_simIdleS {s s' : NState} {pvs : GMap w64 Progress}
    (hpm : prvalsMatch pvs = prvalsMatch s.prvals) (he : s' = { sendMsgs s [] with prvals := pvs })
    (C : List w64) : SimIdleS C s = SimIdleS C s' := by
  rw [he, simIdleS_prvals C s [] pvs hpm]

end pure

section bundle
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

set_option maxHeartbeats 1000000 in
/-- **The end state of a report** (`StepEnd`, traced): `s` but for `Progress` values of the same `Match`
(a leader's `BecomeProbe`); nothing queued. -/
theorem unreach_end {c : CfgM} {id : w64} {m : MessageM} {ents : List EntryM} {ctx : List w8}
    {s s' : NState} (hu : m.Type' = MsgUnreachable) (hT0 : m.Term' = W64 0)
    (h : StepEnd c id m ents ctx s s') :
    ∃ pvs : GMap w64 Progress, prvalsMatch pvs = prvalsMatch s.prvals ∧
      s' = { sendMsgs s [] with prvals := pvs } := by
  have hnbf : ¬ PreBF m s := by
    unfold PreBF; rw [hT0]; intro h'; have := h'.1; simp at this
  have hpre : ∀ pvs, preState s m pvs = s := fun pvs => by simp [preState, hnbf]
  have hety : StepEndTy m.Type' := by unfold StepEndTy; simp [hu]
  have hnh : m.Type' ≠ MsgHup := fun h => by unr_absurd
  have hnv : m.Type' ≠ MsgVote := fun h => by unr_absurd
  have hnp : m.Type' ≠ MsgProp := fun h => by unr_absurd
  have hself : s = { sendMsgs s [] with prvals := s.prvals } := by cases s; simp [sendMsgs]
  obtain ⟨pvs0, hfn⟩ := (h hety).2.2.2 (fun h' => h'.1 hT0) hnh hnv
  rw [hpre pvs0] at hfn
  obtain ⟨hf, hc, hl⟩ := hfn
  cases hr : s.role with
  | follower =>
    obtain ⟨scfg, sv, d, c', hres⟩ := hf hr
    obtain ⟨-, -, he⟩ := StepProof.followerStepResult_rnoop c id s m ents sv d s' ctx (.inr (.inl hu)) hres
    exact ⟨s.prvals, rfl, by rw [he]; exact hself⟩
  | candidate =>
    obtain ⟨scfg, sv, d, c', hres⟩ := hc (.inl hr)
    obtain ⟨-, -, he⟩ :=
      StepProof.candidateStepResult_rest c id s m ents sv d s' ctx (.inr (.inr (.inl hu))) hres
    exact ⟨s.prvals, rfl, by rw [he]; exact hself⟩
  | preCandidate =>
    obtain ⟨scfg, sv, d, c', hres⟩ := hc (.inr hr)
    obtain ⟨-, -, he⟩ :=
      StepProof.candidateStepResult_rest c id s m ents sv d s' ctx (.inr (.inr (.inl hu))) hres
    exact ⟨s.prvals, rfl, by rw [he]; exact hself⟩
  | leader =>
    obtain ⟨d, hres⟩ := hl hr
    unfold LeaderStepResultC at hres
    rw [if_neg hnp] at hres
    obtain ⟨-, hres⟩ := hres
    unfold LeaderNonpropResultC at hres
    rcases hres with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ |
      ⟨-, lt', ms, pvs, rfl, -, hpm, hun⟩ | ⟨h, -⟩
    rotate_right 2
    · obtain ⟨rfl, rfl⟩ := hun hu
      exact ⟨pvs, hpm, rfl⟩
    all_goals exfalso
    all_goals unr_absurd

set_option maxHeartbeats 800000 in
/-- **`raft.Step`'s traced bundle on a report of an unreachable peer.** -/
theorem stepBundle_traced_unreach : stepBundle_traced.on (GF := GF) (hG := hG) UnreachPath := by
  intro γ md c r id s m ents sn ctx rs γd Λ bt hp htr hpv hcq hty hwf hloc hhup hto hT hmT hok hfit _ _ _ _ _
  obtain ⟨hu, hT0⟩ := hp
  have hnbf : ¬ PreBF m s := by
    unfold PreBF; rw [hT0]; intro h; have := h.1; simp at this
  have hpre : ∀ pvs, preState s m pvs = s := fun pvs => by simp [preState, hnbf]
  have hsome : s.gh.tr ≠ none := by rw [htr]; simp
  iintro ⟨Hcap, -, #Hnosnap⟩
  imodintro
  iexists localR bt γ md c r id s Λ
  isplitl [Hcap]
  · dsimp only [localR]; iexact Hcap
  isplitr
  · iunfold stepGates
    dsimp only [ghostIn, localR]
    isplitr
    · -- the receive hook: no line for an untraced type
      iintro ⟨Hgh, Hc⟩
      have hrg : recvGate id s c ⟨m, ents, sn, ctx, rs⟩ = none := by
        apply recvGate_none_of
        intro ty hty'
        have hm : mtypeOf MsgUnreachable = none := rfl
        rw [hu, hm] at hty'; cases hty'
      rw [hrg]
      unfold localF trFam
      rw [htr]
      iapply trCapB_gateNone γd γ r id c bt _ _ Λ _ (fun C cs P h => simIdle_phaseAt C s cs P h)
      iframe Hgh Hc
    isplitr
    · -- the preamble: no step-down at term zero
      unfold preGate
      iintro %_ HG0
      rw [if_neg hnbf]
      imodintro
      iexact HG0
    isplitr
    · iintro %h; exact (h.1 hT0).elim
    isplitr
    · unr_gate
    isplitr
    · unr_gate
    isplitr
    · -- the step functions' gates, at `s` (no preamble), each guarded by another type
      unfold stepFnGates
      iintro %pvs
      rw [hpre pvs]
      dsimp only
      isplit
      · iintro %hr
        unfold followerGates
        isplitr
        · unr_gate
        isplitr
        · unr_gate
        isplitr
        · unr_gate
        isplitr
        · unr_gate
        · imodintro; unr_gate
      isplit
      · iintro %hr
        unfold candidateGates
        isplitr
        · unr_gate
        isplitr
        · unr_gate
        isplitr
        · unr_gate
        isplitr
        · unr_gate
        isplitr
        · unr_gate
        isplitr
        · iintro %h; exact h.elim
        isplitr
        · imodintro; unr_gate
        isplitr
        · iexact Hnosnap
        isplitr
        · unr_gate
        isplitr
        · imodintro; unr_gate
        · unr_gate
      · iintro %hr
        unfold leaderGates
        isplitr
        · imodintro; unr_gate
        isplitr
        · unr_gate
        isplitr
        · imodintro; unr_gate
        isplitr
        · unr_gate
        isplitr
        · unr_gate
        isplitr
        · iexact Hnosnap
        isplitr
        · unr_gate
        isplitr
        · unr_gate
        isplitr
        · unr_gate
        isplitr
        · imodintro; unr_gate
        isplitr
        · unr_gate
        isplitr
        · imodintro; unr_gate
        isplitr
        · unr_gate
        isplitr
        · imodintro; unr_gate
        isplitr
        · imodintro; unr_gate
        isplitr
        · imodintro; unr_gate
        · imodintro; unr_gate
    · ipureintro
      exact ⟨localF_permInv bt γ md c r id s Λ, IdxFree.of_some _ hsome, IdxFree.of_some _ hsome,
        IdxFree.of_some _ hsome, fun _ _ => IdxFree.of_some _ hsome⟩
  · -- the closing wand: the end state idle at the same server; nothing queued
    iapply stepClose_of_at _ _ _ _ _ _ _ _ _ _
      (fun _ => CloseAt.of_ne (fun h => False.elim (by unr_absurd)))
    iunfold stepCloseAt
    iintro %s' %B %recv %_ %hend %_ Hout
    obtain ⟨pvs, hpm, he⟩ := unreach_end hu hT0 (hend (by rw [htr]; rfl))
    have hS : ∀ C, SimIdleS C s = SimIdleS C s' := unreach_simIdleS hpm he
    have hout : OutTrStep s s' :=
      OutTrStep.of_sub (fun x hx => by rw [he] at hx; simpa [sendMsgs] using hx)
    ihave H : localF (GF := GF) bt γ md c r id s Λ s'.outbox $$ [Hout]
    · unfold stepOut
      dsimp only [localR]
      icases Hout with (H | H | H | H | ⟨%b, %N, H⟩) <;> iexact H
    unfold localF
    icases H with ⟨Hgh, H⟩
    imod trFam_idle s.gh.tr γ r id c bt s s' Λ hS $$ H with H
    imodintro
    iframe Hgh
    isplitl [H]
    · iexists bt
      iapply trCapB_monoΛ s.gh.tr γ r id c bt _ Λ _ (fun o h => .inl h) $$ H
    ipureintro; exact hout

end bundle

end EtcdGrove
end Perennial
