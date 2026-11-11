/-
Lean-first (no Rocq counterpart). **A leader's accepted `MsgAppResp` of its term: raft's ghost state
moved past `maybeCommit` inside `"Hgcommit"`** (2026-11-11, trace-check Q8 stage 1 slice 28c,
`notes/decisions.md`, "Q8 stage 1 (slice 28c)").

The `Commit` line's facts read the leader's facts at the new commit index (`quorumLogF_commit`'s
`allFacts γ C σ'`), which only raft's ghost state past the commit gives. So a traced family moves raft's
ghost state, which `Step` hands it at the receive line (`ghostIn`), inside `"Hgcommit"`: the
acknowledgement recorded and the commit at the outcome `(b, N)` (`stepCD_appCommit`: `StepC.appResp` then
`StepC.commit` when `b`; `commitOkC_of_out`, `maybeCommit`'s own argument), one ghost step
(`ghost_stepCD`, the commit invariant's registry half opened with the later credit `"Hgcommit"` gives),
at the mode unchanged (`ghost_stepAppCommit`). The family then gives the ghost state back there
(`CloseMid`'s third case) and `Step` steps the rest (`raft__Step/AppRespMid.lean`).
-/
module

public import Proof.go_etcd_io.raft.v3.TracedRaftStepRecvLeadAcc
public import Proof.go_etcd_io.raft.v3.raft__Step.AppRespMid

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section pure
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext] [GoSemanticsFunctions]

/-- `Committed()`'s quorum index, over the `Match` map (`raft__maybeCommit.lean`'s private lemma, again):
a voter whose `Match` is at least a non-zero `N` has a `Progress`. -/
theorem isQuorumIndex_acked' (c : GSet w64) (pvs : GMap w64 Progress) (N M : w64)
    (Hpos : 0 < uint.Z N) (HM : uint.Z N ≤ uint.Z M) (H : IsQuorumIndex c (pvsMatchAt pvs) M) :
    IsQuorum c (domSet (GMap.filter (fun _ x => decide (uint.Z N ≤ uint.Z x))
      (prvalsMatch pvs))) := by
  obtain ⟨-, Hq, -⟩ := H
  unfold IsQuorum at Hq ⊢
  have Hsub : GMap.filter (fun v _ => decide (uint.Z M ≤ uint.Z (pvsMatchAt pvs v))) c ∩ c ⊆
      domSet (GMap.filter (fun _ x => decide (uint.Z N ≤ uint.Z x)) (prvalsMatch pvs)) ∩ c := by
    rw [GMap.elem_of_subseteq]
    intro v Hv
    rw [GMap.elem_of_intersection] at Hv ⊢
    refine ⟨?_, Hv.2⟩
    have Hle : uint.Z N ≤ uint.Z (pvsMatchAt pvs v) := by
      refine Int.le_trans HM ?_
      have Hv1 := Hv.1
      rw [GMap.mem_iff, GMap.lookup_filter] at Hv1
      cases Hc : c !! v with
      | none => simp [Hc] at Hv1
      | some u =>
        simp only [Hc, Option.filter] at Hv1
        split at Hv1
        · exact of_decide_eq_true ‹_›
        · simp at Hv1
    rw [GMap.elem_of_dom]
    change uint.Z N ≤ uint.Z (((pvs !! v).map Progress.matched).getD (W64 0)) at Hle
    cases E : pvs !! v with
    | none =>
      rw [E] at Hle
      simp only [Option.map_none, Option.getD_none] at Hle
      exfalso
      have : uint.Z (W64 0) = 0 := rfl
      omega
    | some p =>
      refine ⟨p.matched, ?_⟩
      rw [E] at Hle
      simp only [Option.map_some, Option.getD_some] at Hle
      simp only [prvalsMatch, GMap.lookup_filter]
      change Option.filter _ ((pvs !! v).map Progress.matched) = _
      rw [E]
      simp only [Option.map_some, Option.filter]
      simp only [decide_eq_true Hle, ↓reduceIte]
  have := GMap.subseteq_size Hsub
  omega

/-- **A committing outcome of `maybeCommit` is a `StepC.commit`** (`raft.maybeCommit.spec`'s
postcondition's argument, at the outcome). -/
theorem commitOkC_of_out {c : CfgM} {s : NState} {N : w64} (hr : s.role = .leader)
    (h : maybeCommitOut c s true N) : CommitOkC c (toPState s) N := by
  obtain ⟨Hq, Hb⟩ := h
  obtain ⟨-, Hlt, Hm⟩ := Hb.1 rfl
  refine ⟨Hlt, (plogTermAt_some_range _ _ _ _ Hm).2, Hm, ?_⟩
  simp only [toPState, ackedBy, hr, ↓reduceIte]
  have Hpos : 0 < uint.Z N := by have := uint_Z_nonneg s.logst.committed; omega
  obtain ⟨N0, N1, H0, H1, HN⟩ := Hq
  have Hle0 : uint.Z N ≤ uint.Z N0 := by rw [HN]; split <;> omega
  have Hle1 : uint.Z N ≤ uint.Z N1 := by rw [HN]; split <;> omega
  refine ⟨?_, ?_⟩
  · by_cases he : c.incoming = ∅
    · exact Or.inl he
    · exact Or.inr (isQuorumIndex_acked' _ s.prvals N N0 Hpos Hle0 (H0.2 he))
  · by_cases he : c.outgoing = ∅
    · exact Or.inl he
    · exact Or.inr (isQuorumIndex_acked' _ s.prvals N N1 Hpos Hle1 (H1.2 he))

/-- **The accepted response and `maybeCommit`'s outcome, as one model step**: `StepC.appResp` (the
sender's `Match` raised: `toPState` at `pvs`), then `StepC.commit` when the outcome commits. -/
theorem stepCD_appCommit (c : CfgM) (id : w64) (B : Int) (m : MessageM) (ents : List EntryM) (s : NState)
    (pvs : GMap w64 Progress) (b : Bool) (N : w64)
    (hto : m.To' = id) (hterm : m.Term' = s.term) (hrole : s.role = .leader) (hrej : m.Reject' = false)
    (hx : ∃ x, prvalsMatch s.prvals !! m.From' = some x)
    (hpvs : prvalsMatch pvs = appRespMatch s m.From' m.Index')
    (hout : maybeCommitOut c { s with prvals := pvs } b N) :
    StepCD c id B m s [absMsg .appResp m ents] (commitAt { s with prvals := pvs } b N) := by
  obtain ⟨x, Hx⟩ := hx
  have Hpr : (toPState s).role = .leader := by rw [toPState_role, hrole]; rfl
  have Hpr1 : (toPState { s with prvals := pvs }).role = .leader := Hpr
  have Hm0 : (toPState s).matched = prvalsMatch s.prvals := by simp [toPState, hrole]
  have H1 : StepCF c id (toPState s) [absMsg .appResp m ents] (toPState { s with prvals := pvs }) := by
    have he : toPState { s with prvals := pvs } = { toPState s with matched := prvalsMatch pvs } := by
      simp [toPState, hrole]
    rw [he, hpvs, appRespMatch_of_some s _ _ x Hx, ← Hm0]
    exact .appResp (absMsg .appResp m ents) (toPState s) x rfl hto hterm Hpr hrej (by rw [Hm0]; exact Hx)
  cases b with
  | false =>
    exact StepCD.frame H1 ⟨rfl, rfl, fun _ => ⟨hrole, rfl⟩⟩
  | true =>
    have H2 : StepCF c id (toPState { s with prvals := pvs }) []
        (toPState (commitAt { s with prvals := pvs } true N)) := by
      obtain ⟨Hlt, Hle, Hterm, Hq⟩ := commitOkC_of_out (s := { s with prvals := pvs }) hrole hout
      have he : toPState (commitAt { s with prvals := pvs } true N) =
          { toPState { s with prvals := pvs } with commit := N } := by
        simp [toPState, commitAt, hrole]
      rw [he]
      exact .commit _ N Hpr1 Hlt Hle Hterm Hq
    have H := StepCF.trans _ _ _ _ _ H1 H2
    rw [List.append_nil] at H
    exact StepCD.frame H ⟨rfl, rfl, fun _ => ⟨hrole, rfl⟩⟩

end pure

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **The family's ghost step inside `"Hgcommit"`**: raft's ghost state from a leader's `s` to the state
after `maybeCommit`'s outcome (`stepCD_appCommit`), one ghost step with the response's `isMessage` and
`"Hgcommit"`'s later credit, at the mode unchanged (an append response moves no ghost part). -/
theorem ghost_stepAppCommit (γ : RaftNames) (md : GMode) (c : CfgM) (id : w64) (s : NState) (m : MessageM)
    (ents : List EntryM) (pvs : GMap w64 Progress) (b : Bool) (N : w64)
    (hty : m.Type' = MsgAppResp) (hto : m.To' = id) (hterm : m.Term' = s.term) (hrole : s.role = .leader)
    (hrej : m.Reject' = false) (hx : ∃ x, prvalsMatch s.prvals !! m.From' = some x)
    (hpvs : prvalsMatch pvs = appRespMatch s m.From' m.Index')
    (hout : maybeCommitOut c { s with prvals := pvs } b N) :
    ⊢ £ 1 -∗ isMessage (GF := GF) γ (absMsg .appResp m ents) -∗ ownStepGhost γ md c id s ={⊤}=∗
      ownStepGhost γ md c id (commitAt { s with prvals := pvs } b N) := by
  iintro Hlc #Hm Hgs
  iunfold ownStepGhost at Hgs
  icases Hgs with ⟨Hg, Hrest⟩
  ihave ⟨#Hlr, %HB⟩ := ownRaftGhost_lastRec γ id (toPState s) $$ Hg
  imod lastRec_receipt γ _ $$ Hlr with #Hrc
  imod rdCred_zero (GF := GF) γ with Hcr
  have Hstep := stepCD_appCommit c id (plogLastIndexZ (toPState s).base (toPState s).log) m ents s pvs b N
    hto hterm hrole hrej hx hpvs hout
  imod ghost_stepCD γ md c id m _ HB s [absMsg .appResp m ents] _ Hstep
      (fun _ _ _ _ hmd _ HI => (StepProof.gmodePre_appResp (md := md) (ents := ents) hty
          (by rw [hrole]; decide)).dynHyp
        (fun h => absurd (hty.symm.trans h) (by w32_ne))
        (fun h => absurd (hty.symm.trans h) (by w32_ne)) hmd HI)
      ⟨StepProof.commitAt_gh' s pvs b N, StepProof.commitAt_storage s pvs b N⟩
      (fun _ x hx => .inl (by rw [StepProof.commitAt_outbox] at hx; exact hx))
    $$ Hrc [] [Hcr] [] Hlc Hg Hrest with ⟨%md', %Hout, Hg, Hrest⟩
  · iapply (BigSepL.bigSepL_singleton (Φ := fun _ x => isMessage (GF := GF) γ x)).2
    iexact Hm
  · rw [show rdCount [absMsg MsgType.appResp m ents] = 0 by rfl]; iexact Hcr
  · unfold msgsTks
    iapply (BigSepL.bigSepL_singleton (Φ := fun _ x => msgTks (GF := GF) γ x)).2
    rw [msgTks_nonprop γ _ (by simp [absMsg, absMsgFrom])]
    iempintro
  obtain rfl := StepProof.stepOut_appResp_md hty Hout
  imodintro
  iunfold ownStepGhost
  iframe Hg Hrest

end ghost

end EtcdGrove
end Perennial
