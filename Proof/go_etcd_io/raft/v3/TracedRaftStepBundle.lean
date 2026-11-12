/-
Lean-first (no Rocq counterpart). **`raft.Step` on the capability: the assembly** (2026-11-11, trace-check
Q8 stage 1 slice 30c, `notes/decisions.md`, "Q8 stage 1 (slice 30c)"). Raft-internal (not on
`etc/api/raft.txt`).

- **`stepBundle_traced_storAck`**: the storage acknowledgements (`Advance`'s `MsgStorageAppendResp`,
  `MsgStorageApplyResp`; slice 28n's design): no line, the end state's protocol reading the node's
  (`AckEnd`, which the closing wand learns since slice 30c), so the close at `s`. Over
  `stepBundle_traced.onA`: `stepBundle_traced.on` asks `StepEndTy`, which these types are not.
- **`stepBundle_traced`**: `stepBundle_traced.statement` (`TracedRaftStep.lean`), every path of a traced
  node's `Step`, from the per-path lemmas (`stepBundle_traced.on`/`.onC`/`.onG` of the path files; the
  coverage is slice 27d's table with 27b's won vote, 27n's `MsgUnreachable`, 29c/30c's `LeadAcc` and the
  storage acknowledgements). The case split: a local type by role; a traced type by its term against
  the node's (below: `StaleRecv`; above: the `UT*` paths; equal: by role, then by the message's outcome).
  The bootstrap log the paths premise (`γ.reBoot ≠ []`) comes from the capability (`trCapB_reBoot`),
  `MsgHup` at any role from `stepBundle_hup_R`.
- **`raft.Step.traced`**: `raft.Step.spec`'s triple at a traced node, the capability idle at `s` in and
  idle at the end state out (`raft.Step.tracedTriple`), from `raft.Step.spec` and the assembly: the
  traced counterpart of `raft.Step.untraced` (`TracedUntracedRaftStep.lean`).
- **For the node API**, which takes the bundle as a hypothesis on its own paths:
  `stepBundle_traced.on_of_statement` / `.onG_of_statement` (a path whose states carry `StepNodeOk` and,
  for a proposal, a batch of normal entries).
-/
module

public import Proof.go_etcd_io.raft.v3.TracedRaftStepPaths
public import Proof.go_etcd_io.raft.v3.TracedRaftStepLocal
public import Proof.go_etcd_io.raft.v3.TracedRaftStepHup
public import Proof.go_etcd_io.raft.v3.TracedRaftStepPropBundle
public import Proof.go_etcd_io.raft.v3.TracedRaftStepUnreach
public import Proof.go_etcd_io.raft.v3.TracedRaftStepRecv
public import Proof.go_etcd_io.raft.v3.TracedRaftStepRecvApp
public import Proof.go_etcd_io.raft.v3.TracedRaftStepRecvAppRej
public import Proof.go_etcd_io.raft.v3.TracedRaftStepRecvAppAccCand
public import Proof.go_etcd_io.raft.v3.TracedRaftStepRecvAppAccUT
public import Proof.go_etcd_io.raft.v3.TracedRaftStepRecvCandApp
public import Proof.go_etcd_io.raft.v3.TracedRaftStepRecvCand
public import Proof.go_etcd_io.raft.v3.TracedRaftStepRecvHb
public import Proof.go_etcd_io.raft.v3.TracedRaftStepRecvLeadReq
public import Proof.go_etcd_io.raft.v3.TracedRaftStepRecvLeadNA
public import Proof.go_etcd_io.raft.v3.TracedRaftStepRecvLeadAccBundle
public import Proof.go_etcd_io.raft.v3.TracedRaftStepRecvUTApp
public import Proof.go_etcd_io.raft.v3.TracedRaftStepRecvUTHb
public import Proof.go_etcd_io.raft.v3.TracedRaftStepRecvUTVote
public import Proof.go_etcd_io.raft.v3.TracedRaftStepRecvUTResp
public import Proof.go_etcd_io.raft.v3.TracedRaftStepRecvUTVoteResp
public import Proof.go_etcd_io.raft.v3.TracedRaftStepRecvVoteResp
public import Proof.go_etcd_io.raft.v3.TracedRaftStepRecvVoteRespLost
public import Proof.go_etcd_io.raft.v3.TracedRaftStepRecvVoteRespWon
public import Spec.go_etcd_io.raft.v3.raft__Step

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 TraceSim

section pure
variable [GooseExts]

/-- The storage acknowledgements are none of the types a gate guards on. -/
theorem ackTy_ne {t : w32} (h : AckTy t) :
    t ≠ MsgApp ∧ t ≠ MsgHeartbeat ∧ t ≠ MsgProp ∧ t ≠ MsgReadIndex ∧ t ≠ MsgTransferLeader ∧
    t ≠ MsgTimeoutNow ∧ t ≠ MsgBeat ∧ t ≠ MsgCheckQuorum ∧ t ≠ MsgPreVoteResp ∧ t ≠ MsgVote ∧
    t ≠ MsgPreVote ∧ t ≠ MsgHup ∧ t ≠ MsgVoteResp ∧ t ≠ MsgHeartbeatResp ∧ t ≠ MsgAppResp ∧
    t ≠ MsgSnap := by
  rcases h with rfl | rfl <;>
    simp [MsgStorageAppendResp, MsgStorageApplyResp, MsgAppResp, MsgHeartbeatResp, MsgVoteResp, MsgApp,
      MsgHeartbeat, MsgProp, MsgReadIndex, MsgTransferLeader, MsgTimeoutNow, MsgBeat, MsgCheckQuorum,
      MsgPreVoteResp, MsgVote, MsgPreVote, MsgHup, MsgSnap]

/-- No storage acknowledgement is one of the types `StepEnd` describes. -/
theorem ackTy_not_stepEndTy {t : w32} (h : AckTy t) : ¬ StepEndTy t := by
  intro h'
  unfold StepEndTy at h'
  rcases h with rfl | rfl <;>
    rcases h' with h' | h' | h' | h' | h' | h' | h' | h' | h' | h' <;> revert h' <;> decide

/-- The types the traced statement admits (`StepEndTy`, `AckTy`) are none of the four that
`raft.Step.spec`'s untraced-only premises name but the acknowledgements. -/
theorem stepTrTy_ne {t : w32} (h : StepEndTy t ∨ AckTy t) :
    t ≠ MsgSnap := by
  rcases h with h | h
  · unfold StepEndTy at h
    rcases h with h | h | h | h | h | h | h | h | h | h <;> subst h <;> decide
  · exact (ackTy_ne h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- **A storage acknowledgement's path**: an append acknowledgement at most at the node's term (an apply
acknowledgement is at term `0`, a local message's). -/
def StorAck (s : NState) (m : MessageM) : Prop := AckTy m.Type' ∧ uint.Z m.Term' ≤ uint.Z s.term

/-- `SimIdleS` reads the protocol reading only. -/
theorem simIdleS_congr {s s' : NState} (h : toPState s' = toPState s) (C : List w64) :
    SimIdleS C s = SimIdleS C s' := by
  have h1 : s'.term = s.term := congrArg PState.term h
  have h2 : s'.logst.committed = s.logst.committed := congrArg PState.commit h
  unfold SimIdleS; rw [h1, h2, h]

end pure

section bundle
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **`stepBundle_traced.on` for the storage acknowledgements**: its premises verbatim but `AckTy` in
place of `StepEndTy` (the acknowledgements are not among the types `StepEnd` describes). -/
abbrev stepBundle_traced.onA (Path : NState → MessageM → Prop) : Prop :=
  ∀ (γ : RaftNames) (md : GMode) (c : CfgM) (r : Loc) (id : w64) (s : NState) (m : MessageM)
    (ents : List EntryM) (sn : Option SnapshotM) (ctx : List w8) (rs : List Loc) (γd : GName)
    (Λ : Option TraceEv → Prop) (bt : Bool),
  Path s m →
  s.gh.tr = some γd →
  s.prevote = false → s.cq = false → AckTy m.Type' → NStateWf s →
  (trCapB s.gh.tr γ r id c bt (fun C => SimIdle C s) Λ ∗
      (recvTokOf γd m ents ctx ∗
        □ (∀ ty : MsgType, ⌜mtypeOf m.Type' = some ty ∧ ty.traced = true⌝ -∗
          isMessageC γ (absMsg ty m ents ctx))) ∗
      TrNoSnap s.gh.tr s.logst : IProp GF) ⊢
    |={⊤}=> ∃ R : StepG GF, R.G ∗ stepGates c r id s m ents sn ctx rs (ghostIn γ md c id s R) ∗
      stepClose γ md c id m ents ctx s R
        (fun s' => iprop(⌜OutTyStep s s'⌝ ∗ ∃ bt' : Bool, ⌜bt = true → bt' = true⌝ ∗
          trCapB s.gh.tr γ r id c bt' (fun C => SimIdle C s') (stepLastEv Λ)))

/-- **`raft.Step`'s traced bundle on a storage acknowledgement** (see the file header): `localR`'s
resources; no hook logs; the close at `s`, the end state's protocol reading the node's (`AckEnd`). -/
theorem stepBundle_traced_storAck : stepBundle_traced.onA (GF := GF) (hG := hG) StorAck := by
  intro γ md c r id s m ents sn ctx rs γd Λ bt hp htr hpv hcq hty hwf
  obtain ⟨hnA, hnH, hnP, hnRI, hnTL, hnTN, hnB, hnCQ, hnPVR, hnV, hnPV, hnHup, hnVR, hnHR, hnAR, -⟩ :=
    ackTy_ne hp.1
  have hnbf : ¬ PreBF m s := fun h => absurd h.1 (by have := hp.2; omega)
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
    · -- the receive hook: no line for a storage acknowledgement
      iintro ⟨Hgh, Hc⟩
      have hrg : recvGate id s c ⟨m, ents, sn, ctx, rs⟩ = none := by
        apply recvGate_none_of
        intro ty hty'
        have hn : mtypeOf m.Type' = none := by rcases hp.1 with h | h <;> rw [h] <;> rfl
        rw [hn] at hty'; cases hty'
      rw [hrg]
      unfold localF trFam
      rw [htr]
      iapply trCapB_gateNone γd γ r id c bt _ _ Λ _ (fun C cs P h => simIdle_phaseAt C s cs P h)
      iframe Hgh Hc
    isplitr
    · -- the preamble: no step-down (a term at most the node's)
      unfold preGate
      iintro %_ HG0
      rw [if_neg hnbf]
      imodintro
      iexact HG0
    isplitr
    · -- a stale acknowledgement answers nothing
      iintro %_ %ty %mm %hl
      exfalso
      rcases hl with ⟨-, -, h, -⟩ | ⟨-, h, -⟩
      · exact h.elim hnH hnA
      · exact hnPV h
    isplitr
    · iintro %h; exact (h.elim hnV hnPV).elim
    isplitr
    · iintro %h; exact (hnHup h).elim
    isplitr
    · unfold stepFnGates
      iintro %pvs
      rw [hpre pvs]
      isplit
      · iintro %_
        iunfold followerGates
        repeat (isplitr; · iguard_false [hnA, hnH, hnP, hnRI, hnTL, hnTN, hnB, hnCQ, hnPVR, hnV, hnPV, hnHup])
        iguard_false [hnA, hnH, hnP, hnRI, hnTL, hnTN, hnB, hnCQ, hnPVR, hnV, hnPV, hnHup]
      isplit
      · iintro %_
        iunfold candidateGates
        repeat (isplitr; · first | (rw [htr]; iexact Hnosnap) | iguard_false [hnA, hnH, hnP, hnRI, hnTL, hnTN, hnB, hnCQ, hnPVR, hnV, hnPV, hnHup, hnVR])
        iguard_false [hnA, hnH, hnP, hnRI, hnTL, hnTN, hnB, hnCQ, hnPVR, hnV, hnPV, hnHup, hnVR]
      · iintro %_
        iunfold leaderGates
        repeat (isplitr; · first | (rw [htr]; iexact Hnosnap) | iguard_false [hnA, hnH, hnP, hnRI, hnTL, hnTN, hnB, hnCQ, hnPVR, hnV, hnPV, hnHup, hnHR, hnAR])
        iguard_false [hnA, hnH, hnP, hnRI, hnTL, hnTN, hnB, hnCQ, hnPVR, hnV, hnPV, hnHup, hnHR, hnAR]
    · ipureintro
      exact ⟨localF_permInv bt γ md c r id s Λ, IdxFree.of_some _ hsome, IdxFree.of_some _ hsome,
        IdxFree.of_some _ hsome, fun _ _ => IdxFree.of_some _ hsome⟩
  · -- the closing wand: the end state's protocol reading the node's
    iapply stepClose_of_at _ _ _ _ _ _ _ _ _ _ (fun _ => CloseAt.of_ne hnP)
    iunfold stepCloseAt
    iintro %s' %B %recv %_ %_ %hack Hout
    obtain ⟨hps, hlt, hrd⟩ := hack (by rw [htr]; rfl) hp.1
    have hS : ∀ C, SimIdleS C s = SimIdleS C s' := simIdleS_congr hps
    have ho : s'.outbox = s.outbox := congrArg PState.outbox hps
    have hty' : OutTyStep s s' :=
      OutTyStep.of_app' [] (by rw [ho, List.append_nil])
        (TrScope.congr hlt (by rw [hrd]) (by rw [hrd])) (fun _ _ h => absurd h List.not_mem_nil)
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
    · isplitr; · ipureintro; exact hty'
      iexists bt
      isplitr; · ipureintro; exact fun h => h
      iapply trCapB_monoΛ s.gh.tr γ r id c bt _ Λ _ (fun o h => .inl h) $$ H
    ipureintro
    exact outTrStep_of_outOk (by rw [ho]; exact outOk_self s)

/-- **A traced cluster has a bootstrap log**: the capability's node is one of its voters `C`, and
`C.length ≤ γ.reBoot.length` (amendment A6, Q24). -/
theorem trCapB_reBoot {tr : Option GName} {γd : GName} (htr : tr = some γd) (γ : RaftNames) (r : Loc)
    (id : w64) (c : CfgM) (b : Bool) (Φ : List w64 → ServerC → List Etcdraft.Msg → Prop)
    (Λ : Option TraceEv → Prop) :
    trCapB (GF := GF) tr γ r id c b Φ Λ ⊢ ⌜γ.reBoot ≠ []⌝ ∗ trCapB tr γ r id c b Φ Λ := by
  subst htr
  iintro H
  iunfold trCapB at H
  icases H with ⟨%tn, %C, %tl, %cs, %P, #Hdir, %Hpf, #Htl, #Hlg, %Hnn, #Hinv, #Hrinv, Hnode, Hbt, %HΦ⟩
  isplitr
  · ipureintro
    obtain ⟨-, -, -, hid, hlen⟩ := Hpf
    intro h
    have := List.length_pos_of_mem hid
    rw [h, List.length_nil] at hlen
    omega
  iunfold trCapB
  iexists tn, C, tl, cs, P
  iframe Hdir Htl Hlg Hinv Hrinv Hnode Hbt
  isplitr; · ipureintro; exact Hpf
  isplitr; · ipureintro; exact Hnn
  ipureintro; exact HΦ

/-- A pure fact read off the premise, for the rest of the proof. -/
theorem entails_of_pure {P Q : IProp GF} {φ : Prop} (h1 : P ⊢ ⌜φ⌝ ∗ P) (h2 : φ → P ⊢ Q) : P ⊢ Q := by
  iintro HP
  icases h1 $$ HP with ⟨%hφ, HP⟩
  iapply (h2 hφ) $$ HP

set_option hygiene false in
/-- A path lemma (`.on`, `.onC` or `.onG`) at the step's arguments, with its path fact `hp` and its
`MsgHup` premise `hh`. -/
local macro "path" L:term:max hp:term:max hh:term:max : tactic => `(tactic|
  exact $L γ md c r id s m ents sn ctx rs γd Λ bt $hp htr hpv hcq hty hwf hloc' $hh hto hT hmT hok hfit hlrn
    hdom hnpc hsh (fun _ => hrb))

/-- **`raft.Step`'s resources from the capability, on every path** (see the file header). -/
theorem stepBundle_traced : stepBundle_traced.statement (GF := GF) (hG := hG) := by
  intro γ md c r id s m ents sn ctx rs γd Λ bt htr hpv hcq hty2 hwf hloc hapT hto hT hmT hok hfit hlrn hdom
    hnpc hsh hbatch hnode
  rcases hty2 with hty | hack
  rotate_left
  · -- a storage acknowledgement
    refine stepBundle_traced_storAck γ md c r id s m ents sn ctx rs γd Λ bt ⟨hack, ?_⟩ htr hpv hcq hack hwf
    rcases hack with h | h
    · exact hapT h
    · rw [hloc (.inr (.inr (.inr (.inr h))))]; exact uint_Z_nonneg _
  refine entails_of_pure (φ := γ.reBoot ≠ []) ?_ (fun hrb => ?_)
  · iintro ⟨Hc, Hr⟩
    icases trCapB_reBoot htr γ r id c bt _ Λ $$ Hc with ⟨%h, Hc⟩
    isplitr
    · ipureintro; exact h
    iframe Hc Hr
  have hloc' : m.Type' = MsgHup ∨ m.Type' = MsgBeat ∨ m.Type' = MsgProp → m.Term' = W64 0 := by
    intro h
    apply hloc
    rcases h with h | h | h
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl h))
  have hty0 := hty
  unfold StepEndTy at hty0
  rcases hty0 with h | h | h | h | h | h | h | h | h | h
  rotate_right 4
  · -- `MsgHup`, at any role (slice 26n): `stepBundle_hup_R`
    iintro ⟨Hcap, -, #Hnosnap⟩
    imod stepBundle_hup_R γ md c r id s m ents sn ctx rs γd Λ bt h htr hpv hty (hloc (.inl h)) hT hfit hlrn
      $$ [$Hcap $Hnosnap] with ⟨HG, Hgates, Hclose⟩
    imodintro
    iexists hupR bt γ md c r id s Λ
    iframe HG Hgates Hclose
  · -- `MsgBeat`
    have hh : m.Type' = MsgHup → s.role ≠ .leader := fun h' => absurd (h.symm.trans h') (by decide)
    by_cases hr : s.role = .leader
    · path stepBundle_traced_beat ⟨h, hr⟩ hh
    · path stepBundle_traced_localNoLine ⟨⟨.inl h, hr⟩, fun h' => absurd (h.symm.trans h') (by decide)⟩ hh
  · -- `MsgProp`
    have hh : m.Type' = MsgHup → s.role ≠ .leader := fun h' => absurd (h.symm.trans h') (by decide)
    by_cases hr : s.role = .leader
    · obtain ⟨hne, hnorm⟩ := hbatch h
      path stepBundle_traced_prop ⟨h, hr, hne, hnorm, hrb⟩ hh
    · path stepBundle_traced_localNoLine ⟨⟨.inr h, hr⟩, fun h' => (hbatch h').2⟩ hh
  · -- `MsgUnreachable`
    have hh : m.Type' = MsgHup → s.role ≠ .leader := fun h' => absurd (h.symm.trans h') (by decide)
    path stepBundle_traced_unreach ⟨h, hloc (.inr (.inr (.inr (.inl h))))⟩ hh
  all_goals
    have hh : m.Type' = MsgHup → s.role ≠ .leader := fun h' => absurd (h.symm.trans h') (by decide)
  · -- `MsgApp`
    have hmty : mtypeOf m.Type' = some .app := by rw [h]; rfl
    have hT0 : m.Term' ≠ W64 0 := hsh.2.2.2 .app hmty rfl
    rcases Int.lt_trichotomy (uint.Z m.Term') (uint.Z s.term) with hlt | heq | hgt
    · path stepBundle_traced_staleRecv ⟨⟨hT0, hlt⟩, .app, hmty, rfl⟩ hh
    · have hteq : m.Term' = s.term := by word
      cases hr : s.role with
      | follower =>
        by_cases hidx : uint.Z m.Index' < uint.Z s.logst.committed
        · path stepBundle_traced_folAppStale ⟨h, hteq, hr, hidx⟩ hh
        · by_cases hmt : PlogMatches s.logst.prev (s.logst.sents ++ s.logst.uents) (entryID.mk m.LogTerm' m.Index')
          · path stepBundle_traced_folAppAcc_on ⟨h, hteq, hr, by omega, hmt⟩ hh
          · path stepBundle_traced_folAppRej ⟨h, hteq, hr, by omega, hmt⟩ hh
      | candidate =>
        by_cases hidx : uint.Z m.Index' < uint.Z s.logst.committed
        · path (stepBundle_traced_candAppSR true) ⟨h, hteq, hr, fun _ => hidx, fun h' => by cases h'⟩ hh
        · by_cases hmt : PlogMatches s.logst.prev (s.logst.sents ++ s.logst.uents) (entryID.mk m.LogTerm' m.Index')
          · path stepBundle_traced_candAppAcc_on ⟨h, hteq, hr, by omega, hmt⟩ hh
          · path (stepBundle_traced_candAppSR false) ⟨h, hteq, hr, (fun h' => by cases h'), fun _ => ⟨by omega, hmt⟩⟩ hh
      | leader => path stepBundle_traced_leadReq ⟨.inl h, hteq, hr⟩ hh
      | preCandidate => exact absurd hr hnpc
    · by_cases hidx : uint.Z m.Index' < uint.Z s.logst.committed
      · path (stepBundle_traced_utAppSR true) ⟨h, hgt, fun _ => hidx, fun h' => by cases h'⟩ hh
      · by_cases hmt : PlogMatches s.logst.prev (s.logst.sents ++ s.logst.uents) (entryID.mk m.LogTerm' m.Index')
        · path stepBundle_traced_utAppAcc_on ⟨h, hgt, by omega, hmt⟩ hh
        · path (stepBundle_traced_utAppSR false) ⟨h, hgt, (fun h' => by cases h'), fun _ => ⟨by omega, hmt⟩⟩ hh
  · -- `MsgAppResp`
    have hmty : mtypeOf m.Type' = some .appResp := by rw [h]; rfl
    have hT0 : m.Term' ≠ W64 0 := hsh.2.2.2 .appResp hmty rfl
    rcases Int.lt_trichotomy (uint.Z m.Term') (uint.Z s.term) with hlt | heq | hgt
    · path stepBundle_traced_staleRecv ⟨⟨hT0, hlt⟩, .appResp, hmty, rfl⟩ hh
    · have hteq : m.Term' = s.term := by word
      cases hr : s.role with
      | follower => path stepBundle_traced_ignResp ⟨hteq, .appResp, hmty, .inl rfl, .inl hr⟩ hh
      | candidate =>
        path stepBundle_traced_ignResp ⟨hteq, .appResp, hmty, .inl rfl, .inr (.inl ⟨hr, by decide⟩)⟩ hh
      | leader =>
        cases hrej : m.Reject'
        · obtain ⟨hpok, hpdom, hfrom⟩ := hnode
          have hfp := hfrom h
          path stepBundle_traced_leadAcc ⟨h, hrej, hteq, hr, hfp, by rw [hpdom]; exact hfp, hpok⟩ hh
        · path stepBundle_traced_leadRespNA ⟨hteq, hr, .inl ⟨h, hrej⟩⟩ hh
      | preCandidate => exact absurd hr hnpc
    · path stepBundle_traced_utResp ⟨.inl h, hgt⟩ hh
  · -- `MsgHeartbeat`
    have hmty : mtypeOf m.Type' = some .heartbeat := by rw [h]; rfl
    have hT0 : m.Term' ≠ W64 0 := hsh.2.2.2 .heartbeat hmty rfl
    rcases Int.lt_trichotomy (uint.Z m.Term') (uint.Z s.term) with hlt | heq | hgt
    · path stepBundle_traced_staleRecv ⟨⟨hT0, hlt⟩, .heartbeat, hmty, rfl⟩ hh
    · have hteq : m.Term' = s.term := by word
      cases hr : s.role with
      | follower => path stepBundle_traced_folHb ⟨h, hteq, hr⟩ hh
      | candidate => path stepBundle_traced_candHb ⟨h, hteq, hr⟩ hh
      | leader => path stepBundle_traced_leadReq ⟨.inr h, hteq, hr⟩ hh
      | preCandidate => exact absurd hr hnpc
    · path stepBundle_traced_utHb ⟨h, hgt⟩ hh
  · -- `MsgHeartbeatResp`
    have hmty : mtypeOf m.Type' = some .heartbeatResp := by rw [h]; rfl
    have hT0 : m.Term' ≠ W64 0 := hsh.2.2.2 .heartbeatResp hmty rfl
    rcases Int.lt_trichotomy (uint.Z m.Term') (uint.Z s.term) with hlt | heq | hgt
    · path stepBundle_traced_staleRecv ⟨⟨hT0, hlt⟩, .heartbeatResp, hmty, rfl⟩ hh
    · have hteq : m.Term' = s.term := by word
      cases hr : s.role with
      | follower => path stepBundle_traced_ignResp ⟨hteq, .heartbeatResp, hmty, .inr (.inl rfl), .inl hr⟩ hh
      | candidate =>
        path stepBundle_traced_ignResp
          ⟨hteq, .heartbeatResp, hmty, .inr (.inl rfl), .inr (.inl ⟨hr, by decide⟩)⟩ hh
      | leader => path stepBundle_traced_leadRespNA ⟨hteq, hr, .inr h⟩ hh
      | preCandidate => exact absurd hr hnpc
    · path stepBundle_traced_utResp ⟨.inr h, hgt⟩ hh
  · -- `MsgVote`
    have hmty : mtypeOf m.Type' = some .vote := by rw [h]; rfl
    have hT0 : m.Term' ≠ W64 0 := hsh.2.2.2 .vote hmty rfl
    rcases Int.lt_trichotomy (uint.Z m.Term') (uint.Z s.term) with hlt | heq | hgt
    · path stepBundle_traced_staleRecv ⟨⟨hT0, hlt⟩, .vote, hmty, rfl⟩ hh
    · have hteq : m.Term' = s.term := by word
      path stepBundle_traced_voteReq ⟨h, hteq⟩ hh
    · path stepBundle_traced_utVote ⟨h, hgt⟩ hh
  · -- `MsgVoteResp`
    have hmty : mtypeOf m.Type' = some .voteResp := by rw [h]; rfl
    have hT0 : m.Term' ≠ W64 0 := hsh.2.2.2 .voteResp hmty rfl
    rcases Int.lt_trichotomy (uint.Z m.Term') (uint.Z s.term) with hlt | heq | hgt
    · path stepBundle_traced_staleRecv ⟨⟨hT0, hlt⟩, .voteResp, hmty, rfl⟩ hh
    · have hteq : m.Term' = s.term := by word
      cases hr : s.role with
      | follower => path stepBundle_traced_ignResp ⟨hteq, .voteResp, hmty, .inr (.inr rfl), .inl hr⟩ hh
      | leader =>
        path stepBundle_traced_ignResp ⟨hteq, .voteResp, hmty, .inr (.inr rfl), .inr (.inr ⟨hr, rfl⟩)⟩ hh
      | candidate =>
        by_cases hq : JQuorum c (granted (recordVote s.votes m.From' (!m.Reject')))
        · path stepBundle_traced_candVoteRespWon ⟨h, hteq, hr, hq⟩ hh
        · by_cases hl : JLost c (recordVote s.votes m.From' (!m.Reject'))
          · path stepBundle_traced_candVoteRespLost ⟨h, hteq, hr, hq, hl⟩ hh
          · path stepBundle_traced_candVoteRespPending ⟨h, hteq, hr, hq, hl⟩ hh
      | preCandidate => exact absurd hr hnpc
    · path stepBundle_traced_utVoteResp ⟨h, hgt⟩ hh

/-- **For the node API: the assembly on a path** whose states carry `StepNodeOk` and which is not a
proposal (a proposal's path: `stepBundle_traced.onG_of_statement`), with a local `MsgUnreachable` at
term `0`. The `MsgHup` and the bootstrap-log premises of `stepBundle_traced.on` are not needed (the
statement has neither). -/
theorem stepBundle_traced.on_of_statement (h : stepBundle_traced.statement (GF := GF) (hG := hG))
    {Path : NState → MessageM → Prop}
    (hP : ∀ s m, Path s m → StepNodeOk s m ∧ m.Type' ≠ MsgProp ∧ (m.Type' = MsgUnreachable → m.Term' = W64 0)) :
    stepBundle_traced.on (GF := GF) (hG := hG) Path := by
  intro γ md c r id s m ents sn ctx rs γd Λ bt hp htr hpv hcq hty hwf hloc _ hto hT hmT hok hfit hlrn hdom
    hnpc hsh _
  obtain ⟨hn, hnp, hu⟩ := hP s m hp
  have hna : ¬ AckTy m.Type' := fun ha => ackTy_not_stepEndTy ha hty
  exact h γ md c r id s m ents sn ctx rs γd Λ bt htr hpv hcq (.inl hty) hwf
    (fun h' => by
      rcases h' with h' | h' | h' | h' | h'
      · exact hloc (.inl h')
      · exact hloc (.inr (.inl h'))
      · exact hloc (.inr (.inr h'))
      · exact hu h'
      · exact absurd (.inr h') hna)
    (fun h' => absurd (.inl h') hna)
    hto hT hmT hok hfit hlrn hdom hnpc hsh (fun h' => absurd h' hnp) hn

/-- **For the node API: the assembly on a path of the names and the batch** (a proposal's, `PropAny`). -/
theorem stepBundle_traced.onG_of_statement (h : stepBundle_traced.statement (GF := GF) (hG := hG))
    {Path : RaftNames → List EntryM → NState → MessageM → Prop}
    (hP : ∀ γ ents s m, Path γ ents s m → StepNodeOk s m ∧
      (m.Type' = MsgProp → ents ≠ [] ∧ ∀ e ∈ ents, e.Type' = EntryNormal) ∧
      (m.Type' = MsgUnreachable → m.Term' = W64 0)) :
    stepBundle_traced.onG (GF := GF) (hG := hG) Path := by
  intro γ md c r id s m ents sn ctx rs γd Λ bt hp htr hpv hcq hty hwf hloc _ hto hT hmT hok hfit hlrn hdom
    hnpc hsh _
  obtain ⟨hn, hb, hu⟩ := hP γ ents s m hp
  have hna : ¬ AckTy m.Type' := fun ha => ackTy_not_stepEndTy ha hty
  exact h γ md c r id s m ents sn ctx rs γd Λ bt htr hpv hcq (.inl hty) hwf
    (fun h' => by
      rcases h' with h' | h' | h' | h' | h'
      · exact hloc (.inl h')
      · exact hloc (.inr (.inl h'))
      · exact hloc (.inr (.inr h'))
      · exact hu h'
      · exact absurd (.inr h') hna)
    (fun h' => absurd (.inl h') hna)
    hto hT hmT hok hfit hlrn hdom hnpc hsh hb hn

/-- **`raft.Step.spec` at a traced node** (see the file header): `raft.Step.spec`'s premises, but the four
that read `s.gh.tr` (a `MsgSnap`, excluded by the types; a snapshot's acknowledgement and an automatic
leave, excluded by two premises; a proposal's configuration changes, by its batch of normal entries),
with `stepBundle_traced.statement`'s; its resources with, in place of the caller's `R`, gates and closing
wand, the capability idle at `s`, the received message's token and raft facts and `TrNoSnap`; its result
with the capability idle at the end state, with some `booted` flag, and the node's last event
`stepLastEv Λ`. -/
abbrev raft.Step.tracedTriple : Prop :=
  ∀ (c : CfgM)
    (md : GMode)
    (γ : RaftNames) (r : Loc) (id : w64) (s : NState)
    (ml : Loc) (m : MessageM)
    (ents : List EntryM)
    (ctx : List w8) (sn : Option SnapshotM) (rs : List Loc) (γd : GName)
    (Λ : Option TraceEv → Prop) (bt : Bool),
  StepMsg m →
  (m.Type' = MsgHup →
     m.Term' = W64 0 ∧
     uint.Z s.term + 1 < 2 ^ 64 ∧
     (s.prevote = true → uint.Z s.term + 1 ≤ uint.Z s.gh.tc) ∧
     uint.Z s.logst.fl ≤ uint.Z s.logst.applied) →
  (m.Type' = MsgVote →
     m.To' = id ∧ m.Term' ≠ W64 0 ∧
     m.From' ≠ W64 0) →
  (m.Type' = MsgVoteResp →
     m.To' = id ∧ m.Term' ≠ W64 0) →
  (m.Type' = MsgPreVote →
     m.To' = id ∧ m.Term' ≠ W64 0 ∧
     m.From' ≠ W64 0 ∧ m.From' ≠ id ∧
     (s.term = W64 0 →
      plogUpToDate s.logst.prev (s.logst.sents ++ s.logst.uents)
        (entryID.mk m.LogTerm' m.Index') = true) ∧
     (uint.Z m.Term' ≤ uint.Z s.term ∨ uint.Z m.Term' ≤ uint.Z s.gh.tc)) →
  (m.Type' = MsgPreVoteResp →
     m.To' = id ∧ m.Term' ≠ W64 0 ∧
     m.From' ≠ W64 0 ∧
     (s.role = .preCandidate → uint.Z s.term + 1 < 2 ^ 64)) →
  (m.Type' = MsgApp →
     m.To' = id ∧ m.Term' ≠ W64 0 ∧
     m.From' ≠ W64 0 ∧ m.From' ≠ id) →
  (m.Type' = MsgHeartbeat →
     m.To' = id ∧ m.Term' ≠ W64 0 ∧
     m.From' ≠ W64 0 ∧ m.From' ≠ id) →
  (m.Type' = MsgAppResp →
     m.To' = id ∧ m.Term' ≠ W64 0 ∧
     m.From' ≠ W64 0 ∧
     (m.Reject' = true → m.From' ≠ id)) →
  (m.Type' = MsgHeartbeatResp →
     m.To' = id ∧ m.Term' ≠ W64 0 ∧
     m.From' ≠ W64 0 ∧ m.From' ≠ id) →
  (m.Type' = MsgSnap →
     m.To' = id ∧ m.Term' ≠ W64 0 ∧
     m.From' ≠ W64 0 ∧ m.From' ≠ id) →
  (m.Type' = MsgBeat ∨ m.Type' = MsgCheckQuorum → m.Term' = W64 0) →
  (m.Type' = MsgProp →
     m.Term' = W64 0 ∧
     (m.From' = W64 0 ∨ m.From' = id)) →
  (m.Type' = MsgStorageAppendResp →
     (∀ sv, sn = some sv →
        snapHit s.logst.snap sv.Metadata'.Index' = s.logst.sat ∧
        uint.Z sv.Metadata'.Index' ≤ uint.Z s.logst.prev.index' ∧
        s.role = .follower ∧ ((md.isDyn = false ∧ SnapAckOk γ id sv) ∨ SnapAckDyn md s sv) ∧
        (s.logst.snap ≠ none → s.logst.lent = false →
          uint.Z sv.Metadata'.Index' ≤ uint.Z s.logst.sxt) ∧
        (∀ k, s.gh.snp = some k → uint.Z k.sid.index' ≤ uint.Z sv.Metadata'.Index')) ∧
     uint.Z m.Term' ≤ uint.Z s.term ∧
     (m.Term' = W64 0 ∨ m.Term' = s.term →
      m.Index' ≠ W64 0 →
      StableOk (ackLog s.logst sn) (entryID.mk m.LogTerm' m.Index')) ∧
     s.gh.unst = false) →
  (m.Type' = MsgStorageApplyResp → m.Term' = W64 0) →
  (m.Type' = MsgReadIndex → m.Term' = W64 0) →
  (m.Type' = MsgReadIndexResp →
     m.To' = id ∧ m.Term' ≠ W64 0 ∧ m.From' ≠ W64 0 ∧ m.From' ≠ id) →
  RestMsgOk s m ents ctx →
  NStateWf s →
  md.Pre m ents s →
  (m.Type' = MsgSnap → s.gh.ns = false) →
  -- the traced bundle's premises (`stepBundle_traced.statement`'s but `NStateWf s`, above)
  s.gh.tr = some γd →
  s.prevote = false → s.cq = false → (StepEndTy m.Type' ∨ AckTy m.Type') →
  (m.Type' = MsgHup ∨ m.Type' = MsgBeat ∨ m.Type' = MsgProp ∨ m.Type' = MsgUnreachable ∨
    m.Type' = MsgStorageApplyResp → m.Term' = W64 0) →
  (m.Type' = MsgStorageAppendResp → uint.Z m.Term' ≤ uint.Z s.term) →
  (∀ ty, mtypeOf m.Type' = some ty → ty.traced = true → m.To' = id) →
  uint.Z s.term + 1 < traceNumBound → uint.Z m.Term' < traceNumBound →
  (∀ ty, mtypeOf m.Type' = some ty → MsgTrOk γ (absMsg ty m ents ctx)) →
  receiptBound GF + γ.reBoot.length ≤ traceNumBound →
  c.learners = ∅ → domSet s.progress ⊆ c.voters ∪ c.learners →
  s.role ≠ .preCandidate → TrRecvShape m ents →
  (m.Type' = MsgProp → ents ≠ [] ∧ ∀ e ∈ ents, e.Type' = EntryNormal) →
  StepNodeOk s m →
  -- (`raft.Step.spec`'s premises that read `s.gh.tr`, at a traced node) an append acknowledgement of
  -- no snapshot (`TrNoSnap`), an apply acknowledgement with no automatic leave
  (m.Type' = MsgStorageAppendResp → sn = none) →
  (m.Type' = MsgStorageApplyResp → ents ≠ [] → c.autoLeave = false) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
      "Hghost" ∷ ownStepGhost γ md c id s ∗
      "#Hxfer" ∷ □ (⌜m.Type' = MsgTransferLeader ∧ m.Term' ≠ W64 0⌝ -∗ isLeader γ id m.Term') ∗
      "Hm" ∷ (
         "Hmsg_in" ∷ msgIn ml (if m.Type' = MsgProp then DFrac.own 1 else DFrac.discard)
                       ⟨m, ents, sn, ctx, rs⟩ ∗
         "Hents" ∷ (if m.Type' = MsgProp then
                      iprop((∃ cs, ccEntsOk ents cs) ∗ [∗list] e ∈ ents, entTk γ e) else emp) ∗
         "%Hprop" ∷ ⌜m.Type' = MsgProp →
                      ents ≠ [] ∧
                      (ents.length : Int) < 2^61⌝ ∗
         "%Hnors" ∷ ⌜m.Type' = MsgProp ∨ m.Type' = MsgReadIndex ∨ m.Type' = MsgTransferLeader →
                      rs = []⌝ ∗
         "%Happly" ∷ ⌜m.Type' = MsgStorageApplyResp →
                       ∀ e, ents.getLast? = some e →
                       uint.Z e.Index' ≤ uint.Z s.logst.committed ∧
                       uint.Z e.Index' ≤ uint.Z s.logst.applying⌝ ∗
         "#Hmsg" ∷ □ (∀ ty, ⌜mtypeOf m.Type' = some ty⌝ -∗
                            ⌜ty ≠ .snap⌝ -∗
                            isMessage γ (absMsg ty m ents ctx))) ∗
      "Hcred" ∷ rdCred γ (if m.Type' = MsgReadIndex then 1 else 0) ∗
      "Hlc" ∷ £ 1 ∗
      "#Hsnap" ∷ □ (⌜m.Type' = MsgSnap⌝ -∗
         ∃ (sv : SnapshotM) (scfg : CSLists),
           ⌜sn = some sv ∧ scfg = sv.Metadata'.ConfState'.lists ∧
             uint.Z sv.Metadata'.Index' < 2^61⌝ ∗
           isMessageC γ (absSnap m sv scfg) ∗
           snapDataOk γ sv.Metadata'.Index' sv.Data') ∗
      -- the capability idle at `s`, the received message's token and raft facts, `TrNoSnap`
      "Hcap" ∷ trCapB s.gh.tr γ r id c bt (fun C => SimIdle C s) Λ ∗
      "Htok" ∷ recvTokOf γd m ents ctx ∗
      "#Hmc" ∷ □ (∀ ty : MsgType, ⌜mtypeOf m.Type' = some ty ∧ ty.traced = true⌝ -∗
          isMessageC γ (absMsg ty m ents ctx)) ∗
      "#Hnosnap" ∷ TrNoSnap s.gh.tr s.logst }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #ml))
  {{ (err : GoInterface) (s' : NState) (c' : CfgM) (md' : GMode), RET #err;
      "Hphys" ∷ ownRaftPhysCV c' c'.voters r id s' ∗
      "Hghost" ∷ ownStepGhost γ md' c' id s' ∗
      "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
      "%Hrefines" ∷ ⌜md.StepOut c id m s s' md'⌝ ∗
      "%Hcfg'" ∷ ⌜(m.Type' = MsgStorageAppendResp → sn = none) → c' = c⌝ ∗
      "%Hlocal" ∷ ⌜((m.Type' = MsgStorageAppendResp → sn = none) → LocalStepOk m ents s s') ∧
                   (m.Type' = MsgStorageAppendResp → ∀ sv, sn = some sv →
                      c' = snapCfg sv sv.Metadata'.ConfState'.lists ∧
                      (∃ (prs : GMap w64 Loc) (pvs : GMap w64 Progress) (il : Bool),
                        s' = { s with logst := ackSnapLog s.logst m s.term sv, progress := prs,
                                      prvals := pvs, isLearner := il }) ∧
                      (∀ dec c0 h0 g, md = .dyn dec c0 h0 g →
                        ∃ cs', md' = .dyn dec c0 h0 ⟨uint.nat sv.Metadata'.Index', cs', g.fp, g.decs⟩))⌝ ∗
      "%Hframe" ∷ ⌜m.Type' ≠ MsgSnap → m.Type' ≠ MsgStorageApplyResp → m.Type' ≠ MsgTransferLeader →
                   (m.Type' = MsgStorageAppendResp → sn = none) → NetFrame s s'⌝ ∗
      "%Hxwframe" ∷ ⌜m.Type' = MsgTransferLeader → NetFrame s { s' with gh := s.gh } ∧
                   s'.gh = { s.gh with xw := s'.gh.xw } ∧ ∀ p, p ∈ s.gh.xw → p ∈ s'.gh.xw⌝ ∗
      "%Hterm" ∷ ⌜m.Type' ≠ MsgSnap → TermStep m s s'⌝ ∗
      "%Hresp" ∷ ⌜RespStep m s s'⌝ ∗
      "%Hsnapfr" ∷ ⌜m.Type' = MsgSnap → SnapStep m s s' ∧
                     ∀ sv, sn = some sv → SnapLogStep sv m s s'⌝ ∗
      "%Htrunc" ∷ ⌜m.Type' = MsgApp → AppTrunc m ents s s'⌝ ∗
      "Herr" ∷ (⌜err = interface.nil⌝ ∨
                (⌜m.Type' = MsgProp⌝ ∗
                 globalAddr ErrProposalDropped ↦□ err)) ∗
      -- (2026-11-12, implementation step 2) the step's `OutTyStep` (design §3.6, A2)
      "%Houtty" ∷ ⌜OutTyStep s s'⌝ ∗
      -- the capability back, idle at the end state, with some `booted` flag, at least the first one
      -- (implementation step 2, design N1)
      "Hcap" ∷ ∃ bt' : Bool, ⌜bt = true → bt' = true⌝ ∗
        trCapB s.gh.tr γ r id c bt' (fun C => SimIdle C s') (stepLastEv Λ) }}

/-- See `raft.Step.tracedTriple`: `raft.Step.spec` at the resources `stepBundle_traced` gives. -/
theorem raft.Step.traced (h : raft.Step.spec (GF := GF) (hG := hG))
    (hb : stepBundle_traced.statement (GF := GF) (hG := hG)) :
    raft.Step.tracedTriple (GF := GF) (hG := hG) := by
  intro c md γ r id s ml m ents ctx sn rs γd Λ bt Hsm Hhup Hvote Hvoteresp Hprevote Hprevoteresp
    Happ Hhb Happresp Hhbresp Hsnapt Hbeat Hprop Hsar Hsapr Hri Hrir Hrest Hwf Hpre Hnsx
    htr hpv hcq hty hloc hapT hto hT hmT hok hfit hlrn hdom hnpc hsh hbatch hnode hsnn hal
  iintro %Φ ⟨#Hinit, Hphys, Hghost, #Hxfer, Hm, Hcred, Hlc, #Hsnap, Hcap, Htok, #Hmc, #Hnosnap⟩ HΦ
  ihave Hb : (trCapB s.gh.tr γ r id c bt (fun C => SimIdle C s) Λ ∗
      (recvTokOf γd m ents ctx ∗
        □ (∀ ty : MsgType, ⌜mtypeOf m.Type' = some ty ∧ ty.traced = true⌝ -∗
          isMessageC γ (absMsg ty m ents ctx))) ∗
      TrNoSnap s.gh.tr s.logst : IProp GF) $$ [Hcap Htok]
  · iframe Hcap Htok Hmc Hnosnap
  imod hb γ md c r id s m ents sn ctx rs γd Λ bt htr hpv hcq hty Hwf hloc hapT hto hT hmT hok hfit hlrn hdom
    hnpc hsh hbatch hnode $$ Hb with ⟨%R, HG, Hgates, Hclose⟩
  have hne := stepTrTy_ne hty
  iapply h c md γ r id s ml m ents ctx sn rs R
    (fun s' => iprop(⌜OutTyStep s s'⌝ ∗ ∃ bt' : Bool, ⌜bt = true → bt' = true⌝ ∗
      trCapB s.gh.tr γ r id c bt' (fun C => SimIdle C s') (stepLastEv Λ)))
    Hsm Hhup Hvote Hvoteresp Hprevote Hprevoteresp
    Happ Hhb Happresp Hhbresp Hsnapt Hbeat Hprop Hsar Hsapr Hri Hrir Hrest Hwf Hpre Hnsx
    (fun ha => absurd ha hne) (fun ha hsn => absurd (hsnn ha) hsn)
    (fun ha hne' hauto => by rw [hal ha hne'] at hauto; cases hauto)
    (fun hp _ => noConf_of_normal ents (hbatch hp).2)
    $$ [Hphys Hghost Hm Hcred Hlc HG Hgates Hclose]
  · iframe Hinit Hphys Hghost Hxfer Hm Hcred Hlc Hsnap HG Hgates Hclose
  inext
  iintro %err %s' %c' %md' H
  iapply HΦ $$ %err %s' %c' %md'
  iNamed H
  icases HG with ⟨%Houtty, HG⟩
  iframe Hphys Hghost Herr HG
  ipureintro
  exact ⟨Hwf', Hrefines, Hcfg', Hlocal, Hframe, Hxwframe, Hterm, Hresp, Hsnapfr, Htrunc, Houtty⟩

/-- (2026-11-12, implementation step 2; design §8, Probe B item 6, N1) **A booted node stays booted
through a step**: `raft.Step.traced`'s (and the ticks', `RawNode`'s traced triples') end capability
with the monotone flag, at a node booted before the step (`bt = true`, after its first `Ready` line),
is booted: clause 1(a) of `rnTrace` (`delivered ≠ [] → booted`) is kept by a step, which leaves
`delivered` alone. -/
theorem trCapB_booted_of_mono (tr : Option GName) (γ : RaftNames) (r : Loc) (id : w64) (c : CfgM)
    (Φ : List w64 → ServerC → List Etcdraft.Msg → Prop) (Λ : Option TraceEv → Prop) :
    (∃ bt' : Bool, ⌜true = true → bt' = true⌝ ∗ trCapB (GF := GF) tr γ r id c bt' Φ Λ) ⊢
      trCapB tr γ r id c true Φ Λ := by
  iintro ⟨%bt', %h, H⟩
  rw [← h rfl]
  iexact H

/-- (Probe B item 6) **`raft.Step.traced` at a booted node gives back a booted capability**: the
triple at `bt = true`, its post's capability through `trCapB_booted_of_mono`. -/
theorem raft.Step.traced_booted (h : raft.Step.spec (GF := GF) (hG := hG))
    (hb : stepBundle_traced.statement (GF := GF) (hG := hG)) (c : CfgM) (γ : RaftNames)
    (r : Loc) (id : w64) (s s' : NState) (Λ : Option TraceEv → Prop) :
    raft.Step.tracedTriple (GF := GF) (hG := hG) ∧
      ((∃ bt' : Bool, ⌜true = true → bt' = true⌝ ∗
          trCapB s.gh.tr γ r id c bt' (fun C => SimIdle C s') (stepLastEv Λ)) ⊢
        trCapB (GF := GF) s.gh.tr γ r id c true (fun C => SimIdle C s') (stepLastEv Λ)) :=
  ⟨raft.Step.traced h hb, trCapB_booted_of_mono _ γ r id c _ _⟩

end bundle

end EtcdGrove
end Perennial
