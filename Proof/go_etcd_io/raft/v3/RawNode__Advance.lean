/- Port of election_proof/proof_RawNode__Advance.v (857d09190).

Each queued message goes through `Step`'s spec; `StepsOk` (`InvRawnode.lean`) is the loop
invariant on the rest of the queue, carried across each step by `Step`'s `NetFrame`,
`LocalStepOk` and `TermStep` (`applying`, `prev` and `stored` kept, the term not moving
back) and `Step.commit_mono` (`committed` not moving back). The acknowledgement's
`StableOk` comes from the records of `stored` that `ownRawNode` keeps and the ghost
state's of the log, by Log Matching (`stableOk_of_stored`, 2026-10-10).

**The node's own responses (2026-10-10).** The queue starts with the self-addressed
responses `Ready` took from `msgsAfterAppend` (`Pending.self`); `pendingRel` has what
`Step`'s spec asks of each (`SelfMsgOk`, `isMessage`), `StepsOk` its term's bound, and
`SelfBound` keeps that bound at the state `Advance` started in (`s`). Stepping one moves
the term by `TermStep` and `RespStep` (`Spec/raft__Step.lean`), as `SelfStep` says here:
a vote or append response, of a term no later than `s`'s, by nothing (or, stale, keeps
the role); a pre-vote response, of a term at most one later, up to its term or one up
from a pre-candidate. `TermInv` is the loop's term invariant: the term is `s`'s or one
more, and while self-addressed responses remain, a pre-candidate is at `s`'s term -- so
a won pre-vote, which leaves a candidate, cannot be followed by another, and the
pre-candidate's no-wrap premise of `Step` is `Advance`'s own.

Lean notes: like its spec, the section fixes `hlc := HasLC.hasLC` and has `[AllG GF]`.
`wp_step_pending` is Rocq's; `pending_ok`, `apply_ack_ok_mono`, `advance_ok_cons` are
`PendingOk`, `applyAckOk_mono`, `stepsOk_cons` (`InvRawnode.lean`). Rocq's local
`in_types`/`not_ty` are the local macros `msg_ne`/`not_self`.

Raft v3.7 (2026-10-16, stage R5, D8): the queue holds pointers, each message owned
(`pendList`: `msgIn l □ st` with `pendingRel` of its state `st`), handed to `Step` for good;
the slot is set to `nil` after the step. The acknowledgements are the records `appendAckM`,
`applyAckM` (no `pendingOwn`: an apply acknowledgement is not a `MsgApp`, so `msgIn` asks no
capacity of it).
-/
module

public import Spec.go_etcd_io.raft.v3.RawNode__Advance
public import Spec.go_etcd_io.raft.v3.raft__Step
-- (D22 S-d3a) the snapshot's receipt (`loanRet`, `advRS`)
public import Proof.go_etcd_io.raft.v3.InvRawnodeReady
-- `Step.commit_mono`
public import Proof.go_etcd_io.raft.v3.Protocol.Facts

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3
open RawNodeOwnAccess

private theorem drop_cons_of_lookup {α : Type _} {l : List α} {k : Nat} {x : α}
    (h : l[k]? = some x) : l.drop k = x :: l.drop (k + 1) := by
  obtain ⟨hk, rfl⟩ := List.getElem?_eq_some_iff.1 h
  exact List.drop_eq_getElem_cons hk

section terms
variable [GooseExts]

/-- What stepping a self-addressed response of term `t` (a pre-vote response if `pv`)
does to the node's term and role, from `TermStep` and `RespStep`. -/
private def SelfStep (pv : Bool) (t : w64) (s s' : NState) : Prop :=
  (pv = false → uint.Z s'.term ≤ max (uint.Z s.term) (uint.Z t) ∧
      (uint.Z t < uint.Z s.term → s'.role = s.role)) ∧
  (pv = true → (uint.Z s'.term ≤ max (uint.Z s.term) (uint.Z t) ∨
        (s.role = .preCandidate ∧ uint.Z s'.term = uint.Z s.term + 1)) ∧
      (s'.role = .preCandidate → s.role = .preCandidate ∧ s'.term = s.term))

/-- What one pending step does to the term: a storage acknowledgement keeps it
(`LocalFrame`); a self-addressed response, `SelfStep`. -/
private def PendStep (p : Pending) (s s' : NState) : Prop :=
  match p with
  | .self pv t => SelfStep pv t s s'
  | _ => s'.term = s.term

/-- The self-addressed responses of a queue are no later than `s`'s term (one later for
a pre-vote response). -/
private def SelfBound (s : NState) (rest : List Pending) : Prop :=
  ∀ pv t, Pending.self pv t ∈ rest → uint.Z t ≤ uint.Z s.term + (if pv then 1 else 0) ∧
    (pv = true → uint.Z t ≤ uint.Z s.gh.tc)

/-- The loop's term invariant (see the file header): from `s` to `s1`, up by at most
one; and while self-addressed responses remain, a pre-candidate is still at `s`'s term. -/
private def TermInv (s s1 : NState) (rest : List Pending) : Prop :=
  uint.Z s.term ≤ uint.Z s1.term ∧ uint.Z s1.term ≤ uint.Z s.term + 1 ∧
  ((∃ pv t, Pending.self pv t ∈ rest) → s1.role = .preCandidate →
    uint.Z s1.term = uint.Z s.term) ∧
  -- (2026-10-17; 2026-10-10 to 2026-10-17: with pre-vote off the term does not move) within the
  -- term ceiling, a pre-candidate's next term too (`RNPv`)
  uint.Z s1.term ≤ uint.Z s.gh.tc ∧
  (s1.role = .preCandidate → uint.Z s1.term + 1 ≤ uint.Z s.gh.tc)

private theorem stepsOk_selfBound (s : NState) (l : List Pending) :
    StepsOk s l → SelfBound s l := by
  induction l with
  | nil => intro _ pv t h; cases h
  | cons p rest IH =>
    intro H pv t Hm
    cases p with
    | self pv' t' =>
      rcases List.mem_cons.1 Hm with h | h
      · cases h; exact H.1
      · exact IH H.2 pv t h
    | appendAck tm b e sn =>
      exact (stepsOk_ack_noself s _ rest (fun _ _ h => by cases h) H pv t
        ((List.mem_cons.1 Hm).resolve_left (fun h => by cases h))).elim
    | applyAck ce =>
      exact (stepsOk_ack_noself s _ rest (fun _ _ h => by cases h) H pv t
        ((List.mem_cons.1 Hm).resolve_left (fun h => by cases h))).elim

private theorem termInv_step (s s1 s2 : NState) (p : Pending) (rest : List Pending)
    (Hok : StepsOk s1 (p :: rest)) (Hsb : SelfBound s (p :: rest))
    (Hti : TermInv s s1 (p :: rest))
    (Hge : uint.Z s1.term ≤ uint.Z s2.term) (Hps : PendStep p s1 s2)
    (Hrl : s2.role = .preCandidate → s1.role = .preCandidate ∧ s2.term = s1.term) :
    TermInv s s2 rest := by
  obtain ⟨Hlo, Hhi, Hpre, Htc, Hpc⟩ := Hti
  have Hpc2 : s2.role = .preCandidate → uint.Z s2.term + 1 ≤ uint.Z s.gh.tc := fun h => by
    obtain ⟨h1, h2⟩ := Hrl h; rw [h2]; exact Hpc h1
  cases p with
  | self pv t =>
    obtain ⟨Hb, Hbtc⟩ := Hsb pv t List.mem_cons_self
    have Hpre1 := Hpre ⟨pv, t, List.mem_cons_self⟩
    cases pv with
    | false =>
      obtain ⟨Hle, Hrole⟩ := Hps.1 rfl
      simp only [Bool.false_eq_true, ↓reduceIte, Int.add_zero] at Hb
      have H2 : uint.Z s2.term ≤ uint.Z s1.term :=
        Int.le_trans Hle (Int.max_le.2 ⟨Int.le_refl _, by omega⟩)
      refine ⟨by omega, by omega, fun _ Hr => ?_, by omega, Hpc2⟩
      by_cases heq : uint.Z s1.term = uint.Z s.term
      · omega
      · have Hr1 : s1.role = .preCandidate := by rw [← Hrole (by omega)]; exact Hr
        exact absurd (Hpre1 Hr1) heq
    | true =>
      obtain ⟨Hab, Hrole⟩ := Hps.2 rfl
      simp only [↓reduceIte] at Hb
      have Hhi2 : uint.Z s2.term ≤ uint.Z s.term + 1 := by
        rcases Hab with Hle | ⟨Hr1, Heq⟩
        · exact Int.le_trans Hle (Int.max_le.2 ⟨Hhi, Hb⟩)
        · have := Hpre1 Hr1; omega
      have Htc2 : uint.Z s2.term ≤ uint.Z s.gh.tc := by
        rcases Hab with Hle | ⟨Hr1, Heq⟩
        · exact Int.le_trans Hle (Int.max_le.2 ⟨Htc, Hbtc rfl⟩)
        · have := Hpc Hr1; omega
      refine ⟨by omega, Hhi2, fun _ Hr => ?_, Htc2, Hpc2⟩
      obtain ⟨Hr1, Heq⟩ := Hrole Hr
      have := Hpre1 Hr1
      rw [Heq]; exact this
  | appendAck tm b e sn =>
    have Ht : s2.term = s1.term := Hps
    refine ⟨by rw [Ht]; exact Hlo, by rw [Ht]; exact Hhi, fun ⟨pv, t, h⟩ => ?_,
      by rw [Ht]; exact Htc, Hpc2⟩
    exact absurd h (stepsOk_ack_noself s1 _ rest (fun _ _ h => by cases h) Hok pv t)
  | applyAck ce =>
    have Ht : s2.term = s1.term := Hps
    refine ⟨by rw [Ht]; exact Hlo, by rw [Ht]; exact Hhi, fun ⟨pv, t, h⟩ => ?_,
      by rw [Ht]; exact Htc, Hpc2⟩
    exact absurd h (stepsOk_ack_noself s1 _ rest (fun _ _ h => by cases h) Hok pv t)

end terms

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- A premise of `Step` about another message type: the type is not it. -/
local macro "msg_ne" : tactic => `(tactic| (intro Hc; simp [MsgHup, MsgVote, MsgVoteResp,
  MsgPreVote, MsgPreVoteResp, MsgApp, MsgHeartbeat, MsgAppResp, MsgHeartbeatResp,MsgCheckQuorum, MsgSnap,
  MsgBeat, MsgProp, MsgStorageAppendResp, MsgStorageApplyResp, MsgReadIndex,
  MsgReadIndexResp, appendAckM, applyAckM, MsgForgetLeader, MsgUnreachable, MsgSnapStatus, MsgTimeoutNow, MsgTransferLeader] at Hc))

set_option hygiene false in
/-- A premise of `Step` about a type a self-addressed response (`Hty`: one of the three
response types) is not: vacuous. -/
local macro "not_self" : tactic => `(tactic| (
  intro Hc
  first
  | exact Hc.elim
  | (exfalso
     rcases Hty with Hty | Hty | Hty <;> rw [Hty] at Hc <;>
       simp [MsgHup, MsgVote, MsgVoteResp, MsgPreVote, MsgPreVoteResp, MsgApp, MsgHeartbeat,
         MsgAppResp, MsgHeartbeatResp,MsgCheckQuorum, MsgSnap, MsgBeat, MsgProp, MsgStorageAppendResp,
         MsgStorageApplyResp, MsgReadIndex, MsgReadIndexResp, MsgForgetLeader, MsgUnreachable, MsgSnapStatus, MsgTimeoutNow, MsgTransferLeader, MsgForgetLeader, MsgUnreachable, MsgSnapStatus, MsgTimeoutNow, MsgTransferLeader] at Hc)))

/-- One pending message through `Step`'s spec, in the ghost mode `md` (2026-10-14, stage B7
part 2; until then at the static configuration): the `MsgStorageAppendResp` acknowledges
persisted entries (`StableOk`) because it acknowledges the last entry of what the storage
holds, whose records `ownRawNode` keeps, nothing is unpersisted and no snapshot is pending
(`stableOk_of_stored`, 2026-10-10; until then because its index was in progress -- Rocq's
`ready_stable_ok`); a self-addressed response (2026-10-10) is what `pendingRel` says, and
a pre-candidate's term does not wrap (`Hnw`, for a pre-vote response). The dynamic mode's
premises: `PreFacts`, and for the `MsgStorageApplyResp` the caller's (`Hpre`: A1). -/
private theorem wp_step_pending
    (wp_raft_Step : raft.Step.spec (GF := GF) (hG := hG))
    (γ : RaftNames) (c : CfgM) (md : GMode) (r : Loc) (id : w64) (s : NState)
    (ml : Loc) (st : MsgSt) (p : Pending)
    (Hwf : NStateWf s) (Hok : PendingOk s p) (Hal : c.autoLeave = false)
    -- (D22 S-d3a) an acknowledgement of no snapshot (a snapshot's is `wp_step_snapack`'s); (D22
    -- S-d3b) its `StableOk` the caller's (`stableOk_of_stored`, or after a restore its miss,
    -- `stableOk_restored`)
    (Hack : ∀ t b e sn, p = .appendAck t b e sn → sn = none ∧
      ∀ x, e = some x → (t = W64 0 ∨ t = s.term) → StableOk s.logst x)
    (Hunp : s.logst.unpersisted = [])
    (Hnw : ∀ pv t, p = .self pv t → s.role = .preCandidate → uint.Z s.term + 1 < 2 ^ 64)
    (Hghoff : s.gh.unst = false) (Hpf : PreFacts md s)
    (Hpre : ∀ ce (m' : MessageM), p = .applyAck ce → m'.Type' = MsgStorageApplyResp →
      md.Pre m' ce s) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhysCV c c.voters r id s ∗
        ownStepGhost γ md c id s ∗ msgIn ml DFrac.discard st ∗ pendingRel γ id st p ∗ £ 1 }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #ml))
    {{ (err : GoInterface) (s' : NState) (md' : GMode), RET #err;
        ownRaftPhysCV c c.voters r id s' ∗ ownStepGhost γ md' c id s' ∗
        ⌜NStateWf s' ∧ md.StepOut c id st.msg s s' md' ∧ st.msg.Type' ≠ MsgSnap ∧
         ((∀ ce, p ≠ .applyAck ce) → st.msg.Type' ≠ MsgStorageApplyResp) ∧
         s'.logst.applying = s.logst.applying ∧
         s'.logst.unpersisted = s.logst.unpersisted ∧ s'.logst.snap = s.logst.snap ∧
         uint.Z s.term ≤ uint.Z s'.term ∧
         PendStep p s s' ∧
         s'.logst.prev = s.logst.prev ∧ logStoreRec s'.logst = logStoreRec s.logst ∧
         s'.logst.storage = s.logst.storage ∧ s'.prevote = s.prevote ∧ s'.gh = s.gh ∧
         -- (2026-10-17) no message of the queue makes a pre-candidate (`PreCandStep`)
         (s'.role = .preCandidate → s.role = .preCandidate ∧ s'.term = s.term) ∧
         -- (2026-10-25, T-M M2b) and a pre-candidate's campaign guard kept (`PreGuardF.step`)
         (∀ fp, PreGuardF fp s → PreGuardF fp s') ∧
         -- (D19i part 1) the floor kept, `applied` not moved back, and moved up to an apply
         -- acknowledgement's last entry
         s'.logst.fl = s.logst.fl ∧ uint.Z s.logst.applied ≤ uint.Z s'.logst.applied ∧
         (∀ ce, p = .applyAck ce → ∀ e, ce.getLast? = some e →
            uint.Z e.Index' ≤ uint.Z s'.logst.applied) ∧
         -- (2026-10-28, stage U0) a non-follower with a snapshot pending afterwards was one
         SnapRoleBack s s' ∧
         -- (2026-10-28, stage U3) an append acknowledgement does not move `applied`
         (st.msg.Type' = MsgStorageAppendResp → s'.logst.applied = s.logst.applied)⌝ }} := by
  iintro %Φ ⟨#Hinit, Hphys, Hghost, Hmin, #Hp, Hlc⟩ HΦ
  imod rdCred_zero_upd (GF := GF) γ with Hcr
  cases p with
  | self pv t =>
    rcases st with ⟨m, ents, sn, ctx, rsp⟩
    unfold pendingRel
    icases Hp with ⟨%Hsm, #Hmsg⟩
    obtain ⟨⟨Hty, Hfr, Hto, Hnz, Hen, Hcn, Hrj⟩, rfl, rfl⟩ := Hsm
    simp only at Hty Hfr Hto Hnz Hen Hcn Hrj ⊢
    subst Hen Hcn
    icases ownRaftPhysC_id_nz c r id s $$ Hphys with ⟨%Hidnz, Hphys⟩
    have Hfnz : m.From' ≠ W64 0 := by rw [Hfr]; exact Hidnz
    have Hsm : StepMsg m := by
      rcases Hty with h | h | h <;> simp [StepMsg, stepMsgTypes, h]
    iapply wp_raft_Step c md γ r id s ml m [] [] sn rsp Hsm
      (by not_self) (by not_self) (fun _ => ⟨Hto, Hnz⟩) (by not_self)
      (fun _ => ⟨Hto, Hnz, Hfnz, Hnw _ _ rfl⟩) (by not_self) (by not_self)
      (fun h => ⟨Hto, Hnz, Hfnz, fun Hr => by rw [Hrj h] at Hr; cases Hr⟩)
      (by not_self) (by not_self) (by not_self) (by not_self) (by not_self) (by not_self)
      (by not_self) (by not_self) (by not_self)
      (RestMsgOk.of_ne ⟨by not_self, by not_self, by not_self, by not_self, by not_self⟩) Hwf
      (GMode.Pre.of_facts Hpf (by not_self) (by not_self)) (fun h => absurd h (by not_self))
      $$ [$Hinit $Hphys $Hghost $Hlc Hmin Hcr]
    · have hP : m.Type' ≠ MsgProp := by not_self
      simp only [hP, ↓reduceIte, named]
      isplitl [Hmin]
      · isplitl [Hmin]
        · iexact Hmin
        isplitr
        · iempintro
        isplitr
        · ipureintro; not_self
        isplitr
        · ipureintro; not_self
        isplitr
        · ipureintro; not_self
        imodintro
        iintro %ty %Hty' %_
        iapply Hmsg $$ %ty %Hty'
      isplitl [Hcr]
      · rw [ite_eq_right (by not_self)]; iexact Hcr
      imodintro
      iintro %Hc
      exfalso
      revert Hc
      not_self
    · inext
      iintro %err %s' %c' %md' ⟨Hphys, Hghost, %Hwf', %Hstp, %Hcc, -, %Hframe, %Hterm, %Hresp, -⟩
      have e2 := Hcc (fun h => absurd h (by not_self)); subst c'
      have Hfr' := Hframe (by not_self) (by not_self) (fun h => absurd h (by not_self))
      have Htm := Hterm (by not_self)
      iapply HΦ $$ %err %s' %md'
      iframe Hphys Hghost
      ipureintro
      refine ⟨Hwf', Hstp, by not_self, fun _ => by not_self, Hfr'.1, Hfr'.2.2.1, Hfr'.2.1, Htm.1, ?_,
        Hfr'.2.2.2.1, Hfr'.2.2.2.2.1, Hfr'.2.2.2.2.2.1, Hfr'.2.2.2.2.2.2.1, Hfr'.2.2.2.2.2.2.2.1, ?role,
        fun _ => PreGuardF.step Htm, Hfr'.2.2.2.2.2.2.2.2.1, Hfr'.2.2.2.2.2.2.2.2.2, (fun _ h => by cases h),
        Htm.2.2.2.2.2.2, fun h => absurd h (by not_self)⟩
      case role =>
        intro h
        obtain ⟨Ht, Hor⟩ := Htm.2.2.2.2.2.1 h
        exact ⟨(Hor.resolve_right (by not_self)).1, Ht⟩
      show SelfStep _ _ s s'
      refine ⟨fun hpv => ?_, fun hpv => ?_⟩
      · -- a vote or append response
        have hnpv : m.Type' ≠ MsgPreVoteResp := by
          intro h; simp [h] at hpv
        refine ⟨Htm.2.2.1 (by not_self) hnpv (by not_self), fun Hlt => Hresp.1 ?_ Hlt⟩
        rcases Hty with h | h | h
        · exact .inr h
        · exact .inl h
        · exact absurd h hnpv
      · -- a pre-vote response
        exact Hresp.2 (by simpa using hpv)
  | appendAck t b e sn =>
    obtain ⟨Hsn0, Hsok0⟩ := Hack t b e sn rfl
    subst Hsn0
    unfold pendingRel
    icases Hp with ⟨%Hm, -⟩
    have Hm' : st = _ := Hm
    subst Hm'
    obtain ⟨Hle, -⟩ := Hok
    -- the acknowledged entry, if any (`Index` `0` otherwise: no `stableTo`): the caller's
    have Hsok' : (appendAckM id t (e.getD ⟨W64 0, W64 0⟩)).Term' = W64 0 ∨
        (appendAckM id t (e.getD ⟨W64 0, W64 0⟩)).Term' = s.term →
        (appendAckM id t (e.getD ⟨W64 0, W64 0⟩)).Index' ≠ W64 0 →
        StableOk (ackLog s.logst none)
          ⟨(appendAckM id t (e.getD ⟨W64 0, W64 0⟩)).LogTerm',
            (appendAckM id t (e.getD ⟨W64 0, W64 0⟩)).Index'⟩ := by
      intro ht hi
      cases e with
      | none => exact absurd rfl hi
      | some x => exact Hsok0 x rfl ht
    iapply wp_raft_Step c md γ r id s ml (appendAckM id t (e.getD ⟨W64 0, W64 0⟩)) [] [] none []
      (by simp [StepMsg, stepMsgTypes, appendAckM])
      (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne)
      (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne)
      (fun _ => ⟨(fun _ h => by cases h), Hle, Hsok', Hghoff⟩) (by msg_ne) (by msg_ne) (by msg_ne)
      (by msg_ne)
      (RestMsgOk.of_ne ⟨by msg_ne, by msg_ne, by msg_ne, by msg_ne, by msg_ne⟩) Hwf
      (GMode.Pre.of_facts Hpf (by msg_ne) (by msg_ne)) (fun h => absurd h (by msg_ne))
      $$ [$Hinit $Hphys $Hghost $Hlc Hmin Hcr]
    · have hP : (appendAckM id t (e.getD ⟨W64 0, W64 0⟩)).Type' ≠ MsgProp := by msg_ne
      simp only [hP, ↓reduceIte, named]
      have Hty0 : mtypeOf (appendAckM id t (e.getD ⟨W64 0, W64 0⟩)).Type' = none := rfl
      isplitl [Hmin]
      · isplitl [Hmin]
        · iexact Hmin
        isplitr
        · iempintro
        isplitr
        · ipureintro; msg_ne
        isplitr
        · ipureintro; msg_ne
        isplitr
        · ipureintro; msg_ne
        imodintro
        iintro %ty %Hty
        rw [Hty0] at Hty
        cases Hty
      isplitl [Hcr]
      · simp [appendAckM, MsgStorageAppendResp, MsgReadIndex]; iexact Hcr
      imodintro
      iintro %Hc
      exfalso
      revert Hc
      msg_ne
    · inext
      iintro %err %s' %c' %md' ⟨Hphys, Hghost, %Hwf', %Hstp, %Hcc, %Hloc, -, %Hterm, -⟩
      have e2 := Hcc (fun _ => rfl); subst c'
      obtain ⟨Hfr, Hap, -, Hapa⟩ := Hloc.1 (fun _ => rfl) (.inr (.inl rfl))
      iapply HΦ $$ %err %s' %md'
      iframe Hphys Hghost
      ipureintro
      exact ⟨Hwf', Hstp, by msg_ne, fun _ => by msg_ne, Hap (fun Hc => absurd Hc (by msg_ne)), Hfr.2.2.1,
        Hfr.2.2.2.1, by rw [Hfr.1]; exact Int.le_refl _, Hfr.1, Hfr.2.2.2.2.1, Hfr.2.2.2.2.2.1,
        Hfr.2.2.2.2.2.2.1, Hfr.2.2.2.2.2.2.2.1, Hfr.2.2.2.2.2.2.2.2.1,
        fun h => ⟨by rw [← Hfr.2.2.2.2.2.2.2.2.2.1]; exact h, Hfr.1⟩,
        fun _ => PreGuardF.step (Hterm (by msg_ne)), Hfr.2.2.2.2.2.2.2.2.2.2.1, Hfr.2.2.2.2.2.2.2.2.2.2.2, (fun _ h => by cases h),
        (Hterm (by msg_ne)).2.2.2.2.2.2, Hapa⟩
  | applyAck ce =>
    unfold pendingRel
    icases Hp with ⟨%Hm, -⟩
    have Hm' : st = _ := Hm
    subst Hm'
    iapply wp_raft_Step c md γ r id s ml (applyAckM id) ce [] none []
      (by simp [StepMsg, stepMsgTypes, applyAckM])
      (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne)
      (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne)
      (by msg_ne) (fun _ => rfl) (by msg_ne) (fun _ h => by rw [Hal] at h; cases h) (by msg_ne)
      (RestMsgOk.of_ne ⟨by msg_ne, by msg_ne, by msg_ne, by msg_ne, by msg_ne⟩) Hwf
      (Hpre ce _ rfl rfl) (fun h => absurd h (by msg_ne))
      $$ [$Hinit $Hphys $Hghost $Hlc Hmin Hcr]
    · have hP : (applyAckM id).Type' ≠ MsgProp := by msg_ne
      simp only [hP, ↓reduceIte, named]
      have Hty0 : mtypeOf (applyAckM id).Type' = none := rfl
      isplitl [Hmin]
      · isplitl [Hmin]
        · iexact Hmin
        isplitr
        · iempintro
        isplitr
        · ipureintro; msg_ne
        isplitr
        · ipureintro; msg_ne
        isplitr
        · ipureintro; intro _ e He; exact Hok e He
        imodintro
        iintro %ty %Hty
        rw [Hty0] at Hty
        cases Hty
      isplitl [Hcr]
      · simp [applyAckM, MsgStorageApplyResp, MsgReadIndex]; iexact Hcr
      imodintro
      iintro %Hc
      exfalso
      revert Hc
      msg_ne
    · inext
      iintro %err %s' %c' %md' ⟨Hphys, Hghost, %Hwf', %Hstp, %Hcc, %Hloc, -, %Hterm, -⟩
      have e2 := Hcc (fun h => absurd h (by msg_ne)); subst c'
      obtain ⟨Hfr, Hap, Happ, -⟩ := Hloc.1 (fun h => absurd h (by msg_ne)) (.inr (.inr rfl))
      iapply HΦ $$ %err %s' %md'
      iframe Hphys Hghost
      ipureintro
      exact ⟨Hwf', Hstp, by msg_ne, fun h => absurd rfl (h ce), Hap (fun _ e He => (Hok e He).2), Hfr.2.2.1,
        Hfr.2.2.2.1, by rw [Hfr.1]; exact Int.le_refl _, Hfr.1, Hfr.2.2.2.2.1, Hfr.2.2.2.2.2.1,
        Hfr.2.2.2.2.2.2.1, Hfr.2.2.2.2.2.2.2.1, Hfr.2.2.2.2.2.2.2.2.1,
        fun h => ⟨by rw [← Hfr.2.2.2.2.2.2.2.2.2.1]; exact h, Hfr.1⟩,
        fun _ => PreGuardF.step (Hterm (by msg_ne)), Hfr.2.2.2.2.2.2.2.2.2.2.1, Hfr.2.2.2.2.2.2.2.2.2.2.2,
        fun ce' h => by injection h with h; subst h; exact Happ rfl,
        (Hterm (by msg_ne)).2.2.2.2.2.2, fun h => absurd h (by msg_ne)⟩

/-- (2026-10-28, stage U3c) The dynamic mode's invariant (`RInv`), read off the ghost state. -/
private theorem ownStepGhost_rinv (γ : RaftNames) (dec : CCDec) (c0 : CCState) (h0 : CfgOk c0)
    (g : RGh) (c : CfgM) (id : w64) (s : NState) :
    ownStepGhost (GF := GF) γ (.dyn dec c0 h0 g) c id s ⊢
      ⌜RInv (effDec dec g.decs) c0 (rOf s g)⌝ ∗ ownStepGhost γ (.dyn dec c0 h0 g) c id s := by
  iintro H
  iunfold ownStepGhost at H
  icases H with ⟨Hg, Hr⟩
  iunfold ghostRest at Hr
  icases Hr with ⟨%Hnl, Hr, #Hcl⟩
  simp only [ghostRestM]
  icases Hr with ⟨%HC, #HM, #Hfr, Hcamp⟩
  isplitr
  · ipureintro; exact HC.2.2
  iunfold ownStepGhost
  iframe Hg
  iunfold ghostRest
  isplitr
  · ipureintro; exact Hnl
  iframe Hcl
  simp only [ghostRestM]
  iframe Hfr Hcamp HM
  ipureintro; exact HC

/-- (D22 S-d3a, 2026-10-21) **A snapshot `Ready`'s acknowledgement** through `Step`'s spec, its receipt
absorbed: the storage at the pending snapshot (`sat`), in the `sapp` window, where its `stableTo`
moves stable only what the storage holds (`stableOk_of_stored_ls`), or (D22 S-d3b) after a
restore not (its `stableTo` misses, `stableOk_restored`); then `appliedSnap` (`ackSnapLog`). The
acknowledgement's `StableOk` is the caller's (`Hsok`). (2026-10-28, stage U0) `appliedSnap` switches
to the snapshot's configuration: the node is a follower (`SnapFol`, a snapshot pending), and the
snapshot (the one handed out, `NGhost.snp`, in the log's `ksn`) certified in the storage's registry
(`Hkcert`), its `ConfState` naming a node (`loanCom`): statically its certificate's static facts make
`raft.Step`'s `SnapAckOk`. (2026-10-28, stage U3c) Dynamically its certificate's dynamic clause at the
committed log `D` up to the snapshot (the loan's, `SnapLoan.dlv`: the node's full prefix up to the
snapshot's index, ending at its id) makes `SnapAckDyn`, with `applied` below the snapshot's index and,
with nothing else pending, the snapshot at the boundary (the caller's, `Hdyn`); the ghost part moves
to the snapshot's index and the fold of `D` (`StepR.applySnap`). -/
private theorem wp_step_snapack
    (wp_raft_Step : raft.Step.spec (GF := GF) (hG := hG))
    (γ : RaftNames) (md : GMode) (c : CfgM) (r : Loc) (id : w64) (s : NState)
    (ml : Loc) (t : w64) (b : entryID) (e : Option entryID) (sv : SnapshotM) (D : List EntryM)
    (Hwf : NStateWf s) (Hok : PendingOk s (.appendAck t b e (some sv))) (Hal : c.autoLeave = false)
    (Hhit : snapHit s.logst.snap sv.Metadata'.Index' = s.logst.sat)
    (Hle : uint.Z sv.Metadata'.Index' ≤ uint.Z s.logst.prev.index')
    (Hsok : ∀ x, e = some x → (t = W64 0 ∨ t = s.term) → StableOk (ackLog s.logst (some sv)) x)
    (Hghoff : s.gh.unst = false)
    -- (D22 S-d4 item 3) the storage's extent (`SnpExt`) and the snapshot handed out
    (Hsxp : s.logst.snap ≠ none → s.logst.lent = false →
      uint.Z sv.Metadata'.Index' ≤ uint.Z s.logst.sxt)
    (Hkxp : ∀ k, s.gh.snp = some k → uint.Z k.sid.index' ≤ uint.Z sv.Metadata'.Index')
    -- (U0) the configuration's switch: a follower, the snapshot handed out, naming a node
    (Hrole : s.role = .follower) (Hpnd : s.logst.snap ≠ none)
    (Hsnp0 : s.gh.snp = some (snapTrip sv sv.Metadata'.ConfState'.lists))
    (Hhas : ∃ x, sv.Metadata'.ConfState'.lists.Has x)
    -- (U3c) dynamically: `applied` below the snapshot's index, the snapshot at the boundary with
    -- nothing else pending, the committed log `D` up to it ending at its id, and its `ConfState` no
    -- auto-leave one
    (Hdyn : md.isDyn = true →
      uint.Z s.logst.applied < uint.Z sv.Metadata'.Index' ∧
      (s.logst.snap = none ∨ snapHit s.logst.snap sv.Metadata'.Index' = true →
        sv.Metadata'.Index' = s.logst.prev.index') ∧
      D.length = uint.nat sv.Metadata'.Index' ∧ plogLast base0 D = snapId sv ∧
      uint.Z sv.Metadata'.Index' ≤ uint.Z s.logst.committed ∧
      sv.Metadata'.ConfState'.AutoLeave' = false) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhysCV c c.voters r id s ∗
        ownStepGhost γ md c id s ∗
        msgIn ml DFrac.discard ⟨appendAckM id t (e.getD ⟨W64 0, W64 0⟩), [], some sv, [], []⟩ ∗
        £ 1 ∗ isCommitted γ D }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #ml))
    {{ (err : GoInterface) (s' : NState) (md' : GMode), RET #err;
        ownRaftPhysCV (snapCfg sv sv.Metadata'.ConfState'.lists)
          (snapCfg sv sv.Metadata'.ConfState'.lists).voters r id s' ∗
        ownStepGhost γ md' (snapCfg sv sv.Metadata'.ConfState'.lists) id s' ∗
        ⌜NStateWf s' ∧ (md = .static → md' = .static) ∧
         (∀ dec c0 h0 g, md = .dyn dec c0 h0 g →
            md' = .dyn dec c0 h0
              ⟨uint.nat sv.Metadata'.Index', (cfgFold dec c0 D).getD g.cfg, g.fp, g.decs⟩) ∧
         (snapCfg sv sv.Metadata'.ConfState'.lists).autoLeave = false ∧
         ∃ (prs : GMap w64 Loc) (pvs : GMap w64 Progress) (il : Bool), s' = { s with
           logst := ackSnapLog s.logst (appendAckM id t (e.getD ⟨W64 0, W64 0⟩)) s.term sv,
           progress := prs, prvals := pvs, isLearner := il }⌝ }} := by
  iintro %Φ ⟨#Hinit, Hphys, Hghost, Hmin, Hlc, #HD⟩ HΦ
  imod rdCred_zero_upd (GF := GF) γ with Hcr
  obtain ⟨Hle0, -⟩ := Hok
  -- (U0) the snapshot's certificate: in `ksn`, registered in the storage's registry
  icases ownRaftPhysC_gh c r id s $$ Hphys with ⟨%Hgh, Hphys⟩
  have Hk : snapTrip sv sv.Metadata'.ConfState'.lists ∈ s.logst.ksn := (Hgh.1.2.2.1 _ Hsnp0).2.1
  icases ownRaftPhysC_log_same c r id s $$ Hphys with ⟨Hlog, Hlogback⟩
  icases ownRaftLog_kcert _ _ $$ Hlog with ⟨#Hkc, Hlog⟩
  ihave Hphys := Hlogback $$ Hlog
  ihave ⟨#Hsc, -⟩ := BigSepL.bigSepL_mem_acc Hk $$ Hkc
  icases ownRaftPhysC_ns c r id s $$ Hphys with ⟨%Hnsl, -, Hphys⟩
  iunfold ownStepGhost at Hghost
  icases Hghost with ⟨Hg, Hrest⟩
  iunfold ghostRest at Hrest
  icases Hrest with ⟨%Hnlk, Hrm, #Hlink⟩
  ihave #Hlink' := Hlink
  iunfold certLink at Hlink'
  icases Hlink' with (%Hns | #Hok')
  · exfalso; exact Hpnd (Hnsl (by rw [Hnlk.1]; exact Hns)).1
  iunfold storCertOk at Hok'
  icases Hok' with ⟨#Hreg, -⟩
  imod Hreg $$ %_ %⊤ %CoPset.subseteq_top Hsc with #HcrD
  iunfold raftSnapCertD at HcrD
  icases HcrD with ⟨#Hcr, -⟩
  iunfold raftSnapCert at Hcr
  icases Hcr with ⟨%Hl, %Hst, #Hdc, -⟩
  obtain ⟨x, Hx⟩ := Hhas
  have Hsok' : (appendAckM id t (e.getD ⟨W64 0, W64 0⟩)).Term' = W64 0 ∨
      (appendAckM id t (e.getD ⟨W64 0, W64 0⟩)).Term' = s.term →
      (appendAckM id t (e.getD ⟨W64 0, W64 0⟩)).Index' ≠ W64 0 →
      StableOk (ackLog s.logst (some sv))
        ⟨(appendAckM id t (e.getD ⟨W64 0, W64 0⟩)).LogTerm',
          (appendAckM id t (e.getD ⟨W64 0, W64 0⟩)).Index'⟩ := by
    intro ht hi
    cases e with
    | none => exact absurd rfl hi
    | some x => exact Hsok x rfl ht
  -- the mode's acknowledgement premise and the configuration's auto-leave flag, with the ghost
  -- state closed again; dynamically `D` the full prefix up to the snapshot, its fold some
  ihave ⟨%Hmode, %Hal', %HcsD, Hghost⟩ : ⌜(md.isDyn = false ∧ SnapAckOk γ id sv) ∨ SnapAckDyn md s sv⌝ ∗
      ⌜(snapCfg sv sv.Metadata'.ConfState'.lists).autoLeave = false⌝ ∗
      ⌜∀ dec c0 h0 g, md = .dyn dec c0 h0 g →
        g.fp.take (uint.nat sv.Metadata'.Index') = D ∧ (cfgFold dec c0 D).isSome⌝ ∗
      ownStepGhost γ md c id s $$ [Hg Hrm]
  · cases md with
    | static =>
      ihave %HC : ⌜CfgStatic γ c ∧ TrackedOk γ c id⌝ $$ [Hrm]
      · simp only [ghostRestM]; iexact Hrm
      have Hdyn0 : γ.reDyn = none := HC.1.2.2
      obtain ⟨Hvs, Hout, Htr⟩ := Hst Hdyn0 x Hx
      have Hout' : sv.Metadata'.ConfState'.lists.outgoing = [] := Hout
      isplitr
      · ipureintro
        refine .inl ⟨rfl, Hl x Hx, ⟨?_, ?_, Hdyn0⟩, fun T hT => ⟨Htr T hT, (HC.2 T hT).2⟩⟩
        · exact Hvs
        · show GMap.listToSet sv.Metadata'.ConfState'.lists.outgoing = ∅
          rw [Hout']; rfl
      isplitr
      · ipureintro; simp only [snapCfg, csCfgM, Hout', ↓reduceIte]
      isplitr
      · ipureintro; intro _ _ _ _ h; cases h
      unfold ownStepGhost ghostRest
      iframe Hg Hlink
      isplitr
      · ipureintro; exact Hnlk
      simp only [ghostRestM]; ipureintro; exact HC
    | dyn dec c0 h0 g =>
      obtain ⟨Hlt, Hsnb, Hdl, Hdlast, Hic, Half⟩ := Hdyn rfl
      simp only [ghostRestM]
      icases Hrm with ⟨%Hdgc, #HMg, #Hfr, Hcamp⟩
      obtain ⟨HDy, hc, HI⟩ := Hdgc
      ihave Hghost : ownStepGhost γ (.dyn dec c0 h0 g) c id s $$ [Hg Hcamp]
      · unfold ownStepGhost ghostRest
        iframe Hg Hlink
        isplitr
        · ipureintro; exact Hnlk
        simp only [ghostRestM]
        iframe Hfr Hcamp HMg
        ipureintro; exact ⟨HDy, hc, HI⟩
      -- `D`, committed and no longer than the commit index, is the full prefix up to the index
      icases ownStepGhost_deliv γ dec c0 h0 g c id s D
          (by rw [Hdl]; have := uint_nat_eq sv.Metadata'.Index'; omega) $$ HD Hghost
        with ⟨%Hpre, Hghost⟩
      have Hfl : (g.fp.length : Int) = uint.Z s.logst.prev.index' := HI.full.1
      have HlenD : D.length ≤ g.fp.length := by
        have := uint_nat_eq sv.Metadata'.Index'; omega
      have Hpfx : D <+: g.fp :=
        List.prefix_of_prefix_length_le Hpre (List.prefix_append _ _) HlenD
      have Htake : g.fp.take (uint.nat sv.Metadata'.Index') = D := by
        rw [← Hdl]; exact (List.prefix_iff_eq_take.1 Hpfx).symm
      have HfD : FullOk (snapId sv) D :=
        ⟨by rw [Hdl]; simp only [snapId]; first | (have := uint_nat_eq sv.Metadata'.Index'; omega) | skip,
          PlogWf_prefix base0 D g.fp Hpfx HI.full.2.1, Hdlast⟩
      ihave #HrD : logRecs γ base0 D $$ []
      · rw [← Htake]; iapply logRecs_take $$ Hfr
      ihave %Hfold := Hdc $$ %x %Hx %_ %HDy %D HrD %HfD
      simp only [DynCfg.ofFold, effDec_empty] at Hfold
      obtain ⟨cs', Hcs1, Hcs2⟩ := Option.map_eq_some_iff.1 Hfold
      isplitr
      · ipureintro
        exact .inr ⟨Hl x Hx, Hlt, Hsnb, cs', by
          rw [Htake]; exact cfgFold_mono (effDec_base dec g.decs) Hcs1, Hcs2⟩
      isplitr
      · ipureintro; simp only [snapCfg, csCfgM, Half]; split <;> rfl
      isplitr
      · ipureintro; intro _ _ _ _ h; cases h; exact ⟨Htake, by rw [Hcs1]; rfl⟩
      iexact Hghost
  have Hsnp : ∀ sv', some sv = some sv' →
      snapHit s.logst.snap sv'.Metadata'.Index' = s.logst.sat ∧
      uint.Z sv'.Metadata'.Index' ≤ uint.Z s.logst.prev.index' ∧
      s.role = .follower ∧
        ((md.isDyn = false ∧ SnapAckOk γ id sv') ∨ SnapAckDyn md s sv') ∧
      (s.logst.snap ≠ none → s.logst.lent = false →
        uint.Z sv'.Metadata'.Index' ≤ uint.Z s.logst.sxt) ∧
      (∀ k, s.gh.snp = some k → uint.Z k.sid.index' ≤ uint.Z sv'.Metadata'.Index') := by
    intro sv' hsv
    cases hsv
    exact ⟨Hhit, Hle, Hrole, Hmode, Hsxp, Hkxp⟩
  -- the mode's premise: nothing asked of a storage acknowledgement but the guard (a follower's)
  have Hgd : md.Pre (appendAckM id t (e.getD ⟨W64 0, W64 0⟩)) [] s := by
    cases md with
    | static => trivial
    | dyn dec c0 h0 g =>
      refine ⟨fun _ hr => absurd (hr.symm.trans Hrole) (by decide), fun h => absurd h (by msg_ne),
        fun h => absurd h (by msg_ne)⟩
  iapply wp_raft_Step c md γ r id s ml (appendAckM id t (e.getD ⟨W64 0, W64 0⟩)) [] [] (some sv) []
    (by simp [StepMsg, stepMsgTypes, appendAckM])
    (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne)
    (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne)
    (fun _ => ⟨Hsnp, Hle0, Hsok', Hghoff⟩) (by msg_ne) (by msg_ne) (by msg_ne)
    (by msg_ne)
    (RestMsgOk.of_ne ⟨by msg_ne, by msg_ne, by msg_ne, by msg_ne, by msg_ne⟩) Hwf
    Hgd (fun h => absurd h (by msg_ne))
    $$ [$Hinit $Hphys $Hghost $Hlc Hmin Hcr]
  · have hP : (appendAckM id t (e.getD ⟨W64 0, W64 0⟩)).Type' ≠ MsgProp := by msg_ne
    simp only [hP, ↓reduceIte, named]
    have Hty0 : mtypeOf (appendAckM id t (e.getD ⟨W64 0, W64 0⟩)).Type' = none := rfl
    isplitl [Hmin]
    · isplitl [Hmin]
      · iexact Hmin
      isplitr
      · iempintro
      isplitr
      · ipureintro; msg_ne
      isplitr
      · ipureintro; msg_ne
      isplitr
      · ipureintro; msg_ne
      imodintro
      iintro %ty %Hty
      rw [Hty0] at Hty
      cases Hty
    isplitl [Hcr]
    · simp [appendAckM, MsgStorageAppendResp, MsgReadIndex]; iexact Hcr
    imodintro
    iintro %Hc
    exfalso
    revert Hc
    msg_ne
  · inext
    iintro %err %s' %c' %md' ⟨Hphys, Hghost, %Hwf', %Hstp, %Hcc, %Hloc, -, %Hterm, -⟩
    obtain ⟨Hc', Hs', Hmd'⟩ := Hloc.2 rfl sv rfl
    subst Hc'
    -- dynamically the configuration afterwards the fold of `D` (`RInv.cfg` at the new index)
    ihave ⟨%Hmd2, Hghost⟩ : ⌜∀ dec c0 h0 g, md = .dyn dec c0 h0 g →
        md' = .dyn dec c0 h0
          ⟨uint.nat sv.Metadata'.Index', (cfgFold dec c0 D).getD g.cfg, g.fp, g.decs⟩⌝ ∗
        ownStepGhost γ md' (snapCfg sv sv.Metadata'.ConfState'.lists) id s' $$ [Hghost]
    · cases md with
      | static => iframe Hghost; ipureintro; intro _ _ _ _ h; cases h
      | dyn dec c0 h0 g =>
        obtain ⟨cs'', rfl⟩ := Hmd' dec c0 h0 g rfl
        icases ownStepGhost_rinv γ dec c0 h0 _ _ id s' $$ Hghost with ⟨%HI', Hghost⟩
        iframe Hghost
        ipureintro
        intro _ _ _ _ h
        cases h
        obtain ⟨Htake, -⟩ := HcsD dec c0 h0 g rfl
        have Hdl := (Hdyn rfl).2.2.1
        have Hcf := HI'.cfg
        have Hle' : uint.nat sv.Metadata'.Index' ≤ g.fp.length := by
          have h2 := congrArg List.length Htake
          rw [List.length_take, Hdl] at h2; omega
        have Hfull : (g.fp ++ (toPState s').log).take (uint.nat sv.Metadata'.Index') = D := by
          rw [List.take_append_of_le_length Hle']; exact Htake
        have Hcf' : cfgFold dec c0 D = some cs'' := by
          obtain ⟨-, Hsome⟩ := HcsD dec c0 h0 g rfl
          obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 Hsome
          have h2 := cfgFold_mono (effDec_base dec g.decs) hx
          rw [← Hfull] at h2
          rw [show (cfgFold (effDec dec g.decs) c0 ((g.fp ++ (toPState s').log).take
            (uint.nat sv.Metadata'.Index'))) = some cs'' from Hcf] at h2
          rw [hx, Option.some.inj h2]
        rw [Hcf']; rfl
    iapply HΦ $$ %err %s' %md'
    iframe Hphys Hghost
    ipureintro
    exact ⟨Hwf', fun h => by subst h; exact Hstp.1, Hmd2, Hal', Hs'⟩

/-- (D22 S-d3a) What a snapshot's acknowledgement leaves of the log (`ackSnapLog`), the snapshot the
pending one, `applying` at most its index, `applied` at most `applying`: the snapshot dropped, nothing
in progress or absorbed, `applied` and `applying` at its index, the rest kept. -/
theorem ackSnapLog_facts (ls : LogState) (m : MessageM) (t : w64) (sv : SnapshotM)
    (Hsn : ls.snap = some (snapId sv))
    (Hap : uint.Z ls.applying ≤ uint.Z sv.Metadata'.Index')
    (Happ : uint.Z ls.applied ≤ uint.Z ls.applying) :
    (ackSnapLog ls m t sv).snap = none ∧ (ackSnapLog ls m t sv).sip = false ∧
    (ackSnapLog ls m t sv).sat = false ∧
    (ackSnapLog ls m t sv).applying = sv.Metadata'.Index' ∧
    (ackSnapLog ls m t sv).applied = sv.Metadata'.Index' ∧
    (ackSnapLog ls m t sv).unpersisted = ls.unpersisted ∧
    (ackSnapLog ls m t sv).prev = ls.prev ∧ logStoreRec (ackSnapLog ls m t sv) = logStoreRec ls ∧
    (ackSnapLog ls m t sv).storage = ls.storage ∧ (ackSnapLog ls m t sv).fl = ls.fl ∧
    (ackSnapLog ls m t sv).committed = ls.committed ∧ (ackSnapLog ls m t sv).lent = ls.lent := by
  -- after the window and `stableTo` (if called), every field kept but the stable part: then
  -- `stableSnapTo` hits and `appliedTo` moves both to the snapshot's index
  have key : ∀ ls1 : LogState, ls1.snap = ls.snap → ls1.applying = ls.applying →
      ls1.applied = ls.applied → ls1.unpersisted = ls.unpersisted → ls1.prev = ls.prev →
      logStoreRec ls1 = logStoreRec ls → ls1.storage = ls.storage → ls1.fl = ls.fl →
      ls1.committed = ls.committed → ls1.lent = ls.lent →
      let ls2 := logAppliedTo (logStableSnap ls1 sv.Metadata'.Index') sv.Metadata'.Index' (W64 0)
      ls2.snap = none ∧ ls2.sip = false ∧ ls2.sat = false ∧
      ls2.applying = sv.Metadata'.Index' ∧ ls2.applied = sv.Metadata'.Index' ∧
      ls2.unpersisted = ls.unpersisted ∧ ls2.prev = ls.prev ∧ logStoreRec ls2 = logStoreRec ls ∧
      ls2.storage = ls.storage ∧ ls2.fl = ls.fl ∧ ls2.committed = ls.committed ∧
      ls2.lent = ls.lent := by
    intro ls1 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    have Hhit : snapHit ls1.snap sv.Metadata'.Index' = true := by
      rw [h1, Hsn]; simp [snapHit, snapId]
    have Hs2 : logStableSnap ls1 sv.Metadata'.Index' =
        { ls1 with snap := none, sip := false, sapp := false, aps := true, sat := false } := by
      unfold logStableSnap; rw [if_pos Hhit]
    rw [Hs2]
    have Hmax1 : w64Max sv.Metadata'.Index' ls1.applied = sv.Metadata'.Index' := by
      apply uint_Z_inj.1
      rw [w64Max_spec, h3]; omega
    have Hmax2 : w64Max ls1.applying sv.Metadata'.Index' = sv.Metadata'.Index' := by
      apply uint_Z_inj.1
      rw [w64Max_spec, h2]; omega
    simp only [logAppliedTo, Hmax1, Hmax2]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | trivial | assumption | rfl
  have Ha : (ackLog ls (some sv)).snap = ls.snap ∧ (ackLog ls (some sv)).applying = ls.applying ∧
      (ackLog ls (some sv)).applied = ls.applied ∧
      (ackLog ls (some sv)).unpersisted = ls.unpersisted ∧ (ackLog ls (some sv)).prev = ls.prev ∧
      logStoreRec (ackLog ls (some sv)) = logStoreRec ls ∧ (ackLog ls (some sv)).storage = ls.storage ∧
      (ackLog ls (some sv)).fl = ls.fl ∧ (ackLog ls (some sv)).committed = ls.committed ∧
      (ackLog ls (some sv)).lent = ls.lent := by
    unfold ackLog
    by_cases h : ls.sat = true
    · rw [if_pos h]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · rw [if_neg h]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := Ha
  unfold ackSnapLog
  cases hst : ackStableId m t with
  | none => exact key _ a1 a2 a3 a4 a5 a6 a7 a8 a9 a10
  | some id =>
    have Hc : (logStableTo (ackLog ls (some sv)) id).snap = ls.snap ∧
        (logStableTo (ackLog ls (some sv)) id).applying = ls.applying ∧
        (logStableTo (ackLog ls (some sv)) id).applied = ls.applied ∧
        (logStableTo (ackLog ls (some sv)) id).unpersisted = ls.unpersisted ∧
        (logStableTo (ackLog ls (some sv)) id).prev = ls.prev ∧
        logStoreRec (logStableTo (ackLog ls (some sv)) id) = logStoreRec ls ∧
        (logStableTo (ackLog ls (some sv)) id).storage = ls.storage ∧
        (logStableTo (ackLog ls (some sv)) id).fl = ls.fl ∧
        (logStableTo (ackLog ls (some sv)) id).committed = ls.committed ∧
        (logStableTo (ackLog ls (some sv)) id).lent = ls.lent := by
      unfold logStableTo
      by_cases hh : StableHit (ackLog ls (some sv)) id
      · rw [if_pos hh]; exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩
      · rw [if_neg hh]; exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩ := Hc
    exact key _ c1 c2 c3 c4 c5 c6 c7 c8 c9 c10

/-- The bounds of `stepsOnAdvance[:0]`, from the slice's own (`word` alone, out of the proof's
context, which is too large for its time bound). -/
private theorem slice00_ok {l c : w64} (h : 0 ≤ sint.Z l ∧ sint.Z l ≤ sint.Z c) :
    (0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z c) ∧
    (0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z l) := by
  word

/-- The loop's counter at its end: the slice's length. -/
private theorem loop_done_nat {n len : w64} {k : Nat} (h1 : ¬ sint.Z n < sint.Z len)
    (h2 : 0 ≤ sint.Z n ∧ sint.Z n ≤ (k : Int)) (h3 : k = sint.nat len) (h4 : 0 ≤ sint.Z len) :
    sint.nat n = k := by
  word

/-- (D22 S-d3b, 2026-10-21) **After a restore, the acknowledgement misses** (`stableHit_miss`): the
records of what the storage holds after the `Ready`'s boundary `b` and of the log, at the restored
boundary, without its entry in what the storage holds (`ackBaseW`). -/
private theorem stableHit_restored (γ : RaftNames) (id : w64) (s : NState) {md : Bool}
    (b : entryID) (Hbp : uint.Z b.index' < uint.Z s.logst.prev.index')
    (Hnb : plogTermAt b s.logst.stored s.logst.prev.index' ≠ some s.logst.prev.term') :
    ⊢ storedRecs γ b s.logst.stored -∗ ownRaftGhost (GF := GF) γ id (toPState s) md -∗
      ⌜¬ StableHit s.logst (plogLast b s.logst.stored)⌝ ∗ ownRaftGhost γ id (toPState s) md := by
  iintro #Hst Hg
  icases ownRaftGhost_storedRecs_keep γ id (toPState s) $$ Hg with ⟨Hg, #Hlr⟩
  unfold storedRecs
  icases Hst with ⟨%HwL, #HrL⟩
  icases Hlr with ⟨%HwF, #HrF⟩
  icases logRecs_agree γ _ _ _ _ $$ HrL HrF with %HRA
  iframe Hg
  ipureintro
  exact stableHit_miss HwL HwF HRA Hbp Hnb

/-- (2026-10-26, D22 J2) A snapshot's acknowledgement keeps the pending snapshot or clears it
(`logStableSnap`): what keeps its receiver-local fact (`snapLocOk_keep`). -/
theorem ackSnapLog_snap (ls : LogState) (m : MessageM) (t : w64) (sv : SnapshotM) :
    (ackSnapLog ls m t sv).snap = ls.snap ∨ (ackSnapLog ls m t sv).snap = none := by
  have hl : (ackLog ls (some sv)).snap = ls.snap := by
    simp only [ackLog]; split <;> rfl
  have hA : (match ackStableId m t with
       | some id => logStableTo (ackLog ls (some sv)) id
       | none => ackLog ls (some sv)).snap = ls.snap := by
    split
    · unfold logStableTo; split <;> exact hl
    · exact hl
  have key : ∀ X : LogState, X.snap = ls.snap →
      (logAppliedTo (logStableSnap X sv.Metadata'.Index') sv.Metadata'.Index' (W64 0)).snap = ls.snap ∨
      (logAppliedTo (logStableSnap X sv.Metadata'.Index') sv.Metadata'.Index' (W64 0)).snap = none := by
    intro X hX
    show (logStableSnap X _).snap = _ ∨ (logStableSnap X _).snap = none
    unfold logStableSnap
    split
    · exact .inr rfl
    · exact .inl hX
  unfold ackSnapLog
  exact key _ hA

/-- (D22 S-d3b) What a snapshot's acknowledgement leaves of the log after a restore (`ackSnapLog`):
the restored snapshot still pending (`stableSnapTo` misses), the `stableTo` missed (`Hmiss`),
`applied` and `applying` at the acknowledged snapshot's index, the rest kept. -/
theorem ackSnapLog_facts_miss (ls : LogState) (m : MessageM) (t : w64) (sv : SnapshotM)
    (Hhit : snapHit ls.snap sv.Metadata'.Index' = false) (Hsat : ls.sat = false)
    (Hmiss : ∀ id', ackStableId m t = some id' → ¬ StableHit ls id')
    (Hap : uint.Z ls.applying ≤ uint.Z sv.Metadata'.Index')
    (Happ : uint.Z ls.applied ≤ uint.Z ls.applying) :
    (ackSnapLog ls m t sv).snap = ls.snap ∧ (ackSnapLog ls m t sv).sip = ls.sip ∧
    (ackSnapLog ls m t sv).sat = false ∧
    (ackSnapLog ls m t sv).applying = sv.Metadata'.Index' ∧
    (ackSnapLog ls m t sv).applied = sv.Metadata'.Index' ∧
    (ackSnapLog ls m t sv).unpersisted = ls.unpersisted ∧
    (ackSnapLog ls m t sv).prev = ls.prev ∧ logStoreRec (ackSnapLog ls m t sv) = logStoreRec ls ∧
    (ackSnapLog ls m t sv).storage = ls.storage ∧ (ackSnapLog ls m t sv).fl = ls.fl ∧
    (ackSnapLog ls m t sv).committed = ls.committed ∧ (ackSnapLog ls m t sv).lent = ls.lent := by
  have Hak : ackLog ls (some sv) = ls := by simp [ackLog, Hsat]
  have Hmid : ackSnapLog ls m t sv = logAppliedTo ls sv.Metadata'.Index' (W64 0) := by
    unfold ackSnapLog
    cases hst : ackStableId m t with
    | none =>
      simp only [Hak]
      rw [logStableSnap_miss ls _ Hhit]
    | some id =>
      simp only [Hak]
      unfold logStableTo
      rw [if_neg (Hmiss id hst), logStableSnap_miss ls _ Hhit]
  rw [Hmid]
  have Hmax1 : w64Max sv.Metadata'.Index' ls.applied = sv.Metadata'.Index' := by
    apply uint_Z_inj.1
    rw [w64Max_spec]; omega
  have Hmax2 : w64Max ls.applying sv.Metadata'.Index' = sv.Metadata'.Index' := by
    apply uint_Z_inj.1
    rw [w64Max_spec]; omega
  simp only [logAppliedTo, Hmax1, Hmax2, Hsat]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial

private theorem advRS_some {rs : RNState} (t : w64) (ca : Nat) {l : SnapLoan} (h : rs.slent = some l) :
    advRS rs t ca = { rs with steps := [], term := t, capplied := ca, flw := false, slent := none,
                              unpersisted := [], delivered := l.dlv,
                              cfg := rs.mode.foldCfg l.dlv rs.cfg } := by
  unfold advRS; rw [h]

/-- (2026-10-28, stage U3c) A follower's campaign guard holds (it is a pre-candidate's). -/
private theorem preGuardF_of_fol {fp : List EntryM} {s : NState} (h : s.role = .follower) :
    PreGuardF fp s :=
  fun _ hr => absurd (h.symm.trans hr) (by decide)

/-- (2026-10-28, stage U3c) The mode after a snapshot's acknowledgement (`wp_step_snapack`'s post), at
the `RawNode`'s level: the snapshot's index and the fold of the committed log up to it. -/
private theorem snapack_mode {mode : RNMode} {ca j : Nat} {cfg : CCState} {fp D : List EntryM}
    {ds : DecMap} {md' : GMode}
    (h1 : mode.toG ⟨ca, cfg, fp, ds⟩ = .static → md' = .static)
    (h2 : ∀ dec c0 h0 g, mode.toG ⟨ca, cfg, fp, ds⟩ = .dyn dec c0 h0 g →
      md' = .dyn dec c0 h0 ⟨j, (cfgFold dec c0 D).getD g.cfg, g.fp, g.decs⟩) :
    md' = mode.toG ⟨j, mode.foldCfg D cfg, fp, ds⟩ := by
  cases mode with
  | static => exact h1 rfl
  | dyn dec c0 h0 _ => exact h2 dec c0 h0 _ rfl

/-- In the static mode the ghost part is irrelevant. -/
private theorem RNMode.toG_static {mode : RNMode} (h : mode.isDyn = false) (g g' : RGh) :
    mode.toG g = mode.toG g' := by
  cases mode with
  | static => rfl
  | dyn => cases h

theorem RawNode.Advance.wp_proof
    (wp_raft_Step : raft.Step.spec (GF := GF) (hG := hG)) :
    RawNode.Advance.spec (GF := GF) (hG := hG) := by
  intro γ rn id rs rd Hunp0 Hunst0 Ha1 Hal1
  wp_start as H
  iNamed H
  iNamed Hrn
  have Htcb : uint.Z s.gh.tc < 2 ^ 64 := by word
  rcases Option.eq_none_or_eq_some rs.slent with hsl | ⟨l, hsl⟩
  rotate_left
  · -- (D22 S-d3a) **after a snapshot `Ready`**: the application's receipt back, absorbed; the queue
    -- is the node's own responses, then the snapshot's acknowledgement
    obtain ⟨Hsnp, Hss, Hcm0, Hfl0, Hstu, Haplt, Hdlp, Hdll, pre, tA, eA, Hsteq, Hpre⟩ :=
      Hloan.2.2 l hsl
    have Hapl := Int.le_of_lt Haplt
    -- (D22 S-d3b) the lent snapshot pending, or a later one restored past it (`LoanOk`)
    have Hsnn : s.logst.snap ≠ none := by rcases Hss with h | ⟨_, h, -⟩ <;> rw [h] <;> simp
    have Hunst : s.gh.unst = false := by rw [← Hrs_unst]; exact Hunst0
    ihave #Hdlh : iprop(isCommitted γ l.dlv ∗ ⌜(∃ x, l.snap.Metadata'.ConfState'.lists.Has x) ∧
        plogLast base0 l.dlv = snapId l.snap⌝)
      $$ [Hloanc]
    · iExactEq Hloanc; unfold loanCom; rw [hsl]
    icases Hdlh with ⟨#Hdl, %Hhas0⟩
    obtain ⟨Hhas, Hdlast⟩ := Hhas0
    -- the receipt: the application's half of the snapshot, and the storage at the snapshot
    ihave Hret : snapReceipt rs.storage l rs.unpersisted $$ [Hret]
    · iExactEq Hret; unfold loanRet; rw [hsl]
    unfold snapReceipt
    icases Hret with ⟨Hsv2, %σr, HSt, %Hσr⟩
    ihave Hpend : iprop(ownSnapM l.ptr (DFrac.own (1 : Qp).half) l.snap ∗
        (ownSnapM l.ptr (DFrac.own 1) l.snap -∗ pendList γ id steps rs.steps)) $$ [Hpend]
    · iExactEq Hpend; unfold lentPend; rw [hsl]
    icases Hpend with ⟨Hsv1, Hpw⟩
    ihave Hsv := ownSnapM_combine l.ptr _ _ l.snap $$ [Hsv1 Hsv2]
    · iframe Hsv1 Hsv2
    ihave Hsv : ownSnapM l.ptr (DFrac.own 1) l.snap $$ [Hsv]
    · rw [← dfrac_half_half]; iexact Hsv
    ihave Hpend := Hpw $$ Hsv
    -- the log's facts at the snapshot: the boundary, the floor
    icases ownRaftPhysC_log_same cf rnv.raft' id s $$ Hphys with ⟨Hlog0, Hback0⟩
    icases ownRaftLog_snap_facts _ _ $$ Hlog0 with ⟨%Hsf0, Hlog0⟩
    icases ownRaftLog_fl _ _ $$ Hlog0 with ⟨%Hflb0, Hlog0⟩
    ihave Hphys := Hback0 $$ Hlog0
    have Hpvs : ∀ sp, s.logst.snap = some sp → s.logst.prev = sp := fun sp h => (Hsf0.2.2.2 _ h).1
    -- the storage back: absorbed, the log at the snapshot (`sat`), the mirror's lent flag down
    obtain ⟨Hr1, Hr2, Hr3, Hr4, Hr5, Hr6, Hr7, Hr8⟩ := Hσr
    icases ownRaftPhysC_log_at_snp cf rnv.raft' id s $$ Hphys with ⟨Hlog, %Hgh0, Hback⟩
    have Hlt : s.logst.lent = true := by
      rw [Hgh0.1.2.1, Hloan.1, hsl]; rfl
    have Hk : σr.ss.index' ≠ W64 0 → SnapTrip.mk σr.ss σr.scs σr.sal σr.sdat ∈ s.logst.ksn := by
      intro _
      have := (Hgh0.1.2.2.1 _ Hsnp).2.1
      rw [Hr2, Hr6, Hr7, Hr8]; exact this
    ihave HSt : ownStorage s.logst.storage σr $$ [HSt]
    · rw [← Hstor]; iexact HSt
    ihave Hlog := ownRaftLog_absorb_snap s.log s.logst σr Hlt
      ⟨Hr1.trans Hr2.symm, by rw [Hr3, Hunp, Hstu], Hr4, Hr5.trans Hfl0⟩ Hk
      (by rw [Hr1]; exact Hapl) $$ Hlog HSt
    have HghN : LogGhOk { s with gh := { s.gh with slent := false, snp := s.gh.snp } }
        (logAbsorbSnap s.logst σr.ss) := by
      refine ⟨⟨fun _ => .inr Hsnn, rfl,
          fun k hk => ?_, fun _ => by show s.gh.snp ≠ none; rw [Hsnp]; simp, fun h => ?_,
          fun k hk _ => ⟨fun _ => ?_, fun h => absurd h Hsnn⟩⟩,
        fun _ => ⟨rfl, rfl, rfl, Int.le_refl _⟩, rfl⟩
      rotate_right
      · -- (D22 S-d4 item 3) the storage at the snapshot handed out (`sxt`)
        have hk' : s.gh.snp = some k := hk
        rw [Hsnp] at hk'; cases hk'
        show uint.Z (snapId l.snap).index' ≤ uint.Z σr.ss.index'
        rw [Hr2]; exact Int.le_refl _
      · obtain ⟨a, b, c⟩ := Hgh0.1.2.2.1 k hk
        refine ⟨fun h => ⟨(a h).1, .inr ((logAbsorbSnap_sat s.logst σr.ss).2 ⟨?_, (a h).1⟩)⟩, b, c⟩
        rw [Hsnp] at hk; cases hk
        show s.logst.snap = some σr.ss
        rw [Hr2]; exact h
      · -- (D22 S-d3b) the storage at the pending snapshot only for the lent one
        rcases h with h | h
        · exact Hgh0.1.2.2.2.2.1 (.inl h)
        · obtain ⟨Hs, -⟩ := (logAbsorbSnap_sat s.logst σr.ss).1 h
          exact ⟨_, Hsnp, by show s.logst.snap = _; rw [Hs, Hr2]; rfl⟩
    ihave Hphys := Hback $$ %(logAbsorbSnap s.logst σr.ss) %false %s.gh.snp Hlog %HghN
      %(fun _ => Int.le_refl _)
    generalize Hs0 : ({ s with
        logst := logAbsorbSnap s.logst σr.ss
        gh := { s.gh with slent := false, snp := s.gh.snp } } : NState) = s0
    have Hs0f : s0.logst.applying = s.logst.applying ∧ s0.logst.unpersisted = [] ∧
        s0.logst.snap = s.logst.snap ∧ s0.logst.prev = s.logst.prev ∧
        s0.logst.stored = s.logst.stored ∧ s0.logst.storage = s.logst.storage ∧
        s0.prevote = s.prevote ∧ s0.logst.committed = s.logst.committed ∧
        s0.logst.fl = s.logst.fl ∧ s0.logst.applied = s.logst.applied ∧ s0.term = s.term ∧
        s0.role = s.role ∧ s0.gh.tc = s.gh.tc ∧ s0.gh.unst = s.gh.unst ∧
        s0.gh.outlb = s.gh.outlb ∧ s0.gh.snp = s.gh.snp ∧ s0.gh.slent = false := by
      rw [← Hs0]
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    -- (2026-10-28, stage U4a) the storage at the snapshot: no record of its terms after it
    have Hsd0 : s0.logst.sdt = [] := by rw [← Hs0]; rfl
    ihave Hghost := ownStepGhost_congr γ (rs.mode.toG ⟨rs.capplied, rs.cfg, fp, ds⟩) cf id (s := s) (s' := s0)
      (by rw [← Hs0] <;> rfl) (by rw [← Hs0] <;> rfl) (by rw [← Hs0] <;> rfl) (by rw [← Hs0] <;> rfl) (by rw [← Hs0] <;> rfl)
      (by rw [← Hs0] <;> rfl) (by rw [← Hs0] <;> rfl) (by rw [← Hs0] <;> rfl) $$ Hghost
    have Hwf0 : NStateWf s0 := by rw [← Hs0]; exact Hwf
    have Hstok0 : StepsOk s0 rs.steps :=
      stepsOk_mono s s0 rs.steps Hs0f.2.2.2.2.2.2.2.2.2.2.1
        ⟨Hs0f.2.2.2.1, Hs0f.2.2.2.2.1⟩ (by rw [Hs0f.2.2.2.2.2.2.2.1]; exact Int.le_refl _)
        Hs0f.1 (by rw [Hs0f.2.2.2.2.2.2.2.2.2.2.2.2.1]; exact Int.le_refl _) Hstok
    have Htrm0 : rs.term = s0.term := Htrm.trans Hs0f.2.2.2.2.2.2.2.2.2.2.1.symm
    have Htcb0 : uint.Z s0.gh.tc < 2 ^ 64 := by word
    clear Hs0
    wp_auto
    rw [Hasync]
    wp_auto
    ihave %Hlen := BigSepL2.bigSepL2_length $$ Hpend
    ihave %Hsl := ownSlice_len _ _ _ $$ Hsteps
    rename_i ibp
    irename: (ibp ↦ (_ : w64)) => ib
    have Hlen2 : rs.steps.length = pre.length + 1 := by rw [Hsteq]; simp
    ihave IH : iprop(∃ (n : w64) (s1 : NState) (steps1 : List Loc) (mv : Loc) (iv : w64)
        (cf1 : CfgM) (md1 : GMode),
        "i" ∷ i_ptr ↦ n ∗ "m" ∷ m_ptr ↦ mv ∗ "ib" ∷ ibp ↦ iv ∗
        "Hphys" ∷ ownRaftPhysCV cf1 cf1.voters rnv.raft' id s1 ∗
        "Hghost" ∷ ownStepGhost γ md1 cf1 id s1 ∗
        -- (2026-10-28, stage U3c) the mode at the `RawNode`'s ghost part until the snapshot's
        -- acknowledgement, at the snapshot's index and the fold of its committed log after it
        "%Hmd1" ∷ ⌜(sint.nat n ≤ pre.length → md1 = rs.mode.toG ⟨rs.capplied, rs.cfg, fp, ds⟩) ∧
          (pre.length < sint.nat n → md1 = rs.mode.toG
            ⟨uint.nat l.snap.Metadata'.Index', rs.mode.foldCfg l.dlv rs.cfg, fp, ds⟩)⌝ ∗
        "Hsteps" ∷ rnv.stepsOnAdvance' ↦* steps1 ∗
        "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (steps.length : Int)⌝ ∗
        "%Hsteps1" ∷ ⌜steps1.length = steps.length ∧
                      steps1.drop (sint.nat n) = steps.drop (sint.nat n)⌝ ∗
        "%Hwf1" ∷ ⌜NStateWf s1⌝ ∗
        "%Hs1" ∷ ⌜s1.logst.unpersisted = [] ∧ s1.logst.prev = s0.logst.prev ∧
                  logStoreRec s1.logst = logStoreRec s0.logst ∧
                  (sint.nat n ≤ pre.length →
                    s1.logst.applying = s0.logst.applying ∧ s1.logst.snap = s0.logst.snap) ∧
                  (pre.length < sint.nat n →
                    (rs.psnap = false → s1.logst.snap = none) ∧
                    s1.logst.applying = l.snap.Metadata'.Index' ∧
                    s1.logst.applied = l.snap.Metadata'.Index' ∧ s1.logst.sip = false ∧
                    s1.logst.sat = false ∧ s1.logst.lent = false ∧
                    -- (2026-10-26, D22 J2) the pending snapshot kept or cleared (`ackSnapLog_snap`)
                    (s1.logst.snap = s.logst.snap ∨ s1.logst.snap = none) ∧
                    -- (U3c) a follower (it was one, a snapshot pending)
                    s1.role = .follower)⌝ ∗
        "%Hsg1" ∷ ⌜s1.logst.storage = s0.logst.storage ∧ s1.prevote = s0.prevote ∧ s1.gh = s0.gh⌝ ∗
        "%Hc1" ∷ ⌜uint.Z s0.logst.committed ≤ uint.Z s1.logst.committed⌝ ∗
        "%Hok1" ∷ ⌜StepsOk s1 (rs.steps.drop (sint.nat n))⌝ ∗
        "%Hsb1" ∷ ⌜SelfBound s0 (rs.steps.drop (sint.nat n))⌝ ∗
        "%Hti1" ∷ ⌜TermInv s0 s1 (rs.steps.drop (sint.nat n))⌝ ∗
        "%Hfl1" ∷ ⌜s1.logst.fl = s0.logst.fl ∧ uint.Z s0.logst.applied ≤ uint.Z s1.logst.applied⌝ ∗
        -- (2026-10-28, stage U0) the configuration `cf` until the snapshot's acknowledgement,
        -- the snapshot's after it (`appliedSnap`); a node with a snapshot pending a follower
        "%Hcf1" ∷ ⌜cf1.autoLeave = false ∧ (sint.nat n ≤ pre.length → cf1 = cf)⌝ ∗
        "%Hsf1" ∷ ⌜SnapFol s1⌝ ∗
        "Hpend" ∷ pendList γ id (steps.drop (sint.nat n)) (rs.steps.drop (sint.nat n)))
      $$ [i m ib Hphys Hghost Hsteps Hpend]
    · iexists W64 0, s0, steps, null, zero_val w64, cf, rs.mode.toG ⟨rs.capplied, rs.cfg, fp, ds⟩
      have H0 : sint.nat (W64 0) = 0 := rfl
      rw [H0, List.drop_zero, List.drop_zero]
      simp only [named]
      iframe
      ipureintro
      have Htc0 : s0.gh.tc = s.gh.tc := Hs0f.2.2.2.2.2.2.2.2.2.2.2.2.1
      refine ⟨⟨fun _ => by first | rfl | trivial, fun h => absurd h (by omega)⟩, by word,
        ⟨trivial, trivial⟩, Hwf0,
        ⟨Hs0f.2.1, by simp, by simp, by simp,
          fun h => absurd h (by omega)⟩, by simp, Int.le_refl _, Hstok0,
        stepsOk_selfBound s0 rs.steps Hstok0, ⟨Int.le_refl _, by omega, fun _ _ => rfl, ?_, ?_⟩,
        ⟨by simp, Int.le_refl _⟩, ⟨Hal, fun _ => by first | rfl | trivial⟩,
        fun h => by
          rw [Hs0f.2.2.2.2.2.2.2.2.2.2.2.1]
          exact Hpvoff.2.2.2.2 (by rw [← Hs0f.2.2.1]; exact h)⟩
      · rw [Htc0, Hs0f.2.2.2.2.2.2.2.2.2.2.1]; exact Hpvoff.2.2.1
      · intro h
        rw [Htc0, Hs0f.2.2.2.2.2.2.2.2.2.2.1]
        exact Hpvoff.2.2.2.1 (by rw [← Hs0f.2.2.2.2.2.2.2.2.2.2.2.1]; exact h)
    wp_for IH
    wp_if_destruct
    · have Hlt : sint.Z n < sint.Z rnv.stepsOnAdvance'.len := by
        first | exact Hif | exact of_decide_eq_true (GoGlobalContext.intoVal_inj_bool Hif)
      clear Hif
      list_elem steps (sint.nat n) as mm
      list_elem rs.steps (sint.nat n) as p
      have Hmm1 : steps1[sint.nat n]? = some mm := by
        have H := congrArg (fun l => l[0]?) Hsteps1.2
        simp only [List.getElem?_drop, Nat.add_zero] at H
        rw [H]; exact Hmm_lookup
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hn.1, Hlt⟩)]
      wp_apply (lc := 1) wp_load_slice_index rnv.stepsOnAdvance' (sint.Z n) steps1 (DFrac.own 1) mm Hn.1
        $$ [Hsteps] with Hsteps
      · iframe
        ipureintro
        exact Hmm1
      have Hnl : sint.nat n < pre.length + 1 := by
        rw [← Hlen2]; exact (List.getElem?_eq_some_iff.1 Hp_lookup).1
      -- (U0) before the snapshot's acknowledgement: still at `cf`; (U3c) and at the mode's
      have Hcfe := Hcf1.2 (by omega)
      subst cf1
      have Hmde := Hmd1.1 (by omega)
      subst md1
      rw [drop_cons_of_lookup Hp_lookup] at Hok1 Hsb1 Hti1
      rw [drop_cons_of_lookup Hmm_lookup, drop_cons_of_lookup Hp_lookup]
      icases (BigSepL2.bigSepL2_cons (Φ := fun _ l p => iprop(∃ st, msgIn (GF := GF) l DFrac.discard st ∗
          pendingRel γ id st p))).1 $$ Hpend with ⟨⟨%st, Hmin, #Hpm⟩, Hpend⟩
      have HnS : sint.nat n + 1 = sint.nat (n + W64 1) := by word
      rw [HnS] at Hok1 Hsb1 Hti1 ⊢
      obtain ⟨Hpok, Hrest⟩ := stepsOk_cons _ _ _ Hok1
      by_cases Hnp : sint.nat n < pre.length
      · -- one of the node's own responses
        have Hpp : p ∈ pre := by
          rw [Hsteq, List.getElem?_append_left Hnp] at Hp_lookup
          exact List.mem_of_getElem? Hp_lookup
        obtain ⟨pv0, t0, rfl⟩ := Hpre _ Hpp
        have Hnw1 : ∀ pv t, Pending.self pv0 t0 = .self pv t → s1.role = .preCandidate →
            uint.Z s1.term + 1 < 2 ^ 64 := by
          intro pv t _ hr
          have := Hti1.2.2.2.2 hr
          omega
        -- (U3c) a snapshot pending: a follower, whose campaign guard holds
        have Hfol1 : s1.role = .follower := Hsf1 (by
          rw [(Hs1.2.2.2.1 (by omega)).2, Hs0f.2.2.1]; exact Hsnn)
        icases ownRaftPhysC_preFacts cf rnv.raft' id s1
            (RNMode.guard_of (fun _ => preGuardF_of_fol Hfol1) rs.capplied rs.cfg) $$ Hphys
          with ⟨%Hpf1, Hphys⟩
        wp_apply wp_step_pending wp_raft_Step γ cf _ rnv.raft' id s1 mm st (.self pv0 t0) Hwf1
          Hpok Hal (fun _ _ _ _ h => by cases h) Hs1.1 Hnw1
          (by rw [Hsg1.2.2, Hs0f.2.2.2.2.2.2.2.2.2.2.2.2.2.1]; exact Hunst) Hpf1
          (fun _ _ h => by cases h)
          $$ [$Hphys $Hghost $Hmin $Hpm $Hlc1] as %err %s2 %md2 ⟨Hphys, Hghost, %Hst2⟩
        obtain ⟨Hwf2, Hout2, Hns2, Hna2, Ha2, Hu2, Hsn2, Ht2, Hps2, Hpv2, Hsd2, Hsg2, Hsg2', Hsg2'', Hrl2,
          -, Hfl2, Hap2, Hack2, Hsrb2, Hapa2⟩ := Hst2
        have Hc12 := Hout2.commit_mono
        obtain ⟨ca', rfl, -, -, -, Hca4⟩ := RNMode.stepOut_ca Hout2 Hns2 Hapa2
        obtain rfl := Hca4 (Hna2 (fun _ h => by cases h))
        rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hn.1, Hlt⟩)]
        wp_apply wp_store_slice_index rnv.stepsOnAdvance' (sint.Z n) steps1 (null : Loc)
          $$ [Hsteps] with Hsteps
        · iframe
          ipureintro
          constructor <;> word
        wp_for_post
        iframe
        iexists n + W64 1, s2, steps1.set (sint.Z n).toNat (null : Loc), mm, n, cf,
          rs.mode.toG ⟨rs.capplied, rs.cfg, fp, ds⟩
        iframe
        ipureintro
        have Hle : sint.nat (n + W64 1) ≤ pre.length := by rw [← HnS]; omega
        refine ⟨⟨fun _ => by first | rfl | trivial, fun h => absurd h (by omega)⟩, by word, ⟨by rw [List.length_set]; exact Hsteps1.1, ?_⟩, Hwf2,
          ⟨Hu2.trans Hs1.1, Hpv2.trans Hs1.2.1, Hsd2.trans Hs1.2.2.1,
            fun _ => ⟨Ha2.trans (Hs1.2.2.2.1 (by omega)).1, Hsn2.trans (Hs1.2.2.2.1 (by omega)).2⟩,
            fun h => absurd h (by omega)⟩,
          ⟨Hsg2.trans Hsg1.1, Hsg2'.trans Hsg1.2.1, Hsg2''.trans Hsg1.2.2⟩,
          Int.le_trans Hc1 Hc12,
          stepsOk_mono_le s1 s2 _ Ht2 ⟨Hpv2, logStoreRec_stored Hsd2⟩ Hc12 Ha2 (tc_le_of_gh Hsg2'') Hrest,
          fun pv t h => Hsb1 pv t (List.mem_cons_of_mem _ h),
          termInv_step s0 s1 s2 _ _ Hok1 Hsb1 Hti1 Ht2 Hps2 Hrl2,
          ⟨Hfl2.trans Hfl1.1, Int.le_trans Hfl1.2 Hap2⟩, ⟨Hal, fun _ => by first | rfl | trivial⟩, Hsf1.step Hsrb2⟩
        rw [← HnS, List.drop_set_of_lt (by simp [sint.nat]), ← List.drop_drop, ← List.drop_drop,
          Hsteps1.2]
      · -- the snapshot's acknowledgement, last
        have Hne : sint.nat n = pre.length := by omega
        have Hpe : p = .appendAck tA (snapId l.snap) eA (some l.snap) := by
          rw [Hsteq, Hne] at Hp_lookup; simp at Hp_lookup; exact Hp_lookup.symm
        subst Hpe
        iunfold pendingRel at Hpm
        icases Hpm with ⟨%Hst, -⟩
        have Hst' : st = _ := Hst
        subst Hst'
        obtain ⟨Hap1, Hsn1⟩ := Hs1.2.2.2.1 (by omega)
        icases ownRaftPhysC_gh cf rnv.raft' id s1 $$ Hphys with ⟨%Hgh1, Hphys⟩
        have Hsnp1 : s1.gh.snp = some (snapTrip l.snap l.snap.Metadata'.ConfState'.lists) := by
          rw [Hsg1.2.2, Hs0f.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]; exact Hsnp
        have Hsn1s : s1.logst.snap = s.logst.snap := by rw [Hsn1, Hs0f.2.2.1]
        have Hlt1 : s1.logst.lent = false := by
          rw [Hgh1.1.2.1, Hsg1.2.2]; exact Hs0f.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
        icases ownRaftPhysC_logwf cf rnv.raft' id s1 $$ Hphys with ⟨%Hlw1, Hphys⟩
        -- (U3c) what the dynamic mode's acknowledgement needs: `applied` below the snapshot's
        -- index, the index at most the commit index, the committed log up to it of its length
        have Happ1 : uint.Z s1.logst.applied < uint.Z l.snap.Metadata'.Index' := by
          have := Hlw1.1; rw [Hap1, Hs0f.1] at this; omega
        have Hcm1 : uint.Z l.snap.Metadata'.Index' ≤ uint.Z s1.logst.committed := by
          have := Hs0f.2.2.2.2.2.2.2.1; rw [this] at Hc1; omega
        have Hdlen' : l.dlv.length = uint.nat l.snap.Metadata'.Index' := by
          have := uint_nat_eq l.snap.Metadata'.Index'; omega
        have Hal1' : (rs.mode.toG ⟨rs.capplied, rs.cfg, fp, ds⟩).isDyn = true →
            l.snap.Metadata'.ConfState'.AutoLeave' = false := fun hd =>
          Hal1 l hsl (by rw [← RNMode.toG_isDyn rs.mode ⟨rs.capplied, rs.cfg, fp, ds⟩]; exact hd)
        -- (D22 S-d3b) the acknowledgement's facts (`ackInv`): the records of what the storage
        -- holds after the lent snapshot, and the arm
        have Hmem : Pending.appendAck tA (snapId l.snap) eA (some l.snap) ∈ rs.steps := by
          rw [Hsteq]; simp
        have HpoS := stepsOk_ack Hstok Hmem
        icases Hstrecs $$ %tA %(snapId l.snap) %eA %(some l.snap) %Hmem with ⟨#Hstr0, #Harm⟩
        ihave #Hstr1 : storedRecs γ (snapId l.snap) s1.logst.stored $$ []
        · rw [logStoreRec_stored Hs1.2.2.1, Hs0f.2.2.2.2.1]; iexact Hstr0
        have Hgt : pre.length < sint.nat (n + W64 1) := by rw [← HnS]; omega
        have Hdr : rs.steps.drop (sint.nat (n + W64 1)) = [] :=
          List.drop_eq_nil_of_le (by rw [Hlen2, ← HnS]; omega)
        iunfold ownStepGhost at Hghost
        icases Hghost with ⟨Hg, Hgr⟩
        rcases Hss with Hu | ⟨s2, Hs2, Hl2, Hps2⟩
        · -- the lent snapshot still pending: the storage at it (`sat`), the `sapp` window
          have Hsn1' : s1.logst.snap = some (snapId l.snap) := Hsn1s.trans Hu
          have Hsat1 : s1.logst.sat = true := by
            rcases ((Hgh1.1.2.2.1 _ Hsnp1).1 Hsn1').2 with h | h
            · rw [Hlt1] at h; cases h
            · exact h
          have Hpv1 : s1.logst.prev = snapId l.snap := by
            rw [Hs1.2.1, Hs0f.2.2.2.1]; exact Hpvs _ Hu
          have Hak : ackLog s1.logst (some l.snap) = { s1.logst with sapp := true } := by
            simp [ackLog, Hsat1]
          ihave #Hstr2 : storedRecs γ s1.logst.prev s1.logst.stored $$ []
          · rw [Hpv1]; iexact Hstr1
          icases stableOk_of_stored_ls γ id s1 (ackLog s1.logst (some l.snap)) _
              (by rw [Hak]; exact ⟨rfl, rfl, rfl⟩) rfl (.inr (by rw [Hak])) (by rw [Hak]; exact Hs1.1)
            $$ Hstr2 Hg with ⟨%Hsok, Hg⟩
          ihave Hghost : ownStepGhost γ (rs.mode.toG ⟨rs.capplied, rs.cfg, fp, ds⟩) cf id s1 $$ [Hg Hgr]
          · iunfold ownStepGhost; iframe Hg Hgr
          wp_apply wp_step_snapack wp_raft_Step γ (rs.mode.toG ⟨rs.capplied, rs.cfg, fp, ds⟩) cf rnv.raft'
            id s1 mm tA (snapId l.snap) eA l.snap l.dlv
            Hwf1 Hpok Hal (by rw [Hsn1', Hsat1]; simp [snapHit, snapId])
            (by rw [Hpv1]; exact Int.le_refl _)
            (fun x hx _ => by rw [← (Hpok.2 x hx).1, ← Hpv1]; exact Hsok)
            (by rw [Hsg1.2.2, Hs0f.2.2.2.2.2.2.2.2.2.2.2.2.2.1]; exact Hunst)
            (fun hs hl => (Hgh1.1.2.2.2.2.2 _ Hsnp1 hl).1 hs)
            (fun k hk => by rw [Hsnp1] at hk; cases hk; exact Int.le_refl _)
            (Hsf1 (by rw [Hsn1']; simp)) (by rw [Hsn1']; simp) Hsnp1 Hhas
            (fun hd => ⟨Happ1, fun _ => by rw [Hpv1]; rfl, Hdlen', Hdlast, Hcm1, Hal1' hd⟩)
            $$ [$Hphys $Hghost $Hmin $Hlc1 $Hdl] as %err %s2 %md2 ⟨Hphys, Hghost, %Hst2⟩
          obtain ⟨Hwf2, Hmds, Hmdd, Hal2, prs2, pvs2, il2, Hs2⟩ := Hst2
          have Hmd2 := snapack_mode Hmds Hmdd
          have Hl2 : s2.logst =
              ackSnapLog s1.logst (appendAckM id tA (eA.getD ⟨W64 0, W64 0⟩)) s1.term l.snap := by
            rw [Hs2]
          have Hg2 : s2.gh = s1.gh := by rw [Hs2]
          have Ht2 : s2.term = s1.term := by rw [Hs2]
          have Hpv2 : s2.prevote = s1.prevote := by rw [Hs2]
          have Hr2 : s2.role = s1.role := by rw [Hs2]
          obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12⟩ :=
            ackSnapLog_facts s1.logst (appendAckM id tA (eA.getD ⟨W64 0, W64 0⟩)) s1.term
              l.snap Hsn1' (by rw [Hap1, Hs0f.1]; exact Hapl) Hlw1.1
          rw [← Hl2] at b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12
          rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hn.1, Hlt⟩)]
          wp_apply wp_store_slice_index rnv.stepsOnAdvance' (sint.Z n) steps1 (null : Loc)
            $$ [Hsteps] with Hsteps
          · iframe
            ipureintro
            constructor <;> word
          wp_for_post
          iframe
          iexists n + W64 1, s2, steps1.set (sint.Z n).toNat (null : Loc), mm, n,
            snapCfg l.snap l.snap.Metadata'.ConfState'.lists, md2
          iframe
          ipureintro
          refine ⟨⟨fun h => absurd h (by omega), fun _ => Hmd2⟩, by word,
            ⟨by rw [List.length_set]; exact Hsteps1.1, ?_⟩, Hwf2,
            ⟨b6.trans Hs1.1, b7.trans Hs1.2.1, b8.trans Hs1.2.2.1,
              fun h => absurd h (by omega), fun _ => ⟨fun _ => b1, b4, b5, b2, b3, b12.trans Hlt1,
                by rw [Hl2]; exact (ackSnapLog_snap _ _ _ _).imp_left (fun h => h.trans Hsn1s),
                Hr2.trans (Hsf1 (by rw [Hsn1']; simp))⟩⟩,
            ⟨b9.trans Hsg1.1, Hpv2.trans Hsg1.2.1, Hg2.trans Hsg1.2.2⟩,
            by rw [b11]; exact Hc1,
            by rw [Hdr]; trivial,
            fun pv t h => Hsb1 pv t (List.mem_cons_of_mem _ h),
            termInv_step s0 s1 s2 _ _ Hok1 Hsb1 Hti1 (by rw [Ht2]; exact Int.le_refl _) Ht2
              (fun h => ⟨Hr2 ▸ h, Ht2⟩),
            ⟨by rw [b10]; exact Hfl1.1, ?_⟩, ⟨Hal2, fun h => absurd h (by omega)⟩,
            fun _ => Hr2.trans (Hsf1 (by rw [Hsn1']; simp))⟩
          · rw [← HnS, List.drop_set_of_lt (by simp [sint.nat]), ← List.drop_drop, ← List.drop_drop,
              Hsteps1.2]
          · rw [b5]
            have := Hfl1.2
            have := Hlw1.1
            rw [Hap1, Hs0f.1] at this
            have := Hapl
            omega
        · -- (D22 S-d3b) a later snapshot restored: the storage shadowed (`sat` off), the
          -- acknowledgement's `stableTo` missing (`stableHit_restored`, the restore's mark)
          have Hsn1' : s1.logst.snap = some s2 := Hsn1s.trans Hs2
          have Hpv1 : s1.logst.prev = s2 := by rw [Hs1.2.1, Hs0f.2.2.2.1]; exact Hpvs _ Hs2
          have Hne2 : ∀ k, s1.gh.snp = some k → s1.logst.snap = some k.sid → False := by
            intro k hk hks
            rw [Hsnp1] at hk; cases hk
            rw [Hsn1'] at hks
            simp only [Option.some.injEq, snapTrip, snapId] at hks
            rw [hks] at Hl2; simp at Hl2
          have Hsat1 : s1.logst.sat = false := by
            cases h : s1.logst.sat
            · rfl
            · exfalso
              obtain ⟨k, hk, hks⟩ := Hgh1.1.2.2.2.2.1 (.inr h)
              exact Hne2 k hk hks
          have Hsip1 : s1.logst.sip = false := by
            cases h : s1.logst.sip
            · rfl
            · exfalso
              obtain ⟨k, hk, hks⟩ := Hgh1.1.2.2.2.2.1 (.inl h)
              exact Hne2 k hk hks
          have Hak : ackLog s1.logst (some l.snap) = s1.logst := by simp [ackLog, Hsat1]
          have Hbp1 : uint.Z (snapId l.snap).index' < uint.Z s1.logst.prev.index' := by
            rw [Hpv1]; exact Hl2
          ihave %Hnb : ⌜eA ≠ none ∧ s.term = tA →
              plogTermAt (snapId l.snap) s1.logst.stored s1.logst.prev.index' ≠
                some s1.logst.prev.term'⌝ $$ []
          · unfold ackArm
            icases Harm with (⟨%Hp, -⟩ | ⟨%Hbp, #Hb⟩)
            · exfalso
              have := Hpvs _ Hs2
              rw [Hp.1] at this
              rw [← this] at Hl2
              simp [snapId] at Hl2
            · by_cases hc : eA ≠ none ∧ s.term = tA
              · ihave #Hb' := Hb $$ %hc
                iunfold ackBaseW at Hb'
                icases Hb' with ⟨%H, -⟩
                ipureintro
                intro _
                rw [Hs1.2.1, logStoreRec_stored Hs1.2.2.1, Hs0f.2.2.2.1, Hs0f.2.2.2.2.1]
                exact H
              · ipureintro; exact fun h => absurd h hc
          ihave ⟨%Hmiss0, Hg⟩ : ⌜eA ≠ none ∧ s.term = tA →
              ¬ StableHit s1.logst (plogLast (snapId l.snap) s1.logst.stored)⌝ ∗
              ownRaftGhost γ id (toPState s1) (rs.mode.toG ⟨rs.capplied, rs.cfg, fp, ds⟩).isDyn $$ [Hg]
          · by_cases hc : eA ≠ none ∧ s.term = tA
            · icases stableHit_restored γ id s1 (snapId l.snap) Hbp1 (Hnb hc) $$ Hstr1 Hg
                with ⟨%Hm, Hg⟩
              iframe Hg; ipureintro; exact fun _ => Hm
            · iframe Hg; ipureintro; exact fun h => absurd h hc
          have Hts : s.term = s0.term := Hs0f.2.2.2.2.2.2.2.2.2.2.1.symm
          have Hnh : ∀ x, eA = some x → (tA = W64 0 ∨ tA = s1.term) → ¬ StableHit s1.logst x := by
            intro x hx ht
            have h1 := Hpok.2 x hx
            have Htn : tA = s1.term := ht.resolve_left (fun h => by have h2 := h1.2; rw [h] at h2; word)
            have Hst : s.term = tA :=
              ack_term_back HpoS.1 (by rw [Hts]; exact Hti1.1) Htn.symm
            rw [← h1.1]
            exact Hmiss0 ⟨by rw [hx]; simp, Hst⟩
          have Hmiss : ∀ id', ackStableId (appendAckM id tA (eA.getD ⟨W64 0, W64 0⟩)) s1.term =
              some id' → ¬ StableHit s1.logst id' := by
            intro id' h
            unfold ackStableId at h
            split at h
            · rename_i hc
              cases h
              cases hx : eA with
              | none => simp [hx, appendAckM] at hc
              | some x =>
                simp only [hx, Option.getD_some, appendAckM] at hc ⊢
                exact Hnh x hx hc.1
            · cases h
          ihave Hghost : ownStepGhost γ (rs.mode.toG ⟨rs.capplied, rs.cfg, fp, ds⟩) cf id s1 $$ [Hg Hgr]
          · iunfold ownStepGhost; iframe Hg Hgr
          have Hhit1 : snapHit s1.logst.snap l.snap.Metadata'.Index' = false := by
            rw [Hsn1']
            simp only [snapHit, decide_eq_false_iff_not]
            intro h; rw [h] at Hl2; simp [snapId] at Hl2
          have Hsnb1 : s1.logst.snap = none ∨ snapHit s1.logst.snap l.snap.Metadata'.Index' = true →
              l.snap.Metadata'.Index' = s1.logst.prev.index' := by
            intro h
            rcases h with h | h
            · rw [Hsn1'] at h; cases h
            · rw [Hhit1] at h; cases h
          wp_apply wp_step_snapack wp_raft_Step γ (rs.mode.toG ⟨rs.capplied, rs.cfg, fp, ds⟩) cf rnv.raft'
            id s1 mm tA (snapId l.snap) eA l.snap l.dlv
            Hwf1 Hpok Hal (by rw [Hhit1, Hsat1])
            (by rw [Hpv1]; exact Int.le_of_lt Hl2)
            (fun x hx ht => by rw [Hak]; exact fun h => absurd h (Hnh x hx ht))
            (by rw [Hsg1.2.2, Hs0f.2.2.2.2.2.2.2.2.2.2.2.2.2.1]; exact Hunst)
            (fun hs hl => (Hgh1.1.2.2.2.2.2 _ Hsnp1 hl).1 hs)
            (fun k hk => by rw [Hsnp1] at hk; cases hk; exact Int.le_refl _)
            (Hsf1 (by rw [Hsn1']; simp)) (by rw [Hsn1']; simp) Hsnp1 Hhas
            (fun hd => ⟨Happ1, Hsnb1, Hdlen', Hdlast, Hcm1, Hal1' hd⟩)
            $$ [$Hphys $Hghost $Hmin $Hlc1 $Hdl] as %err %s2' %md2 ⟨Hphys, Hghost, %Hst2⟩
          obtain ⟨Hwf2, Hmds, Hmdd, Hal2, prs2, pvs2, il2, Hs2'⟩ := Hst2
          have Hmd2 := snapack_mode Hmds Hmdd
          have Hl2' : s2'.logst =
              ackSnapLog s1.logst (appendAckM id tA (eA.getD ⟨W64 0, W64 0⟩)) s1.term l.snap := by
            rw [Hs2']
          have Hg2 : s2'.gh = s1.gh := by rw [Hs2']
          have Ht2 : s2'.term = s1.term := by rw [Hs2']
          have Hpv2 : s2'.prevote = s1.prevote := by rw [Hs2']
          have Hr2 : s2'.role = s1.role := by rw [Hs2']
          obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12⟩ :=
            ackSnapLog_facts_miss s1.logst (appendAckM id tA (eA.getD ⟨W64 0, W64 0⟩)) s1.term
              l.snap Hhit1 Hsat1 Hmiss (by rw [Hap1, Hs0f.1]; exact Hapl) Hlw1.1
          rw [← Hl2'] at b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12
          rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hn.1, Hlt⟩)]
          wp_apply wp_store_slice_index rnv.stepsOnAdvance' (sint.Z n) steps1 (null : Loc)
            $$ [Hsteps] with Hsteps
          · iframe
            ipureintro
            constructor <;> word
          wp_for_post
          iframe
          iexists n + W64 1, s2', steps1.set (sint.Z n).toNat (null : Loc), mm, n,
            snapCfg l.snap l.snap.Metadata'.ConfState'.lists, md2
          iframe
          ipureintro
          refine ⟨⟨fun h => absurd h (by omega), fun _ => Hmd2⟩, by word,
            ⟨by rw [List.length_set]; exact Hsteps1.1, ?_⟩, Hwf2,
            ⟨b6.trans Hs1.1, b7.trans Hs1.2.1, b8.trans Hs1.2.2.1,
              fun h => absurd h (by omega),
              fun _ => ⟨(fun h => by rw [Hps2] at h; cases h), b4, b5, b2.trans Hsip1, b3,
                b12.trans Hlt1,
                by rw [Hl2']; exact (ackSnapLog_snap _ _ _ _).imp_left (fun h => h.trans Hsn1s),
                Hr2.trans (Hsf1 (by rw [Hsn1']; simp))⟩⟩,
            ⟨b9.trans Hsg1.1, Hpv2.trans Hsg1.2.1, Hg2.trans Hsg1.2.2⟩,
            by rw [b11]; exact Hc1,
            by rw [Hdr]; trivial,
            fun pv t h => Hsb1 pv t (List.mem_cons_of_mem _ h),
            termInv_step s0 s1 s2' _ _ Hok1 Hsb1 Hti1 (by rw [Ht2]; exact Int.le_refl _) Ht2
              (fun h => ⟨Hr2 ▸ h, Ht2⟩),
            ⟨by rw [b10]; exact Hfl1.1, ?_⟩, ⟨Hal2, fun h => absurd h (by omega)⟩,
            fun _ => Hr2.trans (Hsf1 (by rw [Hsn1']; simp))⟩
          · rw [← HnS, List.drop_set_of_lt (by simp [sint.nat]), ← List.drop_drop, ← List.drop_drop,
              Hsteps1.2]
          · rw [b5]
            have := Hfl1.2
            have := Hlw1.1
            rw [Hap1, Hs0f.1] at this
            have := Hapl
            omega
    · -- the loop is done: `stepsOnAdvance = stepsOnAdvance[:0]`
      have Hif' : ¬ sint.Z n < sint.Z rnv.stepsOnAdvance'.len := by
        first | exact Hif | exact fun h => Hif (by rw [decide_eq_true h])
      clear Hif
      try (rw [if_pos (decide_eq_true (by rw [decide_eq_false Hif'] :
        (#(decide (sint.Z n < sint.Z rnv.stepsOnAdvance'.len)) : val) = #false))]; wp_auto)
      ihave %Hwfs := ownSlice_wf _ _ _ $$ Hsteps
      rw [ite_eq_left_of_eq_true _ _ (eq_true (slice00_ok Hwfs).1)]
      wp_auto
      icases (ownSlice_slice (W64 0) (W64 0) _ _ _ (slice00_ok Hwfs).2).1 $$ Hsteps
        with ⟨-, Hsl0, Hrest⟩
      ihave Hcap0 := ownSlice_slice_absorb_capacity _ _ (W64 0) (W64 0) (slice00_ok Hwfs).2
        $$ [$Hrest $Hsteps_cap]
      have Hsub : subslice (sint.nat (W64 0)) (sint.nat (W64 0)) steps1 = [] := by
        simp [subslice]
      rw [Hsub]
      have Hnn : sint.nat n = steps.length := loop_done_nat Hif' Hn Hsl.1 Hsl.2
      have Hgt : pre.length < sint.nat n := by rw [Hnn, Hlen, Hlen2]; omega
      obtain ⟨Hsn1, Hap1, Happ1, Hsip1, Hsat1, Hlt1, Hsk1, Hrl1⟩ := Hs1.2.2.2.2 Hgt
      -- (U3c) the configuration index after: dynamically the snapshot's, statically unmoved
      obtain ⟨CA, HCA⟩ : ∃ CA : Nat, CA = if rs.mode.isDyn then l.dlv.length else rs.capplied :=
        ⟨_, rfl⟩
      have Hmdf : md1 = rs.mode.toG ⟨CA, rs.mode.foldCfg l.dlv rs.cfg, fp, ds⟩ := by
        rw [Hmd1.2 Hgt]
        cases hm : rs.mode.isDyn
        · exact RNMode.toG_static hm _ _
        · rw [HCA, if_pos hm, Hdll]; rfl
      subst md1
      ihave #Hsloc' := snapLocOk_keep γ id Hsk1 $$ Hsloc
      -- the snapshot handed out, acknowledged: the mirror's record of it dropped
      icases ownRaftPhysC_log_at_snp cf1 rnv.raft' id s1 $$ Hphys with ⟨Hlog1, %Hgh1, Hback1⟩
      ihave Hphys := Hback1 $$ %s1.logst %false %none Hlog1
        %(⟨⟨fun h => (by
              rw [Hsg1.2.2, Hs0f.2.2.2.2.2.2.2.2.2.2.2.2.2.1] at h; rw [Hunst] at h; cases h),
            SnpOk.of_none (g := { s1.gh with slent := false, snp := none }) Hlt1 rfl Hsip1 Hsat1⟩,
          fun _ => ⟨rfl, rfl, rfl, Int.le_refl _⟩, rfl⟩ :
          LogGhOk { s1 with gh := { s1.gh with slent := false, snp := none } } s1.logst)
        %(fun _ => Int.le_refl _)
      ihave Hghost := ownStepGhost_congr γ _ cf1 id (s := s1)
        (s' := { s1 with logst := s1.logst, gh := { s1.gh with slent := false, snp := none } })
        rfl rfl rfl rfl $$ Hghost
      ihave #Hstr1 : ackInv γ { rs with
              steps := [], term := s1.term, capplied := CA, flw := false, slent := none,
              unpersisted := [], delivered := l.dlv, cfg := rs.mode.foldCfg l.dlv rs.cfg }
          { s1 with logst := s1.logst, gh := { s1.gh with slent := false, snp := none } } $$ []
      · iapply ackInv_none; intro _ _ _ _ h; cases h
      have Htc1 : s1.gh.tc = s.gh.tc := by rw [Hsg1.2.2]; exact Hs0f.2.2.2.2.2.2.2.2.2.2.2.2.1
      have HrnflA : RNFl { rs with
              steps := [], term := s1.term, capplied := CA, flw := false, slent := none,
              unpersisted := [], delivered := l.dlv, cfg := rs.mode.foldCfg l.dlv rs.cfg }
          { s1 with logst := s1.logst, gh := { s1.gh with slent := false, snp := none } } := by
        refine ⟨fun _ => ?_, fun h => absurd h (by show ¬ (uint.Z s1.logst.applied < _); rw [Hap1, Happ1]; omega)⟩
        show uint.Z s1.logst.fl ≤ uint.Z s1.logst.applied
        rw [Hfl1.1, Hs0f.2.2.2.2.2.2.2.2.1, Happ1]
        have := Hflb0.1
        omega
      have HloanA : LoanOk { rs with
              steps := [], term := s1.term, capplied := CA, flw := false, slent := none,
              unpersisted := [], delivered := l.dlv, cfg := rs.mode.foldCfg l.dlv rs.cfg }
          { s1 with logst := s1.logst, gh := { s1.gh with slent := false, snp := none } } :=
        ⟨rfl, fun _ => ⟨rfl, fun _ _ _ _ h => (by cases h)⟩, fun l h => (by cases h)⟩
      iapply HΦ $$ %s1.term %CA
      rw [advRS_some _ _ hsl]
      isplitl
      · iapply ownRawNode_intro γ rn id
          { rs with
              steps := [], term := s1.term, capplied := CA, flw := false, slent := none,
              unpersisted := [], delivered := l.dlv, cfg := rs.mode.foldCfg l.dlv rs.cfg }
          { s1 with logst := s1.logst, gh := { s1.gh with slent := false, snp := none } }
          cf1 fp
          { rnv with stepsOnAdvance' :=
              slice.slice rnv.stepsOnAdvance' Loc (W64 0) (W64 0) }
          sv hprev [] Hwf1 Hin Hcf1.1 Hasync
          (by show l.dlv.length = _; rw [Hap1]; exact Hdll)
          Hs1.1.symm
          (fun h => Hsn1 h.1) trivial rfl
          (by show rs.storage = _; rw [Hsg1.1, Hs0f.2.2.2.2.2.1]; exact Hstor)
          (by
            refine ⟨fun _ => preGuardF_of_fol Hrl1, by show rs.tc = s1.gh.tc; rw [Htc1]; exact Hpvoff.2.1, ?_, ?_, Hsf1⟩
            · show uint.Z s1.term ≤ uint.Z s1.gh.tc
              rw [Htc1, ← Hs0f.2.2.2.2.2.2.2.2.2.2.2.2.1]; exact Hti1.2.2.2.1
            · intro h
              show uint.Z s1.term + 1 ≤ uint.Z s1.gh.tc
              rw [Htc1, ← Hs0f.2.2.2.2.2.2.2.2.2.2.2.2.1]; exact Hti1.2.2.2.2 h)
          (by show rs.outlb = _; rw [Hsg1.2.2, Hs0f.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]; exact Hrs_out)
          (by show rs.unst = _; rw [Hsg1.2.2, Hs0f.2.2.2.2.2.2.2.2.2.2.2.2.2.1]; exact Hrs_unst)
          (by show uint.Z rs.clb ≤ _
              have := Hs0f.2.2.2.2.2.2.2.1; rw [this] at Hc1; exact Int.le_trans Hrs_clb Hc1)
          HrnflA HloanA
          (fun _ k t h => by
            have e : s1.logst.sdt = s0.logst.sdt := congrArg (·.2.2) Hs1.2.2.1
            rw [e, Hsd0] at h; simp at h)
          $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsl0 Hcap0 [] Hdl Hstr1 [] Hsloc'
        · iapply lentPend_none rfl; iapply pendList_nil
        · iapply loanCom_none γ rfl
      isplitr
      · ipureintro
        rw [Htrm0]
        exact ⟨Hti1.1, Hti1.2.1⟩
      isplitr
      · ipureintro
        rw [Hpvoff.2.1, ← Hs0f.2.2.2.2.2.2.2.2.2.2.2.2.1]
        exact Hti1.2.2.2.1
      ipureintro
      refine ⟨(fun h => by rw [hsl] at h; cases h), fun l' h hd => ?_, fun hm => ?_⟩
      · rw [hsl] at h; cases h; rw [HCA, if_pos hd]
      · rw [HCA, if_neg (by rw [hm]; exact Bool.false_ne_true)]
  -- no snapshot `Ready`: the queue holds no snapshot acknowledgement, a non-empty one no restore
  have Hunp' : s.logst.unpersisted = [] := Hunp ▸ Hunp0 hsl
  ihave Hpend := lentPend_none_elim hsl _ $$ Hpend
  iclear Hret
  wp_auto
  rw [Hasync]
  wp_auto
  ihave %Hlen := BigSepL2.bigSepL2_length $$ Hpend
  ihave %Hsl := ownSlice_len _ _ _ $$ Hsteps
  -- the range construct's own counter `i_ptr` (Rocq's `j`) and the body's `i` share a
  -- Go name; rename the body's
  rename_i ibp
  irename: (ibp ↦ (_ : w64)) => ib
  ihave IH : iprop(∃ (n : w64) (s1 : NState) (steps1 : List Loc)
        (mv : Loc) (iv : w64) (ca : Nat),
      "i" ∷ i_ptr ↦ n ∗ "m" ∷ m_ptr ↦ mv ∗ "ib" ∷ ibp ↦ iv ∗
      "Hphys" ∷ ownRaftPhysCV cf cf.voters rnv.raft' id s1 ∗
      "Hghost" ∷ ownStepGhost γ (rs.mode.toG ⟨ca, rs.cfg, fp, ds⟩) cf id s1 ∗
      "Hsteps" ∷ rnv.stepsOnAdvance' ↦* steps1 ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (steps.length : Int)⌝ ∗
      "%Hsteps1" ∷ ⌜steps1.length = steps.length ∧
                    steps1.drop (sint.nat n) = steps.drop (sint.nat n)⌝ ∗
      "%Hwf1" ∷ ⌜NStateWf s1⌝ ∗
      "%Hs1" ∷ ⌜s1.logst.applying = s.logst.applying ∧
                s1.logst.unpersisted = s.logst.unpersisted ∧ s1.logst.snap = s.logst.snap ∧
                s1.logst.prev = s.logst.prev ∧ logStoreRec s1.logst = logStoreRec s.logst⌝ ∗
      "%Hsg1" ∷ ⌜s1.logst.storage = s.logst.storage ∧ s1.prevote = s.prevote ∧ s1.gh = s.gh⌝ ∗
      "%Hc1" ∷ ⌜uint.Z s.logst.committed ≤ uint.Z s1.logst.committed⌝ ∗
      "%Hca" ∷ ⌜rs.capplied ≤ ca ∧ ca ≤ max rs.capplied rs.delivered.length ∧
                (rs.mode = .static → ca = rs.capplied)⌝ ∗
      "%Hok1" ∷ ⌜StepsOk s1 (rs.steps.drop (sint.nat n))⌝ ∗
      "%Hsb1" ∷ ⌜SelfBound s (rs.steps.drop (sint.nat n))⌝ ∗
      "%Hti1" ∷ ⌜TermInv s s1 (rs.steps.drop (sint.nat n))⌝ ∗
      -- (D19i part 1) the floor kept, `applied` not moved back, and still short of `applying`
      -- only with an acknowledgement up to it ahead
      "%Hfl1" ∷ ⌜s1.logst.fl = s.logst.fl ∧ uint.Z s.logst.applied ≤ uint.Z s1.logst.applied ∧
        (uint.Z s1.logst.applied < uint.Z s.logst.applying →
          ∃ ce e, Pending.applyAck ce ∈ rs.steps.drop (sint.nat n) ∧ ce.getLast? = some e ∧
            uint.Z s.logst.applying ≤ uint.Z e.Index')⌝ ∗
      -- (2026-10-25, T-M M2b) a pre-candidate's campaign guard kept
      "%Hpg1" ∷ ⌜∀ fp, PreGuardF fp s → PreGuardF fp s1⌝ ∗
      -- (2026-10-28, stage U0) a node with a snapshot pending a follower
      "%Hsf1" ∷ ⌜SnapFol s1⌝ ∗
      "Hpend" ∷ pendList γ id (steps.drop (sint.nat n)) (rs.steps.drop (sint.nat n)))
    $$ [i m ib Hphys Hghost Hsteps Hpend]
  · iexists W64 0, s, steps, null, zero_val w64, rs.capplied
    have H0 : sint.nat (W64 0) = 0 := rfl
    rw [H0, List.drop_zero, List.drop_zero]
    simp only [named]
    iframe
    ipureintro
    refine ⟨by word, ⟨trivial, trivial⟩, Hwf, by simp, ⟨trivial, trivial, trivial⟩, Int.le_refl _,
      (by simp [Nat.le_max_left]),
      Hstok,
      stepsOk_selfBound s rs.steps Hstok, ⟨Int.le_refl _, by omega, fun _ _ => rfl,
      Hpvoff.2.2.1, Hpvoff.2.2.2.1⟩, ?_, fun _ h => h, Hpvoff.2.2.2.2⟩
    exact ⟨trivial, Int.le_refl _, Hrnfl.2⟩
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.Z n < sint.Z rnv.stepsOnAdvance'.len := by
      first | exact Hif | exact of_decide_eq_true (GoGlobalContext.intoVal_inj_bool Hif)
    clear Hif
    -- the next pending message
    list_elem steps (sint.nat n) as mm
    list_elem rs.steps (sint.nat n) as p
    -- no snapshot handed out, so no snapshot acknowledgement queued
    have Hnoack : ∀ t b e sn, p = .appendAck t b e sn → sn = none := by
      intro t b e sn hp
      cases sn with
      | none => rfl
      | some sv =>
        exfalso
        exact (Hloan.none_noack hsl).2 t b e sv (hp ▸ List.mem_of_getElem? Hp_lookup)
    have Hpmem : p ∈ rs.steps := List.mem_of_getElem? Hp_lookup
    have Hmm1 : steps1[sint.nat n]? = some mm := by
      have H := congrArg (fun l => l[0]?) Hsteps1.2
      simp only [List.getElem?_drop, Nat.add_zero] at H
      rw [H]; exact Hmm_lookup
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hn.1, Hlt⟩)]
    wp_apply (lc := 1) wp_load_slice_index rnv.stepsOnAdvance' (sint.Z n) steps1 (DFrac.own 1) mm Hn.1
      $$ [Hsteps] with Hsteps
    · iframe
      ipureintro
      exact Hmm1
    rw [drop_cons_of_lookup Hp_lookup] at Hok1 Hsb1 Hti1 Hfl1
    rw [drop_cons_of_lookup Hmm_lookup, drop_cons_of_lookup Hp_lookup]
    icases (BigSepL2.bigSepL2_cons (Φ := fun _ l p => iprop(∃ st, msgIn (GF := GF) l DFrac.discard st ∗
        pendingRel γ id st p))).1 $$ Hpend with ⟨⟨%st, Hmin, #Hpm⟩, Hpend⟩
    have HnS : sint.nat n + 1 = sint.nat (n + W64 1) := by word
    rw [HnS] at Hok1 Hsb1 Hti1 Hfl1 ⊢
    obtain ⟨Hpok, Hrest⟩ := stepsOk_cons _ _ _ Hok1
    -- a pre-candidate stepping its own pre-vote response is at `s`'s term
    have Hnw1 : ∀ pv t, p = .self pv t → s1.role = .preCandidate →
        uint.Z s1.term + 1 < 2 ^ 64 := by
      intro pv t _ hr
      have := Hti1.2.2.2.2 hr
      omega
    -- (D22 S-d3b) the acknowledgement's `StableOk`, at the state it is stepped at: with no restore
    -- since the `Ready`, by Log Matching with what the storage holds (`stableOk_of_stored`); after
    -- one, its miss (`stableHit_restored`, the restore's mark)
    ihave ⟨%Hack, Hghost⟩ : ⌜∀ t b e sn, p = .appendAck t b e sn → sn = none ∧
        ∀ x, e = some x → (t = W64 0 ∨ t = s1.term) → StableOk s1.logst x⌝ ∗
        ownStepGhost γ (rs.mode.toG ⟨ca, rs.cfg, fp, ds⟩) cf id s1 $$ [Hghost]
    · cases hp : p with
      | appendAck t b e sn =>
        have Hmem : Pending.appendAck t b e sn ∈ rs.steps := hp ▸ Hpmem
        have Hsn0 := Hnoack t b e sn hp
        subst Hsn0
        rw [hp] at Hpok
        have HpoS := stepsOk_ack Hstok Hmem
        icases Hstrecs $$ %t %b %e %none %Hmem with ⟨#Hr0, #Harm⟩
        iunfold ownStepGhost at Hghost
        icases Hghost with ⟨Hg, Hgr⟩
        unfold ackArm
        icases Harm with (⟨%Hp, -⟩ | ⟨%Hbp, #Hb⟩)
        · -- no restore: the boundary the `Ready`'s, no snapshot pending
          obtain ⟨Hpb, Hsnn⟩ := Hp
          ihave #Hr1 : storedRecs γ s1.logst.prev s1.logst.stored $$ []
          · rw [Hs1.2.2.2.1, logStoreRec_stored Hs1.2.2.2.2, Hpb]; iexact Hr0
          icases stableOk_of_stored γ id s1 _ rfl (by rw [Hs1.2.2.1]; exact Hsnn)
              (Hs1.2.1.trans Hunp') $$ Hr1 Hg with ⟨%Hsok, Hg⟩
          ihave Hghost : ownStepGhost γ (rs.mode.toG ⟨ca, rs.cfg, fp, ds⟩) cf id s1 $$ [Hg Hgr]
          · iunfold ownStepGhost; iframe Hg Hgr
          iframe Hghost
          ipureintro
          intro t' b' e' sn' h
          cases h
          refine ⟨rfl, fun x hx _ => ?_⟩
          rw [← (Hpok.2 x hx).1, ← Hpb, ← Hs1.2.2.2.1]
          exact Hsok
        · -- a restore since: the acknowledgement misses
          ihave ⟨%Hmiss0, Hg⟩ : ⌜e ≠ none ∧ s.term = t →
              ¬ StableHit s1.logst (plogLast b s1.logst.stored)⌝ ∗
              ownRaftGhost γ id (toPState s1) (rs.mode.toG ⟨ca, rs.cfg, fp, ds⟩).isDyn $$ [Hg]
          · by_cases hc : e ≠ none ∧ s.term = t
            · ihave #Hb' := Hb $$ %hc
              iunfold ackBaseW at Hb'
              icases Hb' with ⟨%H, -⟩
              ihave #Hr1 : storedRecs γ b s1.logst.stored $$ []
              · rw [logStoreRec_stored Hs1.2.2.2.2]; iexact Hr0
              icases stableHit_restored γ id s1 b (by rw [Hs1.2.2.2.1]; exact Hbp)
                  (by rw [Hs1.2.2.2.1, logStoreRec_stored Hs1.2.2.2.2]; exact H) $$ Hr1 Hg with ⟨%Hm, Hg⟩
              iframe Hg; ipureintro; exact fun _ => Hm
            · iframe Hg; ipureintro; exact fun h => absurd h hc
          ihave Hghost : ownStepGhost γ (rs.mode.toG ⟨ca, rs.cfg, fp, ds⟩) cf id s1 $$ [Hg Hgr]
          · iunfold ownStepGhost; iframe Hg Hgr
          iframe Hghost
          ipureintro
          intro t' b' e' sn' h
          cases h
          refine ⟨rfl, fun x hx ht Hhit => ?_⟩
          have h1 := Hpok.2 x hx
          have Htn : t = s1.term := ht.resolve_left (fun h => by have h2 := h1.2; rw [h] at h2; word)
          have Hst : s.term = t := ack_term_back HpoS.1 Hti1.1 Htn.symm
          rw [← h1.1] at Hhit
          exact absurd Hhit (Hmiss0 ⟨by rw [hx]; simp, Hst⟩)
      | self pv t =>
        iframe Hghost; ipureintro; intro _ _ _ _ h; cases h
      | applyAck ce =>
        iframe Hghost; ipureintro; intro _ _ _ _ h; cases h
    icases ownRaftPhysC_preFacts cf rnv.raft' id s1
        (RNMode.guard_of (fun h => Hpg1 fp (Hpvoff.1 h)) ca rs.cfg) $$ Hphys
      with ⟨%Hpf1, Hphys⟩
    icases ownRaftPhysC_logwf cf rnv.raft' id s1 $$ Hphys with ⟨%Hlw1, Hphys⟩
    -- A1 for the `MsgStorageApplyResp`, at the node's full log (dynamic mode)
    ihave Hres : (⌜∀ ce (m' : MessageM), p = .applyAck ce → m'.Type' = MsgStorageApplyResp →
        (rs.mode.toG ⟨ca, rs.cfg, fp, ds⟩).Pre m' ce s1⌝ ∗
        ownStepGhost γ (rs.mode.toG ⟨ca, rs.cfg, fp, ds⟩) cf id s1) $$ [Hghost]
    · cases hm : rs.mode with
      | static =>
        iframe Hghost
        ipureintro; intro _ _ _ _; trivial
      | dyn dec c0 h0 _ =>
        simp only [RNMode.toG]
        icases ownStepGhost_deliv γ dec c0 h0 ⟨ca, rs.cfg, fp, ds⟩ cf id s1 rs.delivered
          (by rw [Hdlen]; have := uint_Z_nonneg s.logst.applying; rw [← Hs1.1] at *; omega)
          $$ Hdeliv Hghost with ⟨%Hpre, Hghost⟩
        iframe Hghost
        ipureintro
        intro ce m' hp hty
        subst hp
        refine ⟨by have H := Hpf1.1; rw [hm] at H; exact H,
          fun _ e He => ?_,
          fun h => absurd (hty.symm.trans h) (by simp [MsgStorageApplyResp, MsgProp])⟩
        have He' := (Hpok e He).2
        rw [Hs1.1] at He'
        have HA := Ha1 (by rw [hm]; rfl)
        refine NoConfIn_prefix Hpre ?_ (HA.mono Hca.1 ?_)
        · have := uint_nat_eq e.Index'; rw [Hdlen]; omega
        · have := uint_nat_eq e.Index'; rw [Hdlen]; omega
    icases Hres with ⟨%Hpre1, Hghost⟩
    wp_apply wp_step_pending wp_raft_Step γ cf _ rnv.raft' id s1 mm st p Hwf1 Hpok Hal
      Hack (Hs1.2.1.trans Hunp') Hnw1
      (by rw [Hsg1.2.2, ← Hrs_unst]; exact Hunst0) Hpf1 Hpre1
      $$ [$Hphys $Hghost $Hmin $Hpm $Hlc1] as %err %s2 %md2 ⟨Hphys, Hghost, %Hst2⟩
    obtain ⟨Hwf2, Hout2, Hns2, Hna2, Ha2, Hu2, Hsn2, Ht2, Hps2, Hpv2, Hsd2, Hsg2, Hsg2', Hsg2'', Hrl2,
      Hpg2, Hfl2, Hap2, Hack2, Hsrb2, Hapa2⟩ := Hst2
    have Hsg2 := And.intro Hsg2 (And.intro Hsg2' Hsg2'')
    have Hc12 := Hout2.commit_mono
    obtain ⟨ca', rfl, Hca1, Hca2, Hca3, -⟩ := RNMode.stepOut_ca Hout2 Hns2 Hapa2
    icases ownRaftPhysC_logwf cf rnv.raft' id s2 $$ Hphys with ⟨%Hlw2, Hphys⟩
    -- `stepsOnAdvance[i] = nil`
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hn.1, Hlt⟩)]
    wp_apply wp_store_slice_index rnv.stepsOnAdvance' (sint.Z n) steps1 (null : Loc)
      $$ [Hsteps] with Hsteps
    · iframe
      ipureintro
      constructor <;> word
    wp_for_post
    iframe
    iexists n + W64 1, s2, steps1.set (sint.Z n).toNat (null : Loc), mm, n, ca'
    iframe
    ipureintro
    refine ⟨by word, ⟨by rw [List.length_set]; exact Hsteps1.1, ?_⟩, Hwf2,
      ⟨Ha2.trans Hs1.1, Hu2.trans Hs1.2.1, Hsn2.trans Hs1.2.2.1, Hpv2.trans Hs1.2.2.2.1,
        Hsd2.trans Hs1.2.2.2.2⟩,
      ⟨Hsg2.1.trans Hsg1.1, Hsg2.2.1.trans Hsg1.2.1, Hsg2.2.2.trans Hsg1.2.2⟩,
      Int.le_trans Hc1 Hc12,
      ⟨Nat.le_trans Hca.1 Hca1, ?_, fun h => (Hca3 h).trans (Hca.2.2 h)⟩,
      stepsOk_mono_le s1 s2 _ Ht2 ⟨Hpv2, logStoreRec_stored Hsd2⟩ Hc12 Ha2 (tc_le_of_gh Hsg2.2.2) Hrest,
      fun pv t h => Hsb1 pv t (List.mem_cons_of_mem _ h),
      termInv_step s s1 s2 p _ Hok1 Hsb1 Hti1 Ht2 Hps2 Hrl2,
      ⟨Hfl2.trans Hfl1.1, Int.le_trans Hfl1.2.1 Hap2, ?_⟩, fun fp h => Hpg2 fp (Hpg1 fp h),
      Hsf1.step Hsrb2⟩
    · rw [← HnS, List.drop_set_of_lt (by simp [sint.nat]), ← List.drop_drop, ← List.drop_drop,
        Hsteps1.2]
    · -- the configuration index stays at most the committed log handed out
      clear Hack2 Hfl1 Hfl2 Hap2
      have Happ2 : uint.Z s2.logst.applied ≤ uint.Z s.logst.applying := by
        rw [← Hs1.1, ← Ha2]; exact Hlw2.1
      have := uint_nat_eq s2.logst.applied
      have := uint_Z_nonneg s.logst.applying
      have Hd : (rs.delivered.length : Int) = uint.Z s.logst.applying := by rw [Hdlen]; omega
      omega
    · -- (D19i part 1) the acknowledgement ahead is not `p`'s, or `p` moved `applied` past it
      intro hlt
      obtain ⟨ce, e, Hm, He, Hle⟩ := Hfl1.2.2 (Int.lt_of_le_of_lt Hap2 hlt)
      rcases List.mem_cons.1 Hm with Hm | Hm
      · exact absurd (Hack2 ce Hm.symm e He) (by omega)
      · exact ⟨ce, e, Hm, He, Hle⟩
  · -- the loop is done: `stepsOnAdvance = stepsOnAdvance[:0]`
    have Hif' : ¬ sint.Z n < sint.Z rnv.stepsOnAdvance'.len := by
      first | exact Hif | exact fun h => Hif (by rw [decide_eq_true h])
    clear Hif
    try (rw [if_pos (decide_eq_true (by rw [decide_eq_false Hif'] :
      (#(decide (sint.Z n < sint.Z rnv.stepsOnAdvance'.len)) : val) = #false))]; wp_auto)
    ihave %Hwfs := ownSlice_wf _ _ _ $$ Hsteps
    rw [ite_eq_left_of_eq_true _ _ (eq_true (slice00_ok Hwfs).1)]
    wp_auto
    icases (ownSlice_slice (W64 0) (W64 0) _ _ _ (slice00_ok Hwfs).2).1 $$ Hsteps
      with ⟨-, Hsl0, Hrest⟩
    ihave Hcap0 := ownSlice_slice_absorb_capacity _ _ (W64 0) (W64 0) (slice00_ok Hwfs).2
      $$ [$Hrest $Hsteps_cap]
    have Hsub : subslice (sint.nat (W64 0)) (sint.nat (W64 0)) steps1 = [] := by
      simp [subslice]
    rw [Hsub]
    ihave #Hstr1 : ackInv γ { rs with steps := [], term := s1.term, capplied := ca, flw := false } s1
        $$ []
    · iapply ackInv_none; intro _ _ _ _ h; cases h
    -- (D19i part 1) the queue stepped, `applied` is at least `applying`, so at least the floor
    have Hdrop : rs.steps.drop (sint.nat n) = [] := by
      apply List.drop_eq_nil_of_le
      have := loop_done_nat Hif' Hn Hsl.1 Hsl.2
      rw [← Hlen]
      omega
    icases ownRaftPhysC_log_same cf rnv.raft' id s1 $$ Hphys with ⟨Hlog1, Hback1⟩
    icases ownRaftLog_fl _ _ $$ Hlog1 with ⟨%Hflb1, Hlog1⟩
    ihave Hphys := Hback1 $$ Hlog1
    have Hge : uint.Z s.logst.applying ≤ uint.Z s1.logst.applied := by
      apply Int.not_lt.1
      intro h
      obtain ⟨_, _, Hm, -⟩ := Hfl1.2.2 h
      rw [Hdrop] at Hm
      simp at Hm
    have HrnflA : RNFl { rs with steps := [], term := s1.term, capplied := ca, flw := false } s1 :=
      ⟨fun _ => by have := Hflb1.1; rw [Hs1.1] at this; omega,
       fun h => absurd Hge (by rw [Hs1.1] at h; omega)⟩
    have HloanA : LoanOk { rs with steps := [], term := s1.term, capplied := ca, flw := false } s1 :=
      ⟨by rw [Hsg1.2.2]; exact Hloan.1, fun h => ⟨by rw [Hsg1.2.2]; exact (Hloan.2.1 h).1,
        fun _ _ _ _ h => (by cases h)⟩, fun l h => (by simp only at h; rw [hsl] at h; cases h)⟩
    ihave #Hsloc' := snapLocOk_keep γ id (.inl Hs1.2.2.1) $$ Hsloc
    iapply HΦ $$ %s1.term %ca
    rw [advRS_none s1.term ca hsl]
    isplitl
    · iapply ownRawNode_intro γ rn id
        { rs with steps := [], term := s1.term, capplied := ca, flw := false } s1
        cf fp
        { rnv with stepsOnAdvance' :=
            slice.slice rnv.stepsOnAdvance' Loc (W64 0) (W64 0) }
        sv hprev [] Hwf1 Hin Hal Hasync (by rw [Hs1.1]; exact Hdlen) (by rw [Hs1.2.1]; exact Hunp)
        (fun h => by rw [Hs1.2.2.1]; exact Hsnap h) trivial rfl (by rw [Hsg1.1]; exact Hstor)
        ⟨fun h => Hpg1 fp (Hpvoff.1 h), by rw [Hsg1.2.2]; exact Hpvoff.2.1,
          by rw [Hsg1.2.2]; exact Hti1.2.2.2.1, fun h => by rw [Hsg1.2.2]; exact Hti1.2.2.2.2 h, Hsf1⟩
        (by rw [Hsg1.2.2]; exact Hrs_out)
        (by rw [Hsg1.2.2]; exact Hrs_unst) (Int.le_trans Hrs_clb Hc1) HrnflA HloanA
        (Hsdt.ofRec Hs1.2.2.1 Hs1.2.2.2.2)
        $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsl0 Hcap0 [] Hdeliv Hstr1 Hloanc Hsloc'
      · iapply lentPend_none hsl; iapply pendList_nil
    isplitr
    · ipureintro
      rw [Htrm]
      exact ⟨Hti1.1, Hti1.2.1⟩
    isplitr
    · ipureintro
      rw [Hpvoff.2.1]
      exact Hti1.2.2.2.1
    ipureintro
    exact ⟨fun _ => ⟨Hca.1, Hca.2.1⟩, (fun l (h : rs.slent = some l) => by rw [hsl] at h; cases h),
      Hca.2.2⟩

end proof

end EtcdGrove
end Perennial
