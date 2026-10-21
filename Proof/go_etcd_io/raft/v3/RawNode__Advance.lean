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
variable [FfiSyntax]

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
    | appendAck tm e =>
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
  | appendAck tm e =>
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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
    (Hsnap : s.logst.snap = none) (Hunp : s.logst.unpersisted = [])
    (Hnw : ∀ pv t, p = .self pv t → s.role = .preCandidate → uint.Z s.term + 1 < 2 ^ 64)
    (Hghoff : s.gh.unst = false) (Hpf : PreFacts md.isDyn s)
    (Hpre : ∀ ce (m' : MessageM), p = .applyAck ce → m'.Type' = MsgStorageApplyResp →
      md.Pre m' ce s) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhysCV c c.voters r id s ∗
        ownStepGhost γ md c id s ∗ msgIn ml DFrac.discard st ∗ pendingRel γ id st p ∗
        storedRecs γ s.logst.prev s.logst.stored ∗ £ 1 }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #ml))
    {{ (err : GoInterface) (s' : NState) (md' : GMode), RET #err;
        ownRaftPhysCV c c.voters r id s' ∗ ownStepGhost γ md' c id s' ∗
        ⌜NStateWf s' ∧ md.StepOut c id st.msg s s' md' ∧ st.msg.Type' ≠ MsgSnap ∧
         ((∀ ce, p ≠ .applyAck ce) → st.msg.Type' ≠ MsgStorageApplyResp) ∧
         s'.logst.applying = s.logst.applying ∧
         s'.logst.unpersisted = s.logst.unpersisted ∧ s'.logst.snap = s.logst.snap ∧
         uint.Z s.term ≤ uint.Z s'.term ∧
         PendStep p s s' ∧
         s'.logst.prev = s.logst.prev ∧ s'.logst.stored = s.logst.stored ∧
         s'.logst.storage = s.logst.storage ∧ s'.prevote = s.prevote ∧ s'.gh = s.gh ∧
         -- (2026-10-17) no message of the queue makes a pre-candidate (`PreCandStep`)
         (s'.role = .preCandidate → s.role = .preCandidate ∧ s'.term = s.term) ∧
         -- (D19i part 1) the floor kept, `applied` not moved back, and moved up to an apply
         -- acknowledgement's last entry
         s'.logst.fl = s.logst.fl ∧ uint.Z s.logst.applied ≤ uint.Z s'.logst.applied ∧
         (∀ ce, p = .applyAck ce → ∀ e, ce.getLast? = some e →
            uint.Z e.Index' ≤ uint.Z s'.logst.applied)⌝ }} := by
  iintro %Φ ⟨#Hinit, Hphys, Hghost, Hmin, #Hp, #Hstr, Hlc⟩ HΦ
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
      have e2 := Hcc (by not_self); subst c'
      have Hfr' := Hframe (by not_self) (by not_self)
      have Htm := Hterm (by not_self)
      iapply HΦ $$ %err %s' %md'
      iframe Hphys Hghost
      ipureintro
      refine ⟨Hwf', Hstp, by not_self, fun _ => by not_self, Hfr'.1, Hfr'.2.2.1, Hfr'.2.1, Htm.1, ?_,
        Hfr'.2.2.2.1, Hfr'.2.2.2.2.1, Hfr'.2.2.2.2.2.1, Hfr'.2.2.2.2.2.2.1, Hfr'.2.2.2.2.2.2.2.1, ?role,
        Hfr'.2.2.2.2.2.2.2.2.1, Hfr'.2.2.2.2.2.2.2.2.2, fun _ h => by cases h⟩
      case role =>
        intro h
        obtain ⟨Ht, Hor⟩ := Htm.2.2.2.2.2 h
        exact ⟨Hor.resolve_right (by not_self), Ht⟩
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
  | appendAck t e =>
    unfold pendingRel
    icases Hp with ⟨%Hm, -⟩
    have Hm' : st = _ := Hm
    subst Hm'
    obtain ⟨Hle, Hlast⟩ := Hok
    iunfold ownStepGhost at Hghost
    icases Hghost with ⟨Hghost, Hrest⟩
    icases stableOk_of_stored γ id s e Hlast Hsnap Hunp $$ Hstr Hghost
      with ⟨%Hsok, Hghost⟩
    ihave Hghost : ownStepGhost γ md c id s $$ [Hghost Hrest]
    · iunfold ownStepGhost; iframe Hghost Hrest
    iapply wp_raft_Step c md γ r id s ml (appendAckM id t e) [] [] none []
      (by simp [StepMsg, stepMsgTypes, appendAckM])
      (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne)
      (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne)
      (fun _ => ⟨rfl, Hle, fun _ _ => Hsok, Hghoff⟩) (by msg_ne) (by msg_ne) (by msg_ne)
      (by msg_ne)
      (RestMsgOk.of_ne ⟨by msg_ne, by msg_ne, by msg_ne, by msg_ne, by msg_ne⟩) Hwf
      (GMode.Pre.of_facts Hpf (by msg_ne) (by msg_ne)) (fun h => absurd h (by msg_ne))
      $$ [$Hinit $Hphys $Hghost $Hlc Hmin Hcr]
    · have hP : (appendAckM id t e).Type' ≠ MsgProp := by msg_ne
      simp only [hP, ↓reduceIte, named]
      have Hty0 : mtypeOf (appendAckM id t e).Type' = none := rfl
      isplitl [Hmin]
      · isplitl [Hmin]
        · iexact Hmin
        isplitr
        · iempintro
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
      iintro %err %s' %c' %md' ⟨Hphys, Hghost, %Hwf', %Hstp, %Hcc, %Hloc, -⟩
      have e2 := Hcc (by msg_ne); subst c'
      obtain ⟨Hfr, Hap, -⟩ := Hloc (.inr (.inl rfl))
      iapply HΦ $$ %err %s' %md'
      iframe Hphys Hghost
      ipureintro
      exact ⟨Hwf', Hstp, by msg_ne, fun _ => by msg_ne, Hap (fun Hc => absurd Hc (by msg_ne)), Hfr.2.2.1,
        Hfr.2.2.2.1, by rw [Hfr.1]; exact Int.le_refl _, Hfr.1, Hfr.2.2.2.2.1, Hfr.2.2.2.2.2.1,
        Hfr.2.2.2.2.2.2.1, Hfr.2.2.2.2.2.2.2.1, Hfr.2.2.2.2.2.2.2.2.1,
        fun h => ⟨by rw [← Hfr.2.2.2.2.2.2.2.2.2.1]; exact h, Hfr.1⟩,
        Hfr.2.2.2.2.2.2.2.2.2.2.1, Hfr.2.2.2.2.2.2.2.2.2.2.2, fun _ h => by cases h⟩
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
      iintro %err %s' %c' %md' ⟨Hphys, Hghost, %Hwf', %Hstp, %Hcc, %Hloc, -⟩
      have e2 := Hcc (by msg_ne); subst c'
      obtain ⟨Hfr, Hap, Happ⟩ := Hloc (.inr (.inr rfl))
      iapply HΦ $$ %err %s' %md'
      iframe Hphys Hghost
      ipureintro
      exact ⟨Hwf', Hstp, by msg_ne, fun h => absurd rfl (h ce), Hap (fun _ e He => (Hok e He).2), Hfr.2.2.1,
        Hfr.2.2.2.1, by rw [Hfr.1]; exact Int.le_refl _, Hfr.1, Hfr.2.2.2.2.1, Hfr.2.2.2.2.2.1,
        Hfr.2.2.2.2.2.2.1, Hfr.2.2.2.2.2.2.2.1, Hfr.2.2.2.2.2.2.2.2.1,
        fun h => ⟨by rw [← Hfr.2.2.2.2.2.2.2.2.2.1]; exact h, Hfr.1⟩,
        Hfr.2.2.2.2.2.2.2.2.2.2.1, Hfr.2.2.2.2.2.2.2.2.2.2.2,
        fun ce' h => by injection h with h; subst h; exact Happ rfl⟩

theorem RawNode.Advance.wp_proof
    (wp_raft_Step : raft.Step.spec (GF := GF) (hG := hG)) :
    RawNode.Advance.spec (GF := GF) (hG := hG) := by
  intro γ rn id rs rd Hunp0 Hunst0 Ha1
  wp_start as H
  iNamed H
  iNamed Hrn
  have Hunp' : s.logst.unpersisted = [] := Hunp ▸ Hunp0
  have Htcb : uint.Z s.gh.tc < 2 ^ 64 := by word
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
      "Hghost" ∷ ownStepGhost γ (rs.mode.toG ⟨ca, rs.cfg, fp⟩) cf id s1 ∗
      "Hsteps" ∷ rnv.stepsOnAdvance' ↦* steps1 ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (steps.length : Int)⌝ ∗
      "%Hsteps1" ∷ ⌜steps1.length = steps.length ∧
                    steps1.drop (sint.nat n) = steps.drop (sint.nat n)⌝ ∗
      "%Hwf1" ∷ ⌜NStateWf s1⌝ ∗
      "%Hs1" ∷ ⌜s1.logst.applying = s.logst.applying ∧
                s1.logst.unpersisted = s.logst.unpersisted ∧ s1.logst.snap = s.logst.snap ∧
                s1.logst.prev = s.logst.prev ∧ s1.logst.stored = s.logst.stored⌝ ∗
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
      Hpvoff.2.2.1, Hpvoff.2.2.2⟩, ?_⟩
    exact ⟨trivial, Int.le_refl _, Hrnfl.2⟩
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.Z n < sint.Z rnv.stepsOnAdvance'.len := Hif
    clear Hif
    -- the next pending message
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
    ihave #Hstr1 := storedRecs_eq γ _ s1.logst.prev _ s1.logst.stored Hs1.2.2.2.1 Hs1.2.2.2.2
      $$ Hstrecs
    icases ownRaftPhysC_preFacts cf rnv.raft' id s1
        (fun h => by rw [Hsg1.2.1]; exact Hpvoff.dyn ⟨ca, rs.cfg, fp⟩ h) $$ Hphys
      with ⟨%Hpf1, Hphys⟩
    icases ownRaftPhysC_logwf cf rnv.raft' id s1 $$ Hphys with ⟨%Hlw1, Hphys⟩
    -- A1 for the `MsgStorageApplyResp`, at the node's full log (dynamic mode)
    ihave Hres : (⌜∀ ce (m' : MessageM), p = .applyAck ce → m'.Type' = MsgStorageApplyResp →
        (rs.mode.toG ⟨ca, rs.cfg, fp⟩).Pre m' ce s1⌝ ∗
        ownStepGhost γ (rs.mode.toG ⟨ca, rs.cfg, fp⟩) cf id s1) $$ [Hghost]
    · cases hm : rs.mode with
      | static =>
        iframe Hghost
        ipureintro; intro _ _ _ _; trivial
      | dyn dec c0 h0 _ =>
        simp only [RNMode.toG]
        icases ownStepGhost_deliv γ dec c0 h0 ⟨ca, rs.cfg, fp⟩ cf id s1 rs.delivered
          (by rw [Hdlen]; have := uint_Z_nonneg s.logst.applying; rw [← Hs1.1] at *; omega)
          $$ Hdeliv Hghost with ⟨%Hpre, Hghost⟩
        iframe Hghost
        ipureintro
        intro ce m' hp hty
        subst hp
        refine ⟨Hpf1.1 (by rw [hm]; rfl),
          fun _ => ⟨Hs1.2.2.1.trans Hsnap, fun e He => ?_⟩,
          fun h => absurd (hty.symm.trans h) (by simp [MsgStorageApplyResp, MsgProp])⟩
        have He' := (Hpok e He).2
        rw [Hs1.1] at He'
        have HA := Ha1 (by rw [hm]; rfl)
        refine NoConfIn_prefix Hpre ?_ (HA.mono Hca.1 ?_)
        · have := uint_nat_eq e.Index'; rw [Hdlen]; omega
        · have := uint_nat_eq e.Index'; rw [Hdlen]; omega
    icases Hres with ⟨%Hpre1, Hghost⟩
    wp_apply wp_step_pending wp_raft_Step γ cf _ rnv.raft' id s1 mm st p Hwf1 Hpok Hal
      (Hs1.2.2.1.trans Hsnap) (Hs1.2.1.trans Hunp') Hnw1
      (by rw [Hsg1.2.2, ← Hrs_unst]; exact Hunst0) Hpf1 Hpre1
      $$ [$Hphys $Hghost $Hmin $Hpm $Hstr1 $Hlc1] as %err %s2 %md2 ⟨Hphys, Hghost, %Hst2⟩
    obtain ⟨Hwf2, Hout2, Hns2, Hna2, Ha2, Hu2, Hsn2, Ht2, Hps2, Hpv2, Hsd2, Hsg2, Hsg2', Hsg2'', Hrl2,
      Hfl2, Hap2, Hack2⟩ := Hst2
    have Hsg2 := And.intro Hsg2 (And.intro Hsg2' Hsg2'')
    have Hc12 := Hout2.commit_mono
    obtain ⟨ca', rfl, Hca1, Hca2, Hca3, -⟩ := RNMode.stepOut_ca Hout2 Hns2
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
      stepsOk_mono_le s1 s2 _ Ht2 ⟨Hpv2, Hsd2⟩ Hc12 Ha2 (tc_le_of_gh Hsg2.2.2) Hrest,
      fun pv t h => Hsb1 pv t (List.mem_cons_of_mem _ h),
      termInv_step s s1 s2 p _ Hok1 Hsb1 Hti1 Ht2 Hps2 Hrl2,
      Hfl2.trans Hfl1.1, Int.le_trans Hfl1.2.1 Hap2, ?_⟩
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
    ihave %Hwfs := ownSlice_wf _ _ _ $$ Hsteps
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by word))]
    wp_auto
    icases (ownSlice_slice (W64 0) (W64 0) _ _ _ (by word)).1 $$ Hsteps with ⟨-, Hsl0, Hrest⟩
    ihave Hcap0 := ownSlice_slice_absorb_capacity _ _ (W64 0) (W64 0) (by word)
      $$ [$Hrest $Hsteps_cap]
    have Hsub : subslice (sint.nat (W64 0)) (sint.nat (W64 0)) steps1 = [] := by
      simp [subslice]
    rw [Hsub]
    ihave #Hstr1 := storedRecs_eq γ _ s1.logst.prev _ s1.logst.stored Hs1.2.2.2.1 Hs1.2.2.2.2
      $$ Hstrecs
    -- (D19i part 1) the queue stepped, `applied` is at least `applying`, so at least the floor
    have Hdrop : rs.steps.drop (sint.nat n) = [] := by
      apply List.drop_eq_nil_of_le
      have := Hsteps1.1
      rw [← Hlen]
      word
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
    iapply HΦ $$ %s1.term %ca
    isplitl
    · iapply ownRawNode_intro γ rn id
        { rs with steps := [], term := s1.term, capplied := ca, flw := false } s1
        cf fp
        { rnv with stepsOnAdvance' :=
            slice.slice rnv.stepsOnAdvance' Loc (W64 0) (W64 0) }
        sv hprev [] Hwf1 Hin Hal Hasync (by rw [Hs1.1]; exact Hdlen) (by rw [Hs1.2.1]; exact Hunp)
        (by rw [Hs1.2.2.1]; exact Hsnap) trivial rfl (by rw [Hsg1.1]; exact Hstor)
        ⟨fun h => by rw [Hsg1.2.1]; exact Hpvoff.1 h, by rw [Hsg1.2.2]; exact Hpvoff.2.1,
          by rw [Hsg1.2.2]; exact Hti1.2.2.2.1, fun h => by rw [Hsg1.2.2]; exact Hti1.2.2.2.2 h⟩
        (by rw [Hsg1.2.2]; exact Hrs_out)
        (by rw [Hsg1.2.2]; exact Hrs_unst) (Int.le_trans Hrs_clb Hc1) HrnflA
        $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsl0 Hcap0 [] Hdeliv Hstr1
      · iapply pendList_nil
    isplitr
    · ipureintro
      rw [Htrm]
      exact ⟨Hti1.1, Hti1.2.1⟩
    isplitr
    · ipureintro
      rw [Hpvoff.2.1]
      exact Hti1.2.2.2.1
    ipureintro; exact Hca

end proof

end EtcdGrove
end Perennial
