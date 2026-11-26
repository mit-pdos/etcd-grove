-- The copy for the part `KvNet/` of `RaftNoAx/Proof/go_etcd_io/raft/v3/AdvanceAbsStep.lean` (etc/copy-part.py; rerun it, do not edit).
/-
#33 S4 (P-raft-3), `notes/antithesis-rawnode-design.md` §2.2, §2.7. **One queued message of
`RawNode.Advance` in the harness's scope, its end state kept**: `wp_step_pending_ns`, the untraced
`wp_step_pending` of `TracedRawNodeAdvance.lean` (its post, conjunct for conjunct) through `raft.Step`'s
instance at the no-snapshot flag (`raft.Step.untracedNs`, `RaftStepNoSnap.lean`), whose post adds the
end state (`StepEnd`, `AckEnd`) and the outbox's having no `MsgSnap`. Its premises beyond the untraced
one's are the scope's: the storage never compacted, the log's boundary at `0`, no `MsgSnap` queued, no
automatic leave (`AckScope`).

With the loop's term bookkeeping (`AdvAbs.SelfStep`, `PendStep`, `SelfBound`, `TermInv`), restated from
`TracedRawNodeAdvance.lean`, where they are private, and the log's persistence invariant read out
(`ownRaftPhysC_ipStored`: the log up to the in-progress boundary is a prefix of what the storage holds),
which bounds the in-progress boundary after the queue (`RawNode__AdvanceAbs.lean`).
-/
module

public import KvNet.Proof.go_etcd_io.raft.v3.TracedRawNodeAdvance
public import KvNet.Proof.go_etcd_io.raft.v3.RaftStepNoSnap
import all KvNet.Proof.go_etcd_io.raft.v3.InvRaftlog

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3
open RawNodeOwnAccess

namespace AdvAbs

theorem drop_cons_of_lookup {α : Type _} {l : List α} {k : Nat} {x : α}
    (h : l[k]? = some x) : l.drop k = x :: l.drop (k + 1) := by
  obtain ⟨hk, rfl⟩ := List.getElem?_eq_some_iff.1 h
  exact List.drop_eq_getElem_cons hk

section terms
variable [GooseExts]

/-- What stepping a self-addressed response of term `t` (a pre-vote response if `pv`)
does to the node's term and role (`TracedRawNodeAdvance.lean`'s). -/
def SelfStep (pv : Bool) (t : w64) (s s' : NState) : Prop :=
  (pv = false → uint.Z s'.term ≤ max (uint.Z s.term) (uint.Z t) ∧
      (uint.Z t < uint.Z s.term → s'.role = s.role)) ∧
  (pv = true → (uint.Z s'.term ≤ max (uint.Z s.term) (uint.Z t) ∨
        (s.role = .preCandidate ∧ uint.Z s'.term = uint.Z s.term + 1)) ∧
      (s'.role = .preCandidate → s.role = .preCandidate ∧ s'.term = s.term))

/-- What one pending step does to the term. -/
def PendStep (p : Pending) (s s' : NState) : Prop :=
  match p with
  | .self pv t => SelfStep pv t s s'
  | _ => s'.term = s.term

/-- The self-addressed responses of a queue are no later than `s`'s term (one later for
a pre-vote response). -/
def SelfBound (s : NState) (rest : List Pending) : Prop :=
  ∀ pv t, Pending.self pv t ∈ rest → uint.Z t ≤ uint.Z s.term + (if pv then 1 else 0) ∧
    (pv = true → uint.Z t ≤ uint.Z s.gh.tc)

/-- The loop's term invariant. -/
def TermInv (s s1 : NState) (rest : List Pending) : Prop :=
  uint.Z s.term ≤ uint.Z s1.term ∧ uint.Z s1.term ≤ uint.Z s.term + 1 ∧
  ((∃ pv t, Pending.self pv t ∈ rest) → s1.role = .preCandidate →
    uint.Z s1.term = uint.Z s.term) ∧
  uint.Z s1.term ≤ uint.Z s.gh.tc ∧
  (s1.role = .preCandidate → uint.Z s1.term + 1 ≤ uint.Z s.gh.tc)

theorem stepsOk_selfBound (s : NState) (l : List Pending) :
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

theorem termInv_step (s s1 s2 : NState) (p : Pending) (rest : List Pending)
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

/-- The bounds of `stepsOnAdvance[:0]`. -/
theorem slice00_ok {l c : w64} (h : 0 ≤ sint.Z l ∧ sint.Z l ≤ sint.Z c) :
    (0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z c) ∧
    (0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z l) := by
  word

/-- The loop's counter at its end: the slice's length. -/
theorem loop_done_nat {n len : w64} {k : Nat} (h1 : ¬ sint.Z n < sint.Z len)
    (h2 : 0 ≤ sint.Z n ∧ sint.Z n ≤ (k : Int)) (h3 : k = sint.nat len) (h4 : 0 ≤ sint.Z len) :
    sint.nat n = k := by
  word

end terms

end AdvAbs

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **The log up to the in-progress boundary is a prefix of what the storage holds** (with no snapshot
pending: the persistence invariant's first conjunct, `LogPersistOk`, the pending batch appended being
the ghost `stored`). -/
theorem ownRaftLog_ipStored (l : Loc) (ls : LogState) :
    ⊢ ownRaftLog (GF := GF) l ls -∗
      ⌜ls.snap = none →
        (ls.sents ++ ls.uents).take ((uint.Z ls.inprogress - uint.Z ls.prev.index' - 1).toNat) <+:
          ls.stored⌝ ∗
      ownRaftLog l ls := by
  iintro H0
  iNamed H0
  isplitr
  · ipureintro
    intro hsn
    obtain ⟨Hp1, -, -, Hp4⟩ := Hpersist hsn
    rw [← Hp4]
    have Hk : (uint.Z ls.inprogress - uint.Z ls.prev.index' - 1).toNat =
        ls.sents.length + (uint.Z ls.inprogress - uint.Z lv.unstable'.offset').toNat := by
      omega
    rw [Hk, List.take_append, List.take_of_length_le (by omega), Nat.add_sub_cancel_left]
    exact Hp1
  · iapply ownRaftLog_intro (sn := ls.sn) l lv lv.storage' σ _ _ ls rfl Hcm Hap Hidx Hnowrap Hstore Hoffset
      Happlied Hpapplied Hcommitted Hapg Hip Hipb Hpersist Happlying
      Hpaused Hasz Hamx Hstor Hpend Hfl Hsip Hsipn Hlent Hq Hprel Hsat Hfr rfl rfl rfl rfl rfl $$ Hl HisStorage HStorage Husnap Hpksn Hkcert Huents Huents_cap Hl_logger
      Hu_logger

/-- The dynamic mode's invariant (`RInv`), read off the ghost state (`TracedRawNodeAdvance.lean`'s). -/
theorem AdvAbs.ownStepGhost_rinv (γ : RaftNames) (dec : CCDec) (c0 : CCState) (h0 : CfgOk c0)
    (g : RGh) (c : CfgM) (id : w64) (s : NState) :
    ownStepGhost (GF := GF) γ (.dyn dec c0 h0 g) c id s ⊢
      ⌜RInv (effDec dec g.decs) c0 (rOf s g)⌝ ∗ ownStepGhost γ (.dyn dec c0 h0 g) c id s := by
  iintro H
  iunfold ownStepGhost at H
  icases H with ⟨Hg, Hr⟩
  iunfold ghostRest at Hr
  icases Hr with ⟨%Hnl, Hr, #Hcl⟩
  simp only [ghostRestM]
  icases Hr with ⟨%HC, #HM, #Hfr⟩
  isplitr
  · ipureintro; exact HC.2.2
  iunfold ownStepGhost
  iframe Hg
  iunfold ghostRest
  isplitr
  · ipureintro; exact Hnl
  iframe Hcl
  simp only [ghostRestM]
  iframe Hfr HM
  ipureintro; exact HC

/-- Dynamically, `applied` is within the configuration index (`RInv`'s `applied_cidx`). -/
theorem AdvAbs.ownStepGhost_applied_le (γ : RaftNames) (md : RNMode) (g : RGh) (c : CfgM) (id : w64)
    (s : NState) :
    ownStepGhost (GF := GF) γ (md.toG g) c id s ⊢
      ⌜md.isDyn = true → uint.nat s.logst.applied ≤ g.cidx⌝ ∗ ownStepGhost γ (md.toG g) c id s := by
  cases md with
  | static => iintro H; iframe H; ipureintro; intro h; cases h
  | dyn dec c0 h0 h1 =>
    simp only [RNMode.toG]
    iintro H
    icases AdvAbs.ownStepGhost_rinv γ dec c0 h0 g c id s $$ H with ⟨%HI, H⟩
    iframe H; ipureintro; intro _; exact HI.applied_cidx

/-- `ownRaftLog_ipStored`, read through the struct. -/
theorem ownRaftPhysC_ipStored (c : CfgM) {V : GSet w64} (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhysCV (GF := GF) c V r id s -∗
      ⌜s.logst.snap = none →
        (s.logst.sents ++ s.logst.uents).take
          ((uint.Z s.logst.inprogress - uint.Z s.logst.prev.index' - 1).toNat) <+: s.logst.stored⌝ ∗
      ownRaftPhysCV c V r id s := by
  iintro H
  icases ownRaftPhysC_log_same c r id s $$ H with ⟨Hlog, Hback⟩
  icases ownRaftLog_ipStored _ _ $$ Hlog with ⟨%Hw, Hlog⟩
  ihave H := Hback $$ Hlog
  iframe H
  ipureintro; exact Hw

end ghost

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
/-- A premise of `Step` about a type a self-addressed response (`Hty`) is not: vacuous. -/
local macro "not_self" : tactic => `(tactic| (
  intro Hc
  first
  | exact Hc.elim
  | (exfalso
     rcases Hty with Hty | Hty | Hty <;> rw [Hty] at Hc <;>
       simp [MsgHup, MsgVote, MsgVoteResp, MsgPreVote, MsgPreVoteResp, MsgApp, MsgHeartbeat,
         MsgAppResp, MsgHeartbeatResp,MsgCheckQuorum, MsgSnap, MsgBeat, MsgProp, MsgStorageAppendResp,
         MsgStorageApplyResp, MsgReadIndex, MsgReadIndexResp, MsgForgetLeader, MsgUnreachable, MsgSnapStatus, MsgTimeoutNow, MsgTransferLeader] at Hc)))

/-- **One pending message through `raft.Step` at the no-snapshot flag** (`TracedRawNodeAdvance.lean`'s
untraced `wp_step_pending`, through `raft.Step.untracedNs`): its post, and the end state (`StepEnd`,
`AckEnd`) with the outbox's having no `MsgSnap`. -/
theorem wp_step_pending_ns
    (wp_raft_Step : raft.Step.spec (GF := GF) (hG := hG))
    (γ : RaftNames) (c : CfgM) (md : GMode) (r : Loc) (id : w64) (s : NState)
    (ml : Loc) (st : MsgSt) (p : Pending) (W : DurMaps)
    (Hwf : NStateWf s) (Hok : PendingOk s p)
    (Hack : ∀ t b e sn, p = .appendAck t b e sn → sn = none ∧
      ∀ x, e = some x → (t = W64 0 ∨ t = s.term) → StableOk s.logst x)
    (Hunp : s.logst.unpersisted = [])
    (Hnw : ∀ pv t, p = .self pv t → s.role = .preCandidate → uint.Z s.term + 1 < 2 ^ 64)
    (Hghoff : s.gh.unst = false) (Hpf : PreFacts md s)
    (Hpre : ∀ ce (m' : MessageM), p = .applyAck ce → m'.Type' = MsgStorageApplyResp →
      md.Pre m' ce s)
    (Htr : s.gh.tr = none) (Hal : AckScope c)
    (Hprev0 : uint.Z s.logst.prev.index' = 0) (Hns0 : NoSnapL s.outbox) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhysCV c c.voters r id s ∗
        ownStepGhost γ md c id s ∗ msgIn ml DFrac.discard st ∗ pendingRel γ id W st p ∗ £ 1 ∗
        durFrags γ id W ∗ storCapF s.logst.storage 0 }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #ml))
    {{ (err : GoInterface) (s' : NState) (md' : GMode), RET #err;
        ownRaftPhysCV c c.voters r id s' ∗ ownStepGhost γ md' c id s' ∗
        ⌜(NStateWf s' ∧ md.StepOut c id st.msg s s' md' ∧ st.msg.Type' ≠ MsgSnap ∧
         ((∀ ce, p ≠ .applyAck ce) → st.msg.Type' ≠ MsgStorageApplyResp) ∧
         s'.logst.applying = s.logst.applying ∧
         s'.logst.unpersisted = s.logst.unpersisted ∧ s'.logst.snap = s.logst.snap ∧
         uint.Z s.term ≤ uint.Z s'.term ∧
         AdvAbs.PendStep p s s' ∧
         s'.logst.prev = s.logst.prev ∧ logStoreRec s'.logst = logStoreRec s.logst ∧
         s'.logst.storage = s.logst.storage ∧ s'.prevote = s.prevote ∧ s'.gh = s.gh ∧
         (s'.role = .preCandidate → s.role = .preCandidate ∧ s'.term = s.term) ∧
         (∀ fp, PreGuardF fp s → PreGuardF fp s') ∧
         s'.logst.fl = s.logst.fl ∧ uint.Z s.logst.applied ≤ uint.Z s'.logst.applied ∧
         (∀ ce, p = .applyAck ce → ∀ e, ce.getLast? = some e →
            uint.Z e.Index' ≤ uint.Z s'.logst.applied) ∧
         SnapRoleBack s s' ∧
         (st.msg.Type' = MsgStorageAppendResp → s'.logst.applied = s.logst.applied) ∧
         uint.Z s.logst.inprogress ≤ uint.Z s'.logst.inprogress) ∧
         StepEnd c id st.msg st.ents st.ctx s s' ∧ AckEnd st.msg s s' ∧ NoSnapL s'.outbox⌝ }} := by
  iintro %Φ ⟨#Hinit, Hphys, Hghost, Hmin, Hp, Hlc, #Hfrg, #Hcap⟩ HΦ
  imod rdCred_zero_upd (GF := GF) γ with Hcr
  cases p with
  | self pv t =>
    rcases st with ⟨m, ents, sn, ctx, rsp⟩
    unfold pendingRel
    icases Hp with ⟨%Hsm, #Hraft0, -⟩
    ihave #Hraft := Hraft0 $$ Hfrg
    obtain ⟨⟨Hty, Hfr, Hto, Hnz, Hen, Hcn, Hrj⟩, rfl, rfl⟩ := Hsm
    simp only at Hty Hfr Hto Hnz Hen Hcn Hrj ⊢
    subst Hen Hcn
    have HtyR : RespType m.Type' := Hty
    ihave #Hmsg : □ (∀ ty, ⌜mtypeOf m.Type' = some ty⌝ -∗ isMessage γ (absMsg ty m [] [])) $$ []
    · imodintro
      iintro %ty %Hty'
      iapply isRaftMsg_isMessage γ id ⟨m, [], sn, [], rsp⟩ ty Hty'
        (fun hs => mtypeOf_resp_ne_snap _ HtyR (hs ▸ Hty')) $$ Hraft
    icases ownRaftPhysC_id_nz c r id s $$ Hphys with ⟨%Hidnz, Hphys⟩
    have Hfnz : m.From' ≠ W64 0 := by rw [Hfr]; exact Hidnz
    have Hsm : StepMsg m := by
      rcases Hty with h | h | h <;> simp [StepMsg, stepMsgTypes, h]
    ihave Hmin := msgIn_toC (b := s.gh.sn.sz) (movesB_false_of (t := m.Type') (by not_self)
      (by not_self) (by not_self) (by not_self) (by not_self)) ml _ _ $$ Hmin
    iapply raft.Step.untracedNs wp_raft_Step c md γ r id s ml m [] [] sn rsp Hsm
      (by not_self) (by not_self) (fun _ => ⟨Hto, Hnz⟩) (by not_self)
      (fun _ => ⟨Hto, Hnz, Hfnz, Hnw _ _ rfl⟩) (by not_self) (by not_self)
      (fun h => ⟨Hto, Hnz, Hfnz, fun Hr => by rw [Hrj h] at Hr; cases Hr⟩)
      (by not_self) (by not_self) (by not_self) (by not_self) (by not_self) (by not_self)
      (by not_self) (by not_self)
      (RestMsgOk.of_ne ⟨by not_self, by not_self, by not_self, by not_self, by not_self⟩) Hwf
      (GMode.Pre.of_facts Hpf (by not_self) (by not_self)) (fun h => absurd h (by not_self))
      Htr Hal $$ [$Hinit $Hphys $Hghost $Hlc Hmin Hcr]
    · have hP : m.Type' ≠ MsgProp := by not_self
      simp only [hP, ↓reduceIte, named]
      isplitr
      · imodintro
        iintro %h
        exact absurd h.1 (by first | not_self | msg_ne)
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
      isplitr
      · imodintro
        iintro %Hc
        exfalso
        revert Hc
        not_self
      isplitr
      · iexact Hcap
      isplitr
      · ipureintro; exact Hprev0
      ipureintro; exact Hns0
    · inext
      iintro %err %s' %c' %md' ⟨Hphys, Hghost, %Hwf', %Hstp, %Hcc, -, %Hframe, -, %Hterm, %Hresp, -,
        -, -, %Hend, %Hack', %Hns', -⟩
      have e2 := Hcc (fun h => absurd h (by not_self)); subst c'
      have Hfr' := Hframe (by not_self) (by not_self) (by not_self) (fun h => absurd h (by not_self))
        (fun _ h => absurd Hfr h)
      have Htm := Hterm (by not_self)
      iapply HΦ $$ %err %s' %md'
      iframe Hphys Hghost
      ipureintro
      refine ⟨⟨Hwf', Hstp, by not_self, fun _ => by not_self, Hfr'.1, Hfr'.2.2.1, Hfr'.2.1, Htm.1, ?_,
        Hfr'.2.2.2.1, Hfr'.2.2.2.2.1, Hfr'.2.2.2.2.2.1, Hfr'.2.2.2.2.2.2.1, Hfr'.2.2.2.2.2.2.2.1, ?role,
        fun _ => PreGuardF.step Htm, Hfr'.2.2.2.2.2.2.2.2.1, Hfr'.2.2.2.2.2.2.2.2.2, (fun _ h => by cases h),
        Htm.2.2.2.2.2.2.1, fun h => absurd h (by not_self), Htm.2.2.2.1 (by not_self)⟩, Hend, Hack', Hns'⟩
      case role =>
        intro h
        obtain ⟨Ht, Hor⟩ := Htm.2.2.2.2.2.1 h
        exact ⟨(Hor.resolve_right (by not_self)).1, Ht⟩
      show AdvAbs.SelfStep _ _ s s'
      refine ⟨fun hpv => ?_, fun hpv => ?_⟩
      · have hnpv : m.Type' ≠ MsgPreVoteResp := by
          intro h; simp [h] at hpv
        refine ⟨Htm.2.2.1 (by not_self) hnpv (by not_self), fun Hlt => Hresp.1 ?_ Hlt⟩
        rcases Hty with h | h | h
        · exact .inr h
        · exact .inl h
        · exact absurd h hnpv
      · exact Hresp.2 (by simpa using hpv)
  | appendAck t b e sn =>
    obtain ⟨Hsn0, Hsok0⟩ := Hack t b e sn rfl
    subst Hsn0
    unfold pendingRel
    icases Hp with ⟨%Hm, -⟩
    have Hm' : st = _ := Hm
    subst Hm'
    obtain ⟨Hle, -⟩ := Hok
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
    ihave Hmin := msgIn_toC (b := s.gh.sn.sz)
      (movesB_false_of (t := (appendAckM id t (e.getD ⟨W64 0, W64 0⟩)).Type') (by msg_ne)
        (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne)) ml _ _ $$ Hmin
    iapply raft.Step.untracedNs wp_raft_Step c md γ r id s ml (appendAckM id t (e.getD ⟨W64 0, W64 0⟩))
      [] [] none []
      (by simp [StepMsg, stepMsgTypes, appendAckM])
      (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne)
      (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne)
      (fun _ => ⟨(fun _ h => by cases h), Hle, Hsok', Hghoff⟩) (by msg_ne) (by msg_ne) (by msg_ne)
      (RestMsgOk.of_ne ⟨by msg_ne, by msg_ne, by msg_ne, by msg_ne, by msg_ne⟩) Hwf
      (GMode.Pre.of_facts Hpf (by msg_ne) (by msg_ne)) (fun h => absurd h (by msg_ne))
      Htr Hal $$ [$Hinit $Hphys $Hghost $Hlc Hmin Hcr]
    · have hP : (appendAckM id t (e.getD ⟨W64 0, W64 0⟩)).Type' ≠ MsgProp := by msg_ne
      simp only [hP, ↓reduceIte, named]
      have Hty0 : mtypeOf (appendAckM id t (e.getD ⟨W64 0, W64 0⟩)).Type' = none := rfl
      isplitr
      · imodintro
        iintro %h
        exact absurd h.1 (by msg_ne)
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
      isplitr
      · imodintro
        iintro %Hc
        exfalso
        revert Hc
        msg_ne
      isplitr
      · iexact Hcap
      isplitr
      · ipureintro; exact Hprev0
      ipureintro; exact Hns0
    · inext
      iintro %err %s' %c' %md' ⟨Hphys, Hghost, %Hwf', %Hstp, %Hcc, %Hloc, -, -, %Hterm, -, -, -, -,
        %Hend, %Hack', %Hns', -⟩
      have e2 := Hcc (fun _ => rfl); subst c'
      obtain ⟨Hfr, Hap, -, Hapa⟩ := Hloc.1 (fun _ => rfl) (.inr (.inl rfl))
      iapply HΦ $$ %err %s' %md'
      iframe Hphys Hghost
      ipureintro
      exact ⟨⟨Hwf', Hstp, by msg_ne, fun _ => by msg_ne, Hap (fun Hc => absurd Hc (by msg_ne)), Hfr.2.2.1,
        Hfr.2.2.2.1, by rw [Hfr.1]; exact Int.le_refl _, Hfr.1, Hfr.2.2.2.2.1, Hfr.2.2.2.2.2.1,
        Hfr.2.2.2.2.2.2.1, Hfr.2.2.2.2.2.2.2.1, Hfr.2.2.2.2.2.2.2.2.1,
        fun h => ⟨by rw [← Hfr.2.2.2.2.2.2.2.2.2.1]; exact h, Hfr.1⟩,
        fun _ => PreGuardF.step (Hterm (by msg_ne)), Hfr.2.2.2.2.2.2.2.2.2.2.1, Hfr.2.2.2.2.2.2.2.2.2.2.2, (fun _ h => by cases h),
        (Hterm (by msg_ne)).2.2.2.2.2.2.1, Hapa, Hfr.2.1⟩, Hend, Hack', Hns'⟩
  | applyAck ce =>
    unfold pendingRel
    icases Hp with ⟨%Hm, -⟩
    have Hm' : st = _ := Hm
    subst Hm'
    ihave Hmin := msgIn_toC (b := s.gh.sn.sz)
      (movesB_false_of (t := (applyAckM id).Type') (by msg_ne)
        (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne)) ml _ _ $$ Hmin
    iapply raft.Step.untracedNs wp_raft_Step c md γ r id s ml (applyAckM id) ce [] none []
      (by simp [StepMsg, stepMsgTypes, applyAckM])
      (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne)
      (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne)
      (by msg_ne) (fun _ => rfl) (by msg_ne) (by msg_ne)
      (RestMsgOk.of_ne ⟨by msg_ne, by msg_ne, by msg_ne, by msg_ne, by msg_ne⟩) Hwf
      (Hpre ce _ rfl rfl) (fun h => absurd h (by msg_ne))
      Htr Hal $$ [$Hinit $Hphys $Hghost $Hlc Hmin Hcr]
    · have hP : (applyAckM id).Type' ≠ MsgProp := by msg_ne
      simp only [hP, ↓reduceIte, named]
      have Hty0 : mtypeOf (applyAckM id).Type' = none := rfl
      isplitr
      · imodintro
        iintro %h
        exact absurd h.1 (by msg_ne)
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
      isplitr
      · imodintro
        iintro %Hc
        exfalso
        revert Hc
        msg_ne
      isplitr
      · iexact Hcap
      isplitr
      · ipureintro; exact Hprev0
      ipureintro; exact Hns0
    · inext
      iintro %err %s' %c' %md' ⟨Hphys, Hghost, %Hwf', %Hstp, %Hcc, %Hloc, -, -, %Hterm, -, -, -, -,
        %Hend, %Hack', %Hns', -⟩
      have e2 := Hcc (fun h => absurd h (by msg_ne)); subst c'
      obtain ⟨Hfr, Hap, Happ, -⟩ := Hloc.1 (fun h => absurd h (by msg_ne)) (.inr (.inr rfl))
      iapply HΦ $$ %err %s' %md'
      iframe Hphys Hghost
      ipureintro
      exact ⟨⟨Hwf', Hstp, by msg_ne, fun h => absurd rfl (h ce), Hap (fun _ e He => (Hok e He).2), Hfr.2.2.1,
        Hfr.2.2.2.1, by rw [Hfr.1]; exact Int.le_refl _, Hfr.1, Hfr.2.2.2.2.1, Hfr.2.2.2.2.2.1,
        Hfr.2.2.2.2.2.2.1, Hfr.2.2.2.2.2.2.2.1, Hfr.2.2.2.2.2.2.2.2.1,
        fun h => ⟨by rw [← Hfr.2.2.2.2.2.2.2.2.2.1]; exact h, Hfr.1⟩,
        fun _ => PreGuardF.step (Hterm (by msg_ne)), Hfr.2.2.2.2.2.2.2.2.2.2.1, Hfr.2.2.2.2.2.2.2.2.2.2.2,
        fun ce' h => by injection h with h; subst h; exact Happ rfl,
        (Hterm (by msg_ne)).2.2.2.2.2.2.1, fun h => absurd h (by msg_ne), Hfr.2.1⟩, Hend, Hack', Hns'⟩

end proof

end EtcdGrove
end Perennial
