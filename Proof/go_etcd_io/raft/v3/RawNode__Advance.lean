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
-/
module

public import Spec.go_etcd_io.raft.v3.RawNode__Advance
public import Spec.go_etcd_io.raft.v3.raft__Step
-- `Step.commit_mono`
public import Proof.go_etcd_io.raft.v3.Protocol.Facts

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

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
  ∀ pv t, Pending.self pv t ∈ rest → uint.Z t ≤ uint.Z s.term + (if pv then 1 else 0)

/-- The loop's term invariant (see the file header): from `s` to `s1`, up by at most
one; and while self-addressed responses remain, a pre-candidate is still at `s`'s term. -/
private def TermInv (s s1 : NState) (rest : List Pending) : Prop :=
  uint.Z s.term ≤ uint.Z s1.term ∧ uint.Z s1.term ≤ uint.Z s.term + 1 ∧
  ((∃ pv t, Pending.self pv t ∈ rest) → s1.role = .preCandidate →
    uint.Z s1.term = uint.Z s.term)

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
    (Hge : uint.Z s1.term ≤ uint.Z s2.term) (Hps : PendStep p s1 s2) :
    TermInv s s2 rest := by
  obtain ⟨Hlo, Hhi, Hpre⟩ := Hti
  cases p with
  | self pv t =>
    have Hb := Hsb pv t List.mem_cons_self
    have Hpre1 := Hpre ⟨pv, t, List.mem_cons_self⟩
    cases pv with
    | false =>
      obtain ⟨Hle, Hrole⟩ := Hps.1 rfl
      simp only [Bool.false_eq_true, ↓reduceIte, Int.add_zero] at Hb
      have H2 : uint.Z s2.term ≤ uint.Z s1.term :=
        Int.le_trans Hle (Int.max_le.2 ⟨Int.le_refl _, by omega⟩)
      refine ⟨by omega, by omega, fun _ Hr => ?_⟩
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
      refine ⟨by omega, Hhi2, fun _ Hr => ?_⟩
      obtain ⟨Hr1, Heq⟩ := Hrole Hr
      have := Hpre1 Hr1
      rw [Heq]; exact this
  | appendAck tm e =>
    have Ht : s2.term = s1.term := Hps
    refine ⟨by rw [Ht]; exact Hlo, by rw [Ht]; exact Hhi, fun ⟨pv, t, h⟩ => ?_⟩
    exact absurd h (stepsOk_ack_noself s1 _ rest (fun _ _ h => by cases h) Hok pv t)
  | applyAck ce =>
    have Ht : s2.term = s1.term := Hps
    refine ⟨by rw [Ht]; exact Hlo, by rw [Ht]; exact Hhi, fun ⟨pv, t, h⟩ => ?_⟩
    exact absurd h (stepsOk_ack_noself s1 _ rest (fun _ _ h => by cases h) Hok pv t)

end terms

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]
variable [AllG GF]

/-- A premise of `Step` about another message type: the type is not it. -/
local macro "msg_ne" : tactic => `(tactic| (intro Hc; simp [MsgHup, MsgVote, MsgVoteResp,
  MsgPreVote, MsgPreVoteResp, MsgApp, MsgHeartbeat, MsgAppResp, MsgHeartbeatResp, MsgSnap,
  MsgBeat, MsgProp, MsgStorageAppendResp, MsgStorageApplyResp, appendAckMsg,
  applyAckMsg] at Hc))

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
         MsgAppResp, MsgHeartbeatResp, MsgSnap, MsgBeat, MsgProp, MsgStorageAppendResp,
         MsgStorageApplyResp] at Hc)))

/-- The node's id is nonzero (the ghost state's `Hidnz`): a self-addressed response's
`From`. -/
private theorem ghost_id_nz (γ : RaftNames) (id : w64) (ps : PState) :
    ⊢ ownRaftGhost (GF := GF) γ id ps -∗ ⌜id ≠ W64 0⌝ := by
  unfold ownRaftGhost
  iintro ⟨%γv, %voted, %kl, H⟩
  iNamed H
  ipureintro; exact Hidnz

/-- One pending message through `Step`'s spec: the `MsgStorageAppendResp` acknowledges
persisted entries (`StableOk`) because it acknowledges the last entry of what the storage
holds, whose records `ownRawNode` keeps, nothing is unpersisted and no snapshot is pending
(`stableOk_of_stored`, 2026-10-10; until then because its index was in progress -- Rocq's
`ready_stable_ok`); a self-addressed response (2026-10-10) is what `pendingRel` says, and
a pre-candidate's term does not wrap (`Hnw`, for a pre-vote response). -/
private theorem wp_step_pending
    (wp_raft_Step : raft.Step.spec (GF := GF) (hG := hG))
    (γ : RaftNames) (r : Loc) (id : w64) (s : NState)
    (ps : PState) (m : raftpb.Message) (p : Pending)
    (Hin : id ∈ γ.reCfg) (Hrel : NStateRel s ps) (Hok : PendingOk s p)
    (Hsnap : s.logst.snap = none) (Hunp : s.logst.unpersisted = [])
    (Hnw : ∀ pv t, p = .self pv t → s.role = .preCandidate → uint.Z s.term + 1 < 2 ^ 64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhys γ.reCfg r id s ∗
        ownRaftGhost γ id ps ∗ pendingRel γ id m p ∗ pendingOwn m p ∗
        storedRecs γ s.logst.prev s.logst.stored }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #m))
    {{ (err : GoInterface) (s' : NState) (ps' : PState), RET #err;
        ownRaftPhys γ.reCfg r id s' ∗ ownRaftGhost γ id ps' ∗
        ⌜NStateRel s' ps' ∧ (∃ recv, Step γ.reCfg id ps recv ps') ∧
         s'.logst.applying = s.logst.applying ∧
         s'.logst.unpersisted = s.logst.unpersisted ∧ s'.logst.snap = s.logst.snap ∧
         uint.Z s.term ≤ uint.Z s'.term ∧
         PendStep p s s' ∧
         s'.logst.prev = s.logst.prev ∧ s'.logst.stored = s.logst.stored ∧
         s'.logst.storage = s.logst.storage⌝ }} := by
  iintro %Φ ⟨#Hinit, Hphys, Hghost, #Hp, Hown, #Hstr⟩ HΦ
  cases p with
  | self pv t =>
    unfold pendingRel
    icases Hp with ⟨%Hsm, #Hmsg⟩
    obtain ⟨⟨Hty, Hfr, Hto, Hnz, Hen, Hcn, Hrj⟩, rfl, rfl⟩ := Hsm
    ihave %Hidnz := ghost_id_nz γ id ps $$ Hghost
    have Hfnz : m.From' ≠ W64 0 := by rw [Hfr]; exact Hidnz
    have Hsm : StepMsg m := by
      rcases Hty with h | h | h <;> simp [StepMsg, stepMsgTypes, h]
    iapply wp_raft_Step γ.reCfg γ r id s ps m [] [] rfl Hsm Hin
      (by not_self) (by not_self) (fun _ => ⟨Hto, Hnz⟩) (by not_self)
      (fun _ => ⟨Hto, Hnz, Hfnz, Hnw _ _ rfl⟩) (by not_self) (by not_self)
      (fun h => ⟨Hto, Hnz, Hfnz, fun Hr => by rw [Hrj h] at Hr; cases Hr⟩)
      (by not_self) (by not_self) (by not_self) (by not_self) (by not_self) (by not_self)
      Hrel $$ [$Hinit $Hphys $Hghost]
    · have hP : m.Type' ≠ MsgProp := by not_self
      simp only [hP, ↓reduceIte, named]
      rw [Hen, Hcn]
      isplitr
      · isplitr
        · iapply ownSlice_nil
        isplitr
        · iapply ownSliceCap_nil
        isplitr
        · ipureintro; not_self
        isplitr
        · ipureintro; not_self
        imodintro
        iintro %ty %Hty' %_
        iapply Hmsg $$ %ty %Hty'
      isplitr
      · itrivial
      isplitr
      · iexists []
        isplitr
        · iapply ownSlice_nil
        ipureintro
        exact ⟨by simp [campaignTransfer], fun _ => rfl⟩
      imodintro
      iintro %Hc
      exfalso
      revert Hc
      not_self
    · inext
      iintro %err %s' %ps' ⟨Hphys, Hghost, %Hrel', %Hstp, -, %Hframe, %Hterm, %Hresp, -⟩
      have Hfr' := Hframe (by not_self) (by not_self)
      have Htm := Hterm (by not_self)
      iapply HΦ $$ %err %s' %ps'
      iframe Hphys Hghost
      ipureintro
      refine ⟨Hrel', Hstp, Hfr'.1, Hfr'.2.2.1, Hfr'.2.1, Htm.1, ?_, Hfr'.2.2.2.1,
        Hfr'.2.2.2.2.1, Hfr'.2.2.2.2.2⟩
      show SelfStep _ _ s s'
      refine ⟨fun hpv => ?_, fun hpv => ?_⟩
      · -- a vote or append response
        have hnpv : m.Type' ≠ MsgPreVoteResp := by
          intro h; simp [h] at hpv
        refine ⟨Htm.2.2.1 (by not_self) hnpv, fun Hlt => Hresp.1 ?_ Hlt⟩
        rcases Hty with h | h | h
        · exact .inr h
        · exact .inl h
        · exact absurd h hnpv
      · -- a pre-vote response
        exact Hresp.2 (by simpa using hpv)
  | appendAck t e =>
    unfold pendingRel
    icases Hp with %Hm
    subst Hm
    obtain ⟨Hle, Hlast⟩ := Hok
    icases stableOk_of_stored γ id s ps e Hrel Hlast Hsnap Hunp $$ Hstr Hghost
      with ⟨%Hsok, Hghost⟩
    iapply wp_raft_Step γ.reCfg γ r id s ps (appendAckMsg id t e) [] [] rfl
      (by simp [StepMsg, stepMsgTypes, appendAckMsg]) Hin
      (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne)
      (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne)
      (fun _ => ⟨rfl, Hle, fun _ _ => Hsok⟩) (by msg_ne) Hrel
      $$ [$Hinit $Hphys $Hghost]
    · have hP : (appendAckMsg id t e).Type' ≠ MsgProp := by msg_ne
      simp only [hP, ↓reduceIte, named]
      have Hty0 : mtypeOf (appendAckMsg id t e).Type' = none := rfl
      simp only [appendAckMsg] at Hty0 ⊢
      isplitr
      · isplitr
        · iapply ownSlice_nil
        isplitr
        · iapply ownSliceCap_nil
        isplitr
        · ipureintro; msg_ne
        isplitr
        · ipureintro; msg_ne
        imodintro
        iintro %ty %Hty
        rw [Hty0] at Hty
        cases Hty
      isplitr
      · itrivial
      isplitr
      · iexists []
        isplitr
        · iapply ownSlice_nil
        ipureintro
        exact ⟨by simp [campaignTransfer], fun _ => rfl⟩
      imodintro
      iintro %Hc
      exfalso
      revert Hc
      msg_ne
    · inext
      iintro %err %s' %ps' ⟨Hphys, Hghost, %Hrel', %Hstp, %Hloc, -⟩
      obtain ⟨Hfr, Hap⟩ := Hloc (.inr (.inl rfl))
      iapply HΦ $$ %err %s' %ps'
      iframe Hphys Hghost
      ipureintro
      exact ⟨Hrel', Hstp, Hap (fun Hc => absurd Hc (by msg_ne)), Hfr.2.2.1, Hfr.2.2.2.1,
        by rw [Hfr.1]; exact Int.le_refl _, Hfr.1, Hfr.2.2.2.2.1, Hfr.2.2.2.2.2.1,
        Hfr.2.2.2.2.2.2⟩
  | applyAck ce =>
    unfold pendingRel
    icases Hp with ⟨%sl, %Hm, #Hsl⟩
    subst Hm
    unfold pendingOwn
    iapply wp_raft_Step γ.reCfg γ r id s ps (applyAckMsg id sl) ce [] rfl
      (by simp [StepMsg, stepMsgTypes, applyAckMsg]) Hin
      (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne)
      (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne) (by msg_ne)
      (by msg_ne) (fun _ => rfl) Hrel $$ [$Hinit $Hphys $Hghost Hown]
    · have hP : (applyAckMsg id sl).Type' ≠ MsgProp := by msg_ne
      simp only [hP, ↓reduceIte, named]
      have Hty0 : mtypeOf (applyAckMsg id sl).Type' = none := rfl
      simp only [applyAckMsg] at Hty0 ⊢
      isplitl [Hown]
      · isplitr
        · iexact Hsl
        isplitl [Hown]
        · iexact Hown
        isplitr
        · ipureintro; msg_ne
        isplitr
        · ipureintro; intro _ e He; exact (Hok e He).1
        imodintro
        iintro %ty %Hty
        rw [Hty0] at Hty
        cases Hty
      isplitr
      · itrivial
      isplitr
      · iexists []
        isplitr
        · iapply ownSlice_nil
        ipureintro
        exact ⟨by simp [campaignTransfer], fun _ => rfl⟩
      imodintro
      iintro %Hc
      exfalso
      revert Hc
      msg_ne
    · inext
      iintro %err %s' %ps' ⟨Hphys, Hghost, %Hrel', %Hstp, %Hloc, -⟩
      obtain ⟨Hfr, Hap⟩ := Hloc (.inr (.inr rfl))
      iapply HΦ $$ %err %s' %ps'
      iframe Hphys Hghost
      ipureintro
      exact ⟨Hrel', Hstp, Hap (fun _ e He => (Hok e He).2), Hfr.2.2.1, Hfr.2.2.2.1,
        by rw [Hfr.1]; exact Int.le_refl _, Hfr.1, Hfr.2.2.2.2.1, Hfr.2.2.2.2.2.1,
        Hfr.2.2.2.2.2.2⟩

theorem RawNode.Advance.wp_proof
    (wp_raft_Step : raft.Step.spec (GF := GF) (hG := hG)) :
    RawNode.Advance.spec (GF := GF) (hG := hG) := by
  intro γ rn id rs rd Hunp0 Hterm0
  wp_start as H
  iNamed H
  iNamed Hrn
  have Hunp' : s.logst.unpersisted = [] := Hunp ▸ Hunp0
  have Hterm0' : uint.Z s.term + 1 < 2 ^ 64 := by rw [← Htrm]; exact Hterm0
  wp_auto
  rw [Hasync]
  wp_auto
  ihave %Hlen := BigSepL2.bigSepL2_length $$ Hpend
  ihave %Hsl := ownSlice_len _ _ _ $$ Hsteps
  -- the range construct's own counter `i_ptr` (Rocq's `j`) and the body's `i` share a
  -- Go name; rename the body's
  rename_i ibp
  irename: (ibp ↦ (_ : w64)) => ib
  ihave IH : iprop(∃ (n : w64) (s1 : NState) (ps1 : PState) (steps1 : List raftpb.Message)
        (mv : raftpb.Message) (iv : w64),
      "i" ∷ i_ptr ↦ n ∗ "m" ∷ m_ptr ↦ mv ∗ "ib" ∷ ibp ↦ iv ∗
      "Hphys" ∷ ownRaftPhys γ.reCfg rnv.raft' id s1 ∗ "Hghost" ∷ ownRaftGhost γ id ps1 ∗
      "Hsteps" ∷ rnv.stepsOnAdvance' ↦* steps1 ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (steps.length : Int)⌝ ∗
      "%Hsteps1" ∷ ⌜steps1.length = steps.length ∧
                    steps1.drop (sint.nat n) = steps.drop (sint.nat n)⌝ ∗
      "%Hrel1" ∷ ⌜NStateRel s1 ps1⌝ ∗
      "%Hs1" ∷ ⌜s1.logst.applying = s.logst.applying ∧
                s1.logst.unpersisted = s.logst.unpersisted ∧ s1.logst.snap = s.logst.snap ∧
                s1.logst.prev = s.logst.prev ∧ s1.logst.stored = s.logst.stored⌝ ∗
      "%Hsg1" ∷ ⌜s1.logst.storage = s.logst.storage⌝ ∗
      "%Hok1" ∷ ⌜StepsOk s1 (rs.steps.drop (sint.nat n))⌝ ∗
      "%Hsb1" ∷ ⌜SelfBound s (rs.steps.drop (sint.nat n))⌝ ∗
      "%Hti1" ∷ ⌜TermInv s s1 (rs.steps.drop (sint.nat n))⌝ ∗
      "Hpown" ∷ ([∗list] _k ↦ m;p ∈ steps.drop (sint.nat n);rs.steps.drop (sint.nat n),
                   pendingOwn m p))
    $$ [i m ib Hphys Hghost Hsteps Hpown]
  · iexists W64 0, s, ps, steps, zero_val raftpb.Message, zero_val w64
    have H0 : sint.nat (W64 0) = 0 := rfl
    rw [H0, List.drop_zero, List.drop_zero]
    simp only [named]
    iframe
    ipureintro
    exact ⟨by word, ⟨trivial, trivial⟩, Hrel, by simp, Hstok,
      stepsOk_selfBound s rs.steps Hstok, Int.le_refl _, by omega, fun _ _ => rfl⟩
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
    ihave #Hpm := BigSepL2.bigSepL2_lookup (Φ := fun _ m p => pendingRel (GF := GF) γ id m p)
      Hmm_lookup Hp_lookup $$ Hpend
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hn.1, Hlt⟩)]
    wp_apply wp_load_slice_index rnv.stepsOnAdvance' (sint.Z n) steps1 (DFrac.own 1) mm Hn.1
      $$ [Hsteps] with Hsteps
    · iframe
      ipureintro
      exact Hmm1
    rw [drop_cons_of_lookup Hp_lookup] at Hok1 Hsb1 Hti1
    rw [drop_cons_of_lookup Hmm_lookup, drop_cons_of_lookup Hp_lookup]
    icases Hpown with ⟨Hpo, Hpown⟩
    have HnS : sint.nat n + 1 = sint.nat (n + W64 1) := by word
    rw [HnS] at Hok1 Hsb1 Hti1 ⊢
    obtain ⟨Hpok, Hrest⟩ := stepsOk_cons _ _ _ Hok1
    -- a pre-candidate stepping its own pre-vote response is at `s`'s term
    have Hnw1 : ∀ pv t, p = .self pv t → s1.role = .preCandidate →
        uint.Z s1.term + 1 < 2 ^ 64 := by
      intro pv t hp hr
      have := Hti1.2.2 ⟨pv, t, by rw [hp]; exact List.mem_cons_self⟩ hr
      omega
    ihave #Hstr1 := storedRecs_eq γ _ s1.logst.prev _ s1.logst.stored Hs1.2.2.2.1 Hs1.2.2.2.2
      $$ Hstrecs
    wp_apply wp_step_pending wp_raft_Step γ rnv.raft' id s1 ps1 mm p Hin
      Hrel1 Hpok (Hs1.2.2.1.trans Hsnap) (Hs1.2.1.trans Hunp') Hnw1
      $$ [$Hphys $Hghost $Hpm $Hpo $Hstr1] as %err %s2 %ps2 ⟨Hphys, Hghost, %Hst2⟩
    obtain ⟨Hrel2, ⟨recv2, Hst2⟩, Ha2, Hu2, Hsn2, Ht2, Hps2, Hpv2, Hsd2, Hsg2⟩ := Hst2
    -- `stepsOnAdvance[i] = pb.Message{}`
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hn.1, Hlt⟩)]
    wp_apply wp_store_slice_index rnv.stepsOnAdvance' (sint.Z n) steps1 (zero_val raftpb.Message)
      $$ [Hsteps] with Hsteps
    · iframe
      ipureintro
      constructor <;> word
    wp_for_post
    have Hc12 : uint.Z s1.logst.committed ≤ uint.Z s2.logst.committed := by
      have H := Step.commit_mono Hst2
      rw [← Hrel1.1, ← Hrel2.1] at H
      exact H
    iframe
    iexists n + W64 1, s2, ps2, steps1.set (sint.Z n).toNat (zero_val raftpb.Message), mm, n
    iframe
    ipureintro
    refine ⟨by word, ⟨by rw [List.length_set]; exact Hsteps1.1, ?_⟩, Hrel2,
      ⟨Ha2.trans Hs1.1, Hu2.trans Hs1.2.1, Hsn2.trans Hs1.2.2.1, Hpv2.trans Hs1.2.2.2.1,
        Hsd2.trans Hs1.2.2.2.2⟩, Hsg2.trans Hsg1,
      stepsOk_mono_le s1 s2 _ Ht2 ⟨Hpv2, Hsd2⟩ Hc12 Ha2 Hrest,
      fun pv t h => Hsb1 pv t (List.mem_cons_of_mem _ h),
      termInv_step s s1 s2 p _ Hok1 Hsb1 Hti1 Ht2 Hps2⟩
    rw [← HnS, List.drop_set_of_lt (by simp [sint.nat]), ← List.drop_drop, ← List.drop_drop,
      Hsteps1.2]
  · -- the loop is done: `stepsOnAdvance = stepsOnAdvance[:0]`
    ihave %Hwf := ownSlice_wf _ _ _ $$ Hsteps
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
    iapply HΦ $$ %s1.term
    isplitl
    · iapply ownRawNode_intro γ rn id { rs with steps := [], term := s1.term } s1 ps1
        { rnv with stepsOnAdvance' :=
            slice.slice rnv.stepsOnAdvance' raftpb.Message (W64 0) (W64 0) }
        sv [] Hrel1 Hin Hasync (by rw [Hs1.1]; exact Hdlen) (by rw [Hs1.2.1]; exact Hunp)
        (by rw [Hs1.2.2.1]; exact Hsnap) trivial rfl (by rw [Hsg1]; exact Hstor)
        $$ Hrn Hphys Hghost Hsoft Hsl0 Hcap0 [] [] Hdeliv Hstr1
      · iempintro
      · iempintro
    ipureintro
    rw [Htrm]
    exact ⟨Hti1.1, Hti1.2.1⟩

end proof

end EtcdGrove
end Perennial
