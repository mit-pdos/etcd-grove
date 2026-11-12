/-
Port of `election_proof/proof_releasePendingReadIndexMessages.v`; rewritten (2026-10-13)
for the general spec of 2026-10-12, which releases the pending requests.

An empty queue returns at the length test (either way, `ReleaseResult` holds of the state
unchanged). Otherwise the entry at the commit index is of
the current term (the premise), so `committedEntryInCurrentTerm` holds and the `Error` arm
is dead; the field is taken (`ownRaftPhysC_misc`, the state's `pend` emptied) and each
request goes to `sendMsgReadIndexResponse`, with the invariant that after `k` of them the
read-only object is `readonlyRelease` of the first `k` (`relState`) -- or (2026-10-14, the
single-voter fix: `sendMsgReadIndexResponse`'s first branch, the configuration fixed through the
loop) that the first `k` are answered (`readRespondAll` of the first `k` of `pendReqs`).
-/
module

public import RaftWitness.Spec.go_etcd_io.raft.v3.releasePendingReadIndexMessages
public import RaftWitness.Spec.go_etcd_io.raft.v3.raft__committedEntryInCurrentTerm

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section helpers
variable [GooseExts]

/-- The state once the first `k` pending requests were released, before the heartbeats. -/
def relState (id : w64) (s : NState) (k : Nat) : NState :=
  { s with rd := { s.rd with pend := [],
                             ro := readonlyRelease s.rd.ro id s.logst.committed (s.rd.pend.take k) } }

theorem relState_full (id : w64) (s : NState) :
    relState id s s.rd.pend.length = releasedState id s := by
  simp only [relState, releasedState, List.take_length]

/-- One more request released. -/
theorem readonlyRelease_take_succ (r : ReadOnly) (id c : w64)
    (pend : List (MessageM × List EntryM)) (k : Nat) (p : MessageM × List EntryM)
    (Hp : pend[k]? = some p) :
    readonlyRelease r id c (pend.take (k + 1)) =
      readonlyArrive (readonlyRelease r id c (pend.take k)) id ⟨c, p.1.From', p.2⟩ := by
  unfold readonlyRelease
  rw [List.take_add_one, Hp]
  simp

/-- With nothing pending, nothing changes. -/
theorem released_nil (id : w64) (s : NState) (Hpend : s.rd.pend = []) :
    { sendMsgs (releasedState id s) [] with prvals := s.prvals } = s := by
  obtain ⟨term, vote, lead, role, votes, outbox, stepfn, ticking, progress, log, logst, prvals,
    prevote, gh, ⟨states, ro, pend⟩⟩ := s
  simp only at Hpend
  subst Hpend
  simp [sendMsgs, releasedState, readonlyRelease]

/-- With nothing pending, emptying the queue changes nothing. -/
theorem pend_nil_eq (s : NState) (Hpend : s.rd.pend = []) :
    { s with rd := { s.rd with pend := [] } } = s := by
  obtain ⟨term, vote, lead, role, votes, outbox, stepfn, ticking, progress, log, logst, prvals,
    prevote, gh, ⟨states, ro, pend⟩⟩ := s
  simp only at Hpend
  subst Hpend
  rfl

theorem pendReqs_lookup (s : NState) (k : Nat) (p : MessageM × List EntryM)
    (Hp : s.rd.pend[k]? = some p) :
    (pendReqs s)[k]? = some ⟨s.logst.committed, p.1.From', p.2⟩ := by
  simp [pendReqs, List.getElem?_map, Hp]

/-- A heartbeat valid in a state with `s`'s term, commit, role and matches is valid
in `s`. -/
theorem heartbeatOk_transfer (id : w64) (s t : NState) (m : Msg)
    (Hterm : t.term = s.term) (Hcm : t.logst.committed = s.logst.committed)
    (Hrole : t.role = s.role) (Hmm : prvalsMatch t.prvals = prvalsMatch s.prvals)
    (H : HeartbeatOk id (toPState t) m) : HeartbeatOk id (toPState s) m := by
  unfold HeartbeatOk matchOf at *
  simp only [toPState, Hterm, Hcm, Hrole, Hmm] at *
  exact H

end helpers

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem releasePendingReadIndexMessages.wp_proof
    (wp_raft_committedEntryInCurrentTerm :
      raft.committedEntryInCurrentTerm.spec (GF := GF) (hG := hG))
    (wp_sendMsgReadIndexResponse : sendMsgReadIndexResponse.spec (GF := GF) (hG := hG)) :
    releasePendingReadIndexMessages.spec (GF := GF) (hG := hG) := by
  intro c r id s Hlead Hterm Hcit Hpne
  wp_start as Hpre
  iNamed Hpre
  wp_auto
  -- `len(r.pendingReadIndexMessages) == 0`
  icases ownRaftPhysC_misc c r id s $$ Hphys with ⟨%rs, %ro, %pr, Hrs, Hro, Hpr, Hmisc, Hback⟩
  iunfold ownRaftMisc at Hmisc
  iNamed Hmisc
  icases Hpri with ⟨%pls, Hpri, #Hpls⟩
  ihave %Hprl := ownSlice_len $$ Hpri
  ihave %Hpll := BigSepL2.bigSepL2_length $$ Hpls
  wp_auto
  ihave Hphys := Hback $$ %rs %ro %pr %s.rd Hrs Hro Hpr
    [HreadStates HreadStates_cap Hro_obj Hpri Hpri_cap]
  · unfold ownRaftMisc
    simp only [named]
    iframe HreadStates HreadStates_cap Hro_obj Hpri_cap
    iexists pls
    iframe Hpri Hpls
  ihave Hphys := ownRaftPhysC_eq c r id _ s rfl $$ Hphys
  by_cases Hpend : s.rd.pend = []
  · -- nothing pending: return
    have Hz : pr.len = W64 0 := by
      rw [Hpend] at Hpll; obtain ⟨h1, h2⟩ := Hprl; simp only [List.length_nil] at Hpll
      word
    rw [decide_eq_true Hz]
    wp_auto
    iapply HΦ $$ %s
    iframe Hphys
    ipureintro
    by_cases Hsg : CfgSingle c id
    · left
      refine ⟨Hsg, ?_⟩
      simp only [pendReqs, Hpend, List.map_nil]
      exact (pend_nil_eq s Hpend).symm
    · right
      exact ⟨Hsg, [], s.prvals, (released_nil id s Hpend).symm,
        fun _ h => absurd h List.not_mem_nil, rfl⟩
  have Hnz : pr.len ≠ W64 0 := by
    intro Hz
    obtain ⟨h1, h2⟩ := Hprl
    rw [Hz] at h1
    exact Hpend (List.eq_nil_of_length_eq_zero (by rw [← Hpll, h1]; rfl))
  rw [decide_eq_false Hnz]
  wp_auto
  iclear Hpls
  clear Hnz Hprl Hpll pr ro rs pls
  -- the entry at the commit index is of the current term
  wp_apply wp_raft_committedEntryInCurrentTerm _ _ _ _ Hterm $$ [$Hphys] as %b ⟨Hphys, %Hb⟩
  rw [Hb.2 (Hcit Hpend)]
  wp_auto
  -- `msgs := r.pendingReadIndexMessages; r.pendingReadIndexMessages = nil`
  icases ownRaftPhysC_misc c r id s $$ Hphys with ⟨%rs, %ro, %pr, Hrs, Hro, Hpr, Hmisc, Hback⟩
  iunfold ownRaftMisc at Hmisc
  iNamed Hmisc
  icases Hpri with ⟨%pls, Hpri, #Hpls⟩
  ihave %Hprl := ownSlice_len $$ Hpri
  ihave %Hpll := BigSepL2.bigSepL2_length $$ Hpls
  wp_auto
  ihave Hphys := Hback $$ %rs %ro %slice.nil %({ s.rd with pend := [] }) Hrs Hro Hpr
    [HreadStates HreadStates_cap Hro_obj]
  · unfold ownRaftMisc
    simp only [named]
    iframe HreadStates HreadStates_cap Hro_obj
    isplitl []
    · iexists []
      isplitr
      · iapply ownSlice_nil
      iapply BigSepL2.bigSepL2_nil.2
      iempintro
    iapply ownSliceCap_nil
  iclear Hpri_cap
  obtain ⟨Hl1, Hl2⟩ := Hprl
  by_cases Hsg : CfgSingle c id
  · -- (2026-10-14) the leader is the single voter: each request answered at once
    ihave Hphys := ownRaftPhysC_eq c r id _
      (readRespondAll id { s with rd := { s.rd with pend := [] } }
        ((pendReqs s).take (sint.nat (W64 0))))
      (by rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero]; rfl) $$ Hphys
    ihave IH : iprop(∃ (n : w64) (mv : Loc),
        "i" ∷ i_ptr ↦ n ∗
        "m" ∷ m_ptr ↦ mv ∗
        "Hpri" ∷ pr ↦* pls ∗
        "Hphys" ∷ ownRaftPhysCV c c.voters r id
          (readRespondAll id { s with rd := { s.rd with pend := [] } }
            ((pendReqs s).take (sint.nat n))) ∗
        "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (s.rd.pend.length : Int)⌝) $$ [i m Hpri Hphys]
    · iexists W64 0, _
      iframe i m Hpri Hphys
      ipureintro
      word
    wp_for IH
    wp_if_destruct
    all_goals try simp at Hif
    · -- request `n`
      have Hlt : sint.nat n < s.rd.pend.length := by word
      obtain ⟨p, Hp⟩ : ∃ p, s.rd.pend[sint.nat n]? = some p :=
        ⟨_, List.getElem?_eq_getElem Hlt⟩
      obtain ⟨l, Hl⟩ : ∃ l, pls[sint.nat n]? = some l :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      ihave #Hpl := BigSepL2.bigSepL2_lookup Hl Hp $$ Hpls
      iunfold ownPendRI at Hpl
      icases Hpl with ⟨%psn, %pctx, %prs, #Hpl⟩
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hn.1, by word⟩)]
      wp_apply wp_load_slice_index pr (sint.Z n) _ (DFrac.own 1) l Hn.1 $$ [Hpri] as Hpri
      · iframe; ipureintro; exact Hl
      try wp_auto
      have Hcf := readRespondAll_fields id { s with rd := { s.rd with pend := [] } }
        ((pendReqs s).take (sint.nat n))
      wp_apply wp_sendMsgReadIndexResponse _ _ _
        (readRespondAll id { s with rd := { s.rd with pend := [] } }
          ((pendReqs s).take (sint.nat n))) l p.1 p.2 psn pctx prs (by rw [Hcf.2.1]; exact Hlead)
        (Hpne p (List.mem_of_getElem? Hp))
        $$ [$Hphys $Hpl] as %s' ⟨Hphys, %Hres⟩
      obtain ⟨-, rfl⟩ := Hres.resolve_right (fun h => h.1 Hsg)
      wp_for_post
      iframe HΦ r
      iexists n + W64 1, l
      have Hsucc : sint.nat (n + W64 1) = sint.nat n + 1 := by word
      rw [Hsucc]
      ihave Hphys := ownRaftPhysC_eq c r id _
        (readRespondAll id { s with rd := { s.rd with pend := [] } }
          ((pendReqs s).take (sint.nat n + 1)))
        (by
          rw [readRespondAll_take_succ id _ _ _ _ (pendReqs_lookup s _ p Hp)]
          simp only [arriveReq, Hcf.1]) $$ Hphys
      iframe i m Hpri Hphys
      ipureintro
      word
    · -- all answered
      have Hfull : sint.nat n = (pendReqs s).length := by
        simp only [pendReqs, List.length_map]; word
      rw [Hfull, List.take_length]
      iapply HΦ
      iframe Hphys
      ipureintro
      exact Or.inl ⟨Hsg, rfl⟩
  ihave Hphys := ownRaftPhysC_eq c r id _
    { sendMsgs (relState id s (sint.nat (W64 0))) [] with prvals := s.prvals }
    (by simp [relState, sendMsgs, readonlyRelease]; rfl) $$ Hphys
  -- the loop: after `n` requests, the first `n` are released
  ihave IH : iprop(∃ (n : w64) (mv : Loc) (ms : List Msg) (pvs : GMap w64 Progress),
      "i" ∷ i_ptr ↦ n ∗
      "m" ∷ m_ptr ↦ mv ∗
      "Hpri" ∷ pr ↦* pls ∗
      "Hphys" ∷ ownRaftPhysCV c c.voters r id
        { sendMsgs (relState id s (sint.nat n)) ms with prvals := pvs } ∗
      "%Hms" ∷ ⌜∀ m' ∈ ms, HeartbeatOk id (toPState s) m' ∧
         ∃ k, 0 < k ∧ k ≤ sint.nat n ∧
           m'.ctx = hbCtx (readonlyRelease s.rd.ro id s.logst.committed (s.rd.pend.take k))⌝ ∗
      "%Hmm" ∷ ⌜prvalsMatch pvs = prvalsMatch s.prvals⌝ ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (s.rd.pend.length : Int)⌝) $$ [i m Hpri Hphys]
  · iexists W64 0, _, [], s.prvals
    iframe i m Hpri Hphys
    ipureintro
    refine ⟨fun _ h => absurd h List.not_mem_nil, rfl, by word, by word⟩
  wp_for IH
  wp_if_destruct
  all_goals try simp at Hif
  · -- request `n`
    have Hlt : sint.nat n < s.rd.pend.length := by word
    obtain ⟨p, Hp⟩ : ∃ p, s.rd.pend[sint.nat n]? = some p := ⟨_, List.getElem?_eq_getElem Hlt⟩
    obtain ⟨l, Hl⟩ : ∃ l, pls[sint.nat n]? = some l :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    ihave #Hpl := BigSepL2.bigSepL2_lookup Hl Hp $$ Hpls
    iunfold ownPendRI at Hpl
    icases Hpl with ⟨%psn, %pctx, %prs, #Hpl⟩
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hn.1, by word⟩)]
    wp_apply wp_load_slice_index pr (sint.Z n) _ (DFrac.own 1) l Hn.1 $$ [Hpri] as Hpri
    · iframe; ipureintro; exact Hl
    try wp_auto
    wp_apply wp_sendMsgReadIndexResponse _ _ _
      { sendMsgs (relState id s (sint.nat n)) ms with prvals := pvs } l p.1 p.2 psn pctx prs Hlead
      (Hpne p (List.mem_of_getElem? Hp))
      $$ [$Hphys $Hpl] as %s1 ⟨Hphys, %Hres⟩
    rcases Hres with ⟨Hs1, -⟩ | ⟨-, ms', pvs', rfl, Hms', Hmm'⟩
    · exact absurd Hs1 Hsg
    wp_for_post
    iframe HΦ r
    iexists n + W64 1, l, ms ++ ms', pvs'
    have Hsucc : sint.nat (n + W64 1) = sint.nat n + 1 := by word
    rw [Hsucc]
    ihave Hphys := ownRaftPhysC_eq c r id _
      { sendMsgs (relState id s (sint.nat n + 1)) (ms ++ ms') with prvals := pvs' }
      (by simp only [sendMsgs, arriveState, relState, arriveReq,
            readonlyRelease_take_succ _ _ _ _ _ _ Hp, List.append_assoc]) $$ Hphys
    iframe i m Hpri Hphys
    ipureintro
    refine ⟨?_, Hmm'.trans Hmm, by word, by word⟩
    intro m' Hm'
    rcases List.mem_append.1 Hm' with Hm' | Hm'
    · obtain ⟨Hhb, k, Hk0, Hkn, Hctx⟩ := Hms m' Hm'
      exact ⟨Hhb, k, Hk0, by omega, Hctx⟩
    · obtain ⟨Hhb, Hctx⟩ := Hms' m' Hm'
      refine ⟨heartbeatOk_transfer id s
        { sendMsgs (relState id s (sint.nat n)) ms with prvals := pvs } m' rfl rfl rfl Hmm Hhb,
        sint.nat n + 1, by omega, by omega, ?_⟩
      rw [Hctx, readonlyRelease_take_succ _ _ _ _ _ _ Hp]
      simp only [readonlyArrive, hbCtx_recvAck]
      rfl
  · -- all released
    have Hfull : sint.nat n = s.rd.pend.length := by word
    rw [Hfull, relState_full]
    iapply HΦ
    iframe Hphys
    ipureintro
    exact Or.inr ⟨Hsg, ms, pvs, rfl, fun m' Hm' => by
      obtain ⟨Hhb, k, Hk0, Hkn, Hctx⟩ := Hms m' Hm'
      exact ⟨Hhb, k, Hk0, by omega, Hctx⟩, Hmm⟩

end proof

end EtcdGrove
end Perennial
