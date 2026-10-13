/-
Port of `election_proof/proof_releasePendingReadIndexMessages.v`; rewritten (2026-10-13)
for the general spec of 2026-10-12, which releases the pending requests.

An empty queue returns at the length test. Otherwise the entry at the commit index is of
the current term (the premise), so `committedEntryInCurrentTerm` holds and the `Error` arm
is dead; the field is taken (`ownRaftPhys_misc`, the state's `pend` emptied) and each
request goes to `sendMsgReadIndexResponse`, with the invariant that after `k` of them the
read-only object is `readonlyRelease` of the first `k` (`relState`).
-/
module

public import Spec.go_etcd_io.raft.v3.releasePendingReadIndexMessages
public import Spec.go_etcd_io.raft.v3.raft__committedEntryInCurrentTerm

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section helpers
variable [FfiSyntax]

/-- The state once the first `k` pending requests were released, before the heartbeats. -/
def relState (id : w64) (s : NState) (k : Nat) : NState :=
  { s with rd := { s.rd with pend := [],
                             ro := readonlyRelease s.rd.ro id s.logst.committed (s.rd.pend.take k) } }

theorem relState_full (id : w64) (s : NState) :
    relState id s s.rd.pend.length = releasedState id s := by
  simp only [relState, releasedState, List.take_length]

/-- One more request released. -/
theorem readonlyRelease_take_succ (r : ReadOnly) (id c : w64)
    (pend : List (raftpb.Message × List raftpb.Entry)) (k : Nat) (p : raftpb.Message × List raftpb.Entry)
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem releasePendingReadIndexMessages.wp_proof
    (wp_raft_committedEntryInCurrentTerm :
      raft.committedEntryInCurrentTerm.spec (GF := GF) (hG := hG))
    (wp_sendMsgReadIndexResponse : sendMsgReadIndexResponse.spec (GF := GF) (hG := hG)) :
    releasePendingReadIndexMessages.spec (GF := GF) (hG := hG) := by
  intro cfg r id s Hlead Hterm Hcit
  wp_start as Hpre
  iNamed Hpre
  wp_auto
  -- `len(r.pendingReadIndexMessages) == 0`
  icases ownRaftPhys_misc cfg r id s $$ Hphys with ⟨%rs, %ro, %pr, Hrs, Hro, Hpr, Hmisc, Hback⟩
  iunfold ownRaftMisc at Hmisc
  iNamed Hmisc
  ihave %Hprl := ownSlice_len _ _ _ $$ Hpri
  wp_auto
  ihave Hphys := Hback $$ %rs %ro %pr %s.rd Hrs Hro Hpr
    [HreadStates HreadStates_cap Hro_obj Hpri Hpri_cap]
  · unfold ownRaftMisc
    simp only [named]
    iframe HreadStates HreadStates_cap Hro_obj Hpri Hpri_cap Hpri_ents
  ihave Hphys := ownRaftPhys_eq cfg r id _ s rfl $$ Hphys
  by_cases Hpend : s.rd.pend = []
  · -- nothing pending: return
    have Hz : pr.len = W64 0 := by
      rw [Hpend] at Hprl; obtain ⟨h1, h2⟩ := Hprl; simp only [List.map_nil, List.length_nil] at h1
      word
    rw [decide_eq_true Hz]
    wp_auto
    iapply HΦ $$ %([] : List Msg) %s.prvals
    ihave Hphys := ownRaftPhys_eq cfg r id s
      { sendMsgs (releasedState id s) [] with prvals := s.prvals } (released_nil id s Hpend).symm
      $$ Hphys
    iframe Hphys
    ipureintro
    exact ⟨fun _ h => absurd h List.not_mem_nil, rfl⟩
  have Hnz : pr.len ≠ W64 0 := by
    intro Hz
    obtain ⟨h1, h2⟩ := Hprl
    rw [Hz, List.length_map] at h1
    exact Hpend (List.eq_nil_of_length_eq_zero (by rw [h1]; rfl))
  rw [decide_eq_false Hnz]
  wp_auto
  clear Hnz Hprl pr ro rs
  -- the entry at the commit index is of the current term
  wp_apply wp_raft_committedEntryInCurrentTerm _ _ _ _ Hterm $$ [$Hphys] as %b ⟨Hphys, %Hb⟩
  rw [Hb.2 (Hcit Hpend)]
  wp_auto
  -- `msgs := r.pendingReadIndexMessages; r.pendingReadIndexMessages = nil`
  icases ownRaftPhys_misc cfg r id s $$ Hphys with ⟨%rs, %ro, %pr, Hrs, Hro, Hpr, Hmisc, Hback⟩
  iunfold ownRaftMisc at Hmisc
  iNamed Hmisc
  ihave %Hprl := ownSlice_len _ _ _ $$ Hpri
  wp_auto
  ihave Hphys := Hback $$ %rs %ro %slice.nil %({ s.rd with pend := [] }) Hrs Hro Hpr
    [HreadStates HreadStates_cap Hro_obj]
  · unfold ownRaftMisc
    simp only [named, List.map_nil]
    iframe HreadStates HreadStates_cap Hro_obj
    isplitr
    · iapply ownSlice_nil
    isplitr
    · iapply ownSliceCap_nil
    iapply BigSepL.bigSepL_nil.2
    iempintro
  iclear Hpri_cap
  ihave Hphys := ownRaftPhys_eq cfg r id _
    { sendMsgs (relState id s (sint.nat (W64 0))) [] with prvals := s.prvals }
    (by simp [relState, sendMsgs, readonlyRelease]; rfl) $$ Hphys
  -- the loop: after `n` requests, the first `n` are released
  ihave IH : iprop(∃ (n : w64) (mv : raftpb.Message) (ms : List Msg) (pvs : GMap w64 Progress),
      "i" ∷ i_ptr ↦ n ∗
      "m" ∷ m_ptr ↦ mv ∗
      "Hpri" ∷ pr ↦* s.rd.pend.map Prod.fst ∗
      "Hphys" ∷ ownRaftPhys cfg r id
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
  obtain ⟨Hl1, Hl2⟩ := Hprl
  rw [List.length_map] at Hl1
  wp_if_destruct
  all_goals try simp at Hif
  · -- request `n`
    have Hlt : sint.nat n < s.rd.pend.length := by word
    obtain ⟨p, Hp⟩ : ∃ p, s.rd.pend[sint.nat n]? = some p := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hp1 : (s.rd.pend.map Prod.fst)[(sint.Z n).toNat]? = some p.1 := by
      show (s.rd.pend.map Prod.fst)[sint.nat n]? = _
      rw [List.getElem?_map, Hp]; rfl
    ihave #Hents := BigSepL.bigSepL_lookup (Φ := fun _ p => iprop(p.1.Entries' ↦*□ p.2))
      Hp $$ Hpri_ents
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hn.1, by word⟩)]
    wp_apply wp_load_slice_index pr (sint.Z n) _ (DFrac.own 1) p.1 Hn.1 $$ [Hpri] as Hpri
    · iframe; ipureintro; exact Hp1
    try wp_auto
    wp_apply wp_sendMsgReadIndexResponse _ _ _
      { sendMsgs (relState id s (sint.nat n)) ms with prvals := pvs } p.1 p.2 Hlead
      $$ [$Hphys $Hents] as %ms' %pvs' ⟨Hphys, %Hms', %Hmm'⟩
    wp_for_post
    iframe HΦ r
    iexists n + W64 1, p.1, ms ++ ms', pvs'
    have Hsucc : sint.nat (n + W64 1) = sint.nat n + 1 := by word
    rw [Hsucc]
    ihave Hphys := ownRaftPhys_eq cfg r id _
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
    iapply HΦ $$ %ms %pvs
    iframe Hphys
    ipureintro
    exact ⟨fun m' Hm' => by
      obtain ⟨Hhb, k, Hk0, Hkn, Hctx⟩ := Hms m' Hm'
      exact ⟨Hhb, k, Hk0, by omega, Hctx⟩, Hmm⟩

end proof

end EtcdGrove
end Perennial
